//! Symbol table and scope management for the Abide elaborator.

use std::collections::HashMap;

use super::error::{ElabError, ErrorKind};
use super::types::{
    EAxiom, EConst, EEntity, EExtern, EFn, EInterface, ELemma, EPred, EProc, EProp, EScene,
    ESystem, ETheorem, EVerify, Ty, VariantFieldsMap,
};
use crate::ast::{UseDecl, Visibility};

/// What kind of top-level declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Entity,
    Interface,
    Extern,
    System,
    Proc,
    Pred,
    Prop,
    Verify,
    Scene,
    Theorem,
    Axiom,
    Lemma,
    Const,
    Fn,
}

/// A use declaration with provenance (source module + source file).
#[derive(Debug, Clone)]
pub struct UseDeclEntry {
    pub decl: UseDecl,
    /// Module that contains this use declaration.
    pub source_module: Option<String>,
    /// File that contains this use declaration.
    pub source_file: Option<String>,
}

/// Information about a declaration in the symbol table.
#[derive(Debug, Clone)]
pub struct DeclInfo {
    pub kind: DeclKind,
    pub name: String,
    pub ty: Option<Ty>,
    pub visibility: Visibility,
    /// Source module this declaration belongs to (None = no module declared).
    pub module: Option<String>,
    /// Source span of this declaration (for diagnostic pointing).
    pub span: Option<crate::span::Span>,
    /// Source file path of this declaration (for cross-file diagnostics).
    pub file: Option<String>,
}

/// The elaboration environment (symbol table).
///
/// Two-level namespace:
/// - `decls`: module-qualified keys (`Module::Name`), global declaration registry
/// - `types`/`entities`/`systems`/etc: bare-name keys, the *working namespace*
///   that downstream passes (resolve, check, lower) operate on.
///
/// For single-module compilation, both levels have the same content.
/// For multi-module, collection populates `decls` with qualified keys and
/// bare-name maps with module-local declarations. Use resolution then imports
/// cross-module public declarations into the bare-name maps.
#[derive(Debug, Clone)]
pub struct Env {
    pub module_name: Option<String>,
    /// Whether the current `module_name` was inherited from a parent file via include
    /// (as opposed to declared by this file's own `module` declaration).
    /// When true, a `module` declaration in this file overrides it without conflict.
    pub module_inherited: bool,
    /// Current source file being collected (set by loader, used to tag declarations).
    pub current_file: Option<String>,
    pub includes: Vec<String>,
    /// Use declarations with provenance (source module + source file).
    /// Enables per-use-decl visibility checks and file tagging for diagnostics.
    pub use_decls: Vec<UseDeclEntry>,
    /// Global declaration registry, keyed by `Module::Name` (or bare name if no module).
    pub decls: HashMap<String, DeclInfo>,
    /// Working namespace — bare-name maps used by resolve/check/lower.
    /// Populated by `build_working_namespace` (current module) and `import_into_namespace` (use).
    pub types: HashMap<String, Ty>,
    pub entities: HashMap<String, EEntity>,
    pub interfaces: HashMap<String, EInterface>,
    pub externs: HashMap<String, EExtern>,
    pub systems: HashMap<String, ESystem>,
    pub procs: HashMap<String, EProc>,
    pub preds: HashMap<String, EPred>,
    pub props: HashMap<String, EProp>,
    pub verifies: Vec<EVerify>,
    pub scenes: Vec<EScene>,
    pub theorems: Vec<ETheorem>,
    pub axioms: Vec<EAxiom>,
    pub lemmas: Vec<ELemma>,
    /// canonical proof-environment objects
    /// (`under { }` blocks). Populated by `collect_under`. Each
    /// member theorem/lemma carries an index into this vec.
    pub under_blocks: Vec<crate::elab::types::EUnderBlock>,
    pub consts: HashMap<String, EConst>,
    pub fns: HashMap<String, EFn>,
    /// Constructor field info for enums with record variants.
    /// Maps `enum_name` → Vec<(`variant_name`, Vec<(`field_name`, Ty)>)>.
    pub variant_fields: VariantFieldsMap,
    /// Generic type definitions (e.g., `Option<T>`, `Result<T, E>`).
    /// Stored here, NOT in `types` — concrete monomorphized instances go in `types`.
    pub generic_types: HashMap<String, crate::elab::types::GenericTypeDef>,
    pub errors: Vec<ElabError>,
    /// Structured load errors from included files (lex/IO errors that should be
    /// rendered through miette rather than downgraded to plain `ElabError` text).
    pub include_load_errors: Vec<crate::loader::LoadError>,
    /// All known module names (populated from `module` declarations across files).
    pub known_modules: std::collections::HashSet<String>,
    /// Alias map: `local_name` → `canonical_name`. Built during use resolution
    /// so the resolve pass can rewrite aliased references to canonical names.
    pub aliases: HashMap<String, String>,
    /// Frozen qualified stores — preserved across `build_working_namespace` for
    /// cross-module `import_into_namespace` lookups.
    qualified_types: HashMap<String, Ty>,
    qualified_entities: HashMap<String, EEntity>,
    qualified_interfaces: HashMap<String, EInterface>,
    qualified_externs: HashMap<String, EExtern>,
    qualified_systems: HashMap<String, ESystem>,
    qualified_procs: HashMap<String, EProc>,
    qualified_preds: HashMap<String, EPred>,
    qualified_props: HashMap<String, EProp>,
    qualified_consts: HashMap<String, EConst>,
    qualified_fns: HashMap<String, EFn>,
    qualified_generic_types: HashMap<String, crate::elab::types::GenericTypeDef>,
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Self {
            module_name: None,
            module_inherited: false,
            current_file: None,
            includes: Vec::new(),
            use_decls: Vec::new(),
            decls: HashMap::new(),
            types: HashMap::new(),
            entities: HashMap::new(),
            interfaces: HashMap::new(),
            externs: HashMap::new(),
            systems: HashMap::new(),
            procs: HashMap::new(),
            preds: HashMap::new(),
            props: HashMap::new(),
            verifies: Vec::new(),
            scenes: Vec::new(),
            theorems: Vec::new(),
            axioms: Vec::new(),
            lemmas: Vec::new(),
            under_blocks: Vec::new(),
            consts: HashMap::new(),
            fns: HashMap::new(),
            variant_fields: HashMap::new(),
            generic_types: HashMap::new(),
            errors: Vec::new(),
            include_load_errors: Vec::new(),
            known_modules: std::collections::HashSet::new(),
            aliases: HashMap::new(),
            qualified_types: HashMap::new(),
            qualified_entities: HashMap::new(),
            qualified_interfaces: HashMap::new(),
            qualified_externs: HashMap::new(),
            qualified_systems: HashMap::new(),
            qualified_procs: HashMap::new(),
            qualified_preds: HashMap::new(),
            qualified_props: HashMap::new(),
            qualified_consts: HashMap::new(),
            qualified_fns: HashMap::new(),
            qualified_generic_types: HashMap::new(),
        }
    }

    /// Add a declaration, reporting duplicates.
    ///
    /// Uses module-qualified keys (`Module::Name`) when a module is set,
    /// so same-named declarations from different modules don't collide.
    pub fn add_decl(&mut self, name: &str, info: DeclInfo) {
        let key = Self::qualified_key(info.module.as_deref(), name);
        if let Some(existing) = self.decls.get(&key) {
            let mut err = if let Some(span) = info.span {
                ElabError::with_span(
                    ErrorKind::DuplicateDecl,
                    format!("duplicate declaration '{name}'"),
                    "duplicate defined here".to_owned(),
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::DuplicateDecl,
                    format!("duplicate declaration '{name}'"),
                    String::new(),
                )
            };
            // Point to the original declaration if it has a span.
            // Use with_secondary_in_file when original is in a different file.
            if let Some(orig_span) = existing.span {
                let label = format!("'{name}' first declared here");
                if let Some(ref orig_file) = existing.file {
                    err = err.with_secondary_in_file(orig_span, label, orig_file.clone());
                } else {
                    err = err.with_secondary(orig_span, label);
                }
            }
            self.errors
                .push(err.with_help(crate::messages::HELP_DUPLICATE_DECL));
        } else {
            self.decls.insert(key, info);
        }
    }

    /// Build a module-qualified key for the decls map.
    pub fn qualified_key(module: Option<&str>, name: &str) -> String {
        match module {
            Some(m) => format!("{m}::{name}"),
            None => name.to_owned(),
        }
    }

    /// Look up a declaration by bare name in the qualified registry.
    ///
    /// Checks bare key first (no module), then scans qualified entries
    /// sorted by module name for deterministic behavior.
    /// For unambiguous cross-module lookup, use `lookup_decl_qualified`.
    pub fn lookup_decl(&self, name: &str) -> Option<&DeclInfo> {
        if let Some(d) = self.decls.get(name) {
            return Some(d);
        }
        let mut matches: Vec<&DeclInfo> = self.decls.values().filter(|d| d.name == name).collect();
        matches.sort_by_key(|d| d.module.as_deref().unwrap_or(""));
        matches.into_iter().next()
    }

    /// Look up a declaration by module-qualified name.
    pub fn lookup_decl_qualified(&self, module: &str, name: &str) -> Option<&DeclInfo> {
        let key = Self::qualified_key(Some(module), name);
        self.decls.get(&key)
    }

    /// Get all declarations belonging to a given module.
    pub fn decls_in_module(&self, module: &str) -> Vec<&DeclInfo> {
        self.decls
            .values()
            .filter(|d| d.module.as_deref() == Some(module))
            .collect()
    }

    /// Insert a type into the semantic map using a module-qualified key
    /// (for multi-module isolation). Single-module files use bare names.
    pub fn insert_type(&mut self, name: &str, ty: Ty) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.types.insert(key, ty);
    }

    /// Insert a generic type definition using a module-qualified key.
    pub fn insert_generic_type(&mut self, name: &str, gdef: crate::elab::types::GenericTypeDef) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.generic_types.insert(key, gdef);
    }

    /// Insert an entity into the semantic map using a module-qualified key.
    pub fn insert_entity(&mut self, name: &str, entity: EEntity) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.entities.insert(key, entity);
    }

    /// Insert an interface into the semantic map using a module-qualified key.
    pub fn insert_interface(&mut self, name: &str, interface: EInterface) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.interfaces.insert(key, interface);
    }

    /// Insert an extern into the semantic map using a module-qualified key.
    pub fn insert_extern(&mut self, name: &str, ext: EExtern) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.externs.insert(key, ext);
    }

    /// Insert a system into the semantic map using a module-qualified key.
    pub fn insert_system(&mut self, name: &str, system: ESystem) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.systems.insert(key, system);
    }

    /// Insert a reusable proc into the semantic map using a module-qualified key.
    pub fn insert_proc(&mut self, name: &str, proc_decl: EProc) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.procs.insert(key, proc_decl);
    }

    /// Insert a pred into the semantic map using a module-qualified key.
    pub fn insert_pred(&mut self, name: &str, pred: EPred) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.preds.insert(key, pred);
    }

    /// Insert a prop into the semantic map using a module-qualified key.
    pub fn insert_prop(&mut self, name: &str, prop: EProp) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.props.insert(key, prop);
    }

    /// Insert a const into the semantic map using a module-qualified key.
    pub fn insert_const(&mut self, name: &str, c: EConst) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.consts.insert(key, c);
    }

    /// Insert a fn into the semantic map using a module-qualified key.
    pub fn insert_fn(&mut self, name: &str, f: EFn) {
        let key = Self::qualified_key(self.module_name.as_deref(), name);
        self.fns.insert(key, f);
    }

    /// Build the bare-name working namespace from qualified semantic maps.
    ///
    /// Replaces the semantic maps (types, entities, systems, preds, props)
    /// with bare-name-keyed maps containing ONLY the current module's
    /// declarations. Cross-module names are NOT included — they come in
    /// via explicit `use` resolution in the resolve pass.
    ///
    /// For declarations without a module (bare keys), they always go in.
    fn bare_name(key: &str) -> &str {
        key.rsplit("::").next().unwrap_or(key)
    }

    fn key_matches_module(key: &str, module: Option<&str>) -> bool {
        if key.contains("::") {
            match module {
                Some(m) => key.rsplit_once("::").unwrap().0 == m,
                // No root module (e.g., directory load) — include all modules.
                None => true,
            }
        } else {
            true
        }
    }

    /// Deterministically flatten qualified entries to bare names.
    ///
    /// When multiple qualified keys collapse to the same bare name,
    /// unscoped (bare) keys take priority over qualified keys.
    /// Among qualified keys, alphabetically-first module wins.
    fn flatten_sorted<V: Clone>(
        map: &HashMap<String, V>,
        module: Option<&str>,
    ) -> HashMap<String, V> {
        let mut entries: Vec<(String, V)> = map
            .iter()
            .filter(|(k, _)| Self::key_matches_module(k, module))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        // Sort: bare keys first (no::), then qualified keys alphabetically.
        entries.sort_by(|(a, _), (b, _)| {
            let a_qualified = a.contains("::");
            let b_qualified = b.contains("::");
            match (a_qualified, b_qualified) {
                (false, true) => std::cmp::Ordering::Less,
                (true, false) => std::cmp::Ordering::Greater,
                _ => a.cmp(b),
            }
        });
        let mut result = HashMap::new();
        for (k, v) in entries {
            result.entry(Self::bare_name(&k).to_string()).or_insert(v);
        }
        result
    }

    pub fn build_working_namespace(&mut self) {
        // Per-module pre-resolution: resolve all entity and system field
        // types within each module's own scope BEFORE freezing qualified
        // stores. This ensures that when entities are later imported into
        // another module, their field types are already resolved — the
        // importing module doesn't need to know about the defining
        // module's internal type names.
        //
        // Without this, an entity defined in module Warehouse with a
        // field `status: SlotStatus` would carry `Ty::Named("SlotStatus")`
        // into any module that imports it, and the importing module's
        // resolve pass can't find `SlotStatus` in its bare-name maps.
        self.resolve_qualified_field_types();

        // Freeze qualified stores BEFORE replacing bare-name maps.
        self.qualified_types = self.types.clone();
        self.qualified_entities = self.entities.clone();
        self.qualified_interfaces = self.interfaces.clone();
        self.qualified_externs = self.externs.clone();
        self.qualified_systems = self.systems.clone();
        self.qualified_procs = self.procs.clone();
        self.qualified_preds = self.preds.clone();
        self.qualified_props = self.props.clone();
        self.qualified_consts = self.consts.clone();
        self.qualified_fns = self.fns.clone();
        self.qualified_generic_types = self.generic_types.clone();

        let current = self.module_name.clone();

        self.types = Self::flatten_sorted(&self.types, current.as_deref());
        self.entities = Self::flatten_sorted(&self.entities, current.as_deref());
        self.interfaces = Self::flatten_sorted(&self.interfaces, current.as_deref());
        self.externs = Self::flatten_sorted(&self.externs, current.as_deref());
        self.systems = Self::flatten_sorted(&self.systems, current.as_deref());
        self.procs = Self::flatten_sorted(&self.procs, current.as_deref());
        self.preds = Self::flatten_sorted(&self.preds, current.as_deref());
        self.props = Self::flatten_sorted(&self.props, current.as_deref());
        self.consts = Self::flatten_sorted(&self.consts, current.as_deref());
        self.fns = Self::flatten_sorted(&self.fns, current.as_deref());
        self.generic_types = Self::flatten_sorted(&self.generic_types, current.as_deref());

        // Filter verify/scene/theorem/axiom/lemma vectors by module.
        // These use their decl key (prefixed with "verify:", "scene:", etc.) to check module.
        let is_current_module = |prefix: &str, name: &str| -> bool {
            let decl_key_bare = format!("{prefix}{name}");
            // Check if this block belongs to the current module via decls map
            if let Some(di) = self
                .decls
                .get(&Env::qualified_key(current.as_deref(), &decl_key_bare))
            {
                di.module.as_deref() == current.as_deref()
            } else {
                // Also check bare key (no module)
                self.decls
                    .get(&decl_key_bare)
                    .is_some_and(|di| di.module.is_none())
                    || current.is_none()
            }
        };

        self.verifies
            .retain(|v| is_current_module("verify:", &v.name));
        self.scenes.retain(|s| is_current_module("scene:", &s.name));
        self.theorems.retain(|t| is_current_module("", &t.name));
        self.axioms.retain(|a| is_current_module("", &a.name));
        self.lemmas.retain(|l| is_current_module("", &l.name));

        // filter `under_blocks` to the current
        // module the same way theorems and lemmas are filtered, then
        // remap each member's `enclosing_under_idx` to point at the
        // new (post-filter) position. Without this, foreign-module
        // under blocks would leak into `env.under_blocks` and the
        // resolve pass would resolve them against the wrong system
        // set, producing spurious "unknown event" / "ambiguous fair
        // event" diagnostics.
        let cur_mod_for_under = current.as_deref();
        let original_under_count = self.under_blocks.len();
        let mut under_remap: Vec<Option<usize>> = vec![None; original_under_count];
        let mut kept_unders: Vec<crate::elab::types::EUnderBlock> =
            Vec::with_capacity(original_under_count);
        for (old_idx, ub) in self.under_blocks.iter().enumerate() {
            if ub.module.as_deref() == cur_mod_for_under {
                under_remap[old_idx] = Some(kept_unders.len());
                kept_unders.push(ub.clone());
            }
        }
        self.under_blocks = kept_unders;

        // Remap surviving member references. Members of a foreign
        // under block were already dropped by the theorem/lemma
        // filters above (siblings inside an `under` are collected
        // with the same `current_file`/`module_name`, so they share
        // the under's module), but defensively map any straggler to
        // `None` rather than crashing.
        for t in &mut self.theorems {
            if let Some(old) = t.enclosing_under_idx {
                t.enclosing_under_idx = under_remap.get(old).copied().flatten();
            }
        }
        for l in &mut self.lemmas {
            if let Some(old) = l.enclosing_under_idx {
                l.enclosing_under_idx = under_remap.get(old).copied().flatten();
            }
        }
    }

    /// Import a specific declaration into the bare-name working namespace.
    ///
    /// Reads from the frozen qualified stores (preserved by `build_working_namespace`)
    /// and inserts into the bare-name working maps. Explicit imports override
    /// existing entries (last `use` wins for the same local name).
    pub fn import_into_namespace(
        &mut self,
        local_name: &str,
        source_module: &str,
        source_name: &str,
    ) {
        let qkey = Self::qualified_key(Some(source_module), source_name);

        if let Some(ty) = self.qualified_types.get(&qkey).cloned() {
            self.types.insert(local_name.to_string(), ty);
        }
        if let Some(entity) = self.qualified_entities.get(&qkey).cloned() {
            self.entities.insert(local_name.to_string(), entity);
        }
        if let Some(interface) = self.qualified_interfaces.get(&qkey).cloned() {
            self.interfaces.insert(local_name.to_string(), interface);
        }
        if let Some(ext) = self.qualified_externs.get(&qkey).cloned() {
            self.externs.insert(local_name.to_string(), ext);
        }
        if let Some(system) = self.qualified_systems.get(&qkey).cloned() {
            self.systems.insert(local_name.to_string(), system);
        }
        if let Some(proc_decl) = self.qualified_procs.get(&qkey).cloned() {
            self.procs.insert(local_name.to_string(), proc_decl);
        }
        if let Some(pred) = self.qualified_preds.get(&qkey).cloned() {
            self.preds.insert(local_name.to_string(), pred);
        }
        if let Some(prop) = self.qualified_props.get(&qkey).cloned() {
            self.props.insert(local_name.to_string(), prop);
        }
        if let Some(c) = self.qualified_consts.get(&qkey).cloned() {
            self.consts.insert(local_name.to_string(), c);
        }
        if let Some(f) = self.qualified_fns.get(&qkey).cloned() {
            self.fns.insert(local_name.to_string(), f);
        }
        if let Some(g) = self.qualified_generic_types.get(&qkey).cloned() {
            self.generic_types.insert(local_name.to_string(), g);
        }
    }

    /// Create a `DeclInfo` tagged with the current module name and source span.
    pub fn make_decl_info(
        &self,
        kind: DeclKind,
        name: String,
        ty: Option<Ty>,
        visibility: Visibility,
        span: crate::span::Span,
    ) -> DeclInfo {
        DeclInfo {
            kind,
            name,
            ty,
            visibility,
            module: self.module_name.clone(),
            span: Some(span),
            file: self.current_file.clone(),
        }
    }

    /// Resolve all entity and system field types within each module's
    /// own scope. For each module, builds a bare-name type/entity map
    /// from that module's qualified entries, then resolves every
    /// `Ty::Named` field type using that map.
    ///
    /// This mirrors how Rust and Go resolve names: each compilation
    /// unit resolves its own names in its own context. Imported symbols
    /// arrive already-resolved.
    fn resolve_qualified_field_types(&mut self) {
        use super::types::GenericTypeDef;
        use std::collections::HashSet;

        // Collect all module names from qualified keys.
        let mut modules: HashSet<Option<String>> = HashSet::new();
        for key in self.types.keys().chain(self.entities.keys()) {
            if let Some((module, _)) = key.rsplit_once("::") {
                modules.insert(Some(module.to_owned()));
            } else {
                modules.insert(None);
            }
        }

        for module in &modules {
            // Build this module's bare-name type scope.
            let module_types: HashMap<String, Ty> =
                Self::flatten_sorted(&self.types, module.as_deref());
            let module_entities: HashMap<String, String> =
                Self::flatten_sorted(&self.entities, module.as_deref())
                    .into_iter()
                    .map(|(k, e)| (k, e.name.clone()))
                    .collect();
            let module_generics: HashMap<String, GenericTypeDef> =
                Self::flatten_sorted(&self.generic_types, module.as_deref());

            // Resolve entity field types for entities in this module.
            for (key, entity) in &mut self.entities {
                if !Self::key_matches_module(key, module.as_deref()) {
                    continue;
                }
                for field in &mut entity.fields {
                    field.ty = Self::resolve_ty_with(
                        &module_types,
                        &module_entities,
                        &module_generics,
                        &field.ty,
                    );
                }
                for action in &mut entity.actions {
                    action.refs = action
                        .refs
                        .iter()
                        .map(|(n, t)| {
                            (
                                n.clone(),
                                Self::resolve_ty_with(
                                    &module_types,
                                    &module_entities,
                                    &module_generics,
                                    t,
                                ),
                            )
                        })
                        .collect();
                    action.params = action
                        .params
                        .iter()
                        .map(|(n, t)| {
                            (
                                n.clone(),
                                Self::resolve_ty_with(
                                    &module_types,
                                    &module_entities,
                                    &module_generics,
                                    t,
                                ),
                            )
                        })
                        .collect();
                }
            }

            // Resolve system field types for systems in this module.
            for (key, system) in &mut self.systems {
                if !Self::key_matches_module(key, module.as_deref()) {
                    continue;
                }
                for field in &mut system.fields {
                    field.ty = Self::resolve_ty_with(
                        &module_types,
                        &module_entities,
                        &module_generics,
                        &field.ty,
                    );
                }
                for step in &mut system.steps {
                    step.params = step
                        .params
                        .iter()
                        .map(|(n, t)| {
                            (
                                n.clone(),
                                Self::resolve_ty_with(
                                    &module_types,
                                    &module_entities,
                                    &module_generics,
                                    t,
                                ),
                            )
                        })
                        .collect();
                }
                for query in &mut system.queries {
                    query.params = query
                        .params
                        .iter()
                        .map(|(n, t)| {
                            (
                                n.clone(),
                                Self::resolve_ty_with(
                                    &module_types,
                                    &module_entities,
                                    &module_generics,
                                    t,
                                ),
                            )
                        })
                        .collect();
                }
                for pred in &mut system.preds {
                    pred.params = pred
                        .params
                        .iter()
                        .map(|(n, t)| {
                            (
                                n.clone(),
                                Self::resolve_ty_with(
                                    &module_types,
                                    &module_entities,
                                    &module_generics,
                                    t,
                                ),
                            )
                        })
                        .collect();
                }
            }

            // Resolve fn param/return types for fns in this module.
            for (key, func) in &mut self.fns {
                if !Self::key_matches_module(key, module.as_deref()) {
                    continue;
                }
                func.params = func
                    .params
                    .iter()
                    .map(|(n, t)| {
                        (
                            n.clone(),
                            Self::resolve_ty_with(
                                &module_types,
                                &module_entities,
                                &module_generics,
                                t,
                            ),
                        )
                    })
                    .collect();
                func.ret_ty = Self::resolve_ty_with(
                    &module_types,
                    &module_entities,
                    &module_generics,
                    &func.ret_ty,
                );
            }

            // Resolve pred param types for preds in this module.
            for (key, pred) in &mut self.preds {
                if !Self::key_matches_module(key, module.as_deref()) {
                    continue;
                }
                pred.params = pred
                    .params
                    .iter()
                    .map(|(n, t)| {
                        (
                            n.clone(),
                            Self::resolve_ty_with(
                                &module_types,
                                &module_entities,
                                &module_generics,
                                t,
                            ),
                        )
                    })
                    .collect();
            }
        }
    }

    /// Resolve a single type using the given bare-name maps. This is a
    /// standalone version of `resolve_ty` from the resolve pass, used
    /// during per-module pre-resolution before the resolve pass runs.
    fn resolve_ty_with(
        types: &HashMap<String, Ty>,
        entities: &HashMap<String, String>,
        generic_types: &HashMap<String, super::types::GenericTypeDef>,
        ty: &Ty,
    ) -> Ty {
        match ty {
            Ty::Named(n) => {
                if let Some(t) = types.get(n.as_str()) {
                    t.clone()
                } else if let Some(canonical) = entities.get(n.as_str()) {
                    Ty::Entity(canonical.clone())
                } else if generic_types.contains_key(n.as_str()) {
                    // Generic type reference without args — leave for
                    // monomorphization to handle.
                    ty.clone()
                } else {
                    ty.clone()
                }
            }
            Ty::Record(n, fs) => Ty::Record(
                n.clone(),
                fs.iter()
                    .map(|(fn_, ft)| {
                        (
                            fn_.clone(),
                            Self::resolve_ty_with(types, entities, generic_types, ft),
                        )
                    })
                    .collect(),
            ),
            Ty::Param(n, args) => Ty::Param(
                n.clone(),
                args.iter()
                    .map(|a| Self::resolve_ty_with(types, entities, generic_types, a))
                    .collect(),
            ),
            Ty::Alias(n, inner) => Ty::Alias(
                n.clone(),
                Box::new(Self::resolve_ty_with(types, entities, generic_types, inner)),
            ),
            Ty::Newtype(n, inner) => Ty::Newtype(
                n.clone(),
                Box::new(Self::resolve_ty_with(types, entities, generic_types, inner)),
            ),
            Ty::Set(inner) => Ty::Set(Box::new(Self::resolve_ty_with(
                types,
                entities,
                generic_types,
                inner,
            ))),
            Ty::Seq(inner) => Ty::Seq(Box::new(Self::resolve_ty_with(
                types,
                entities,
                generic_types,
                inner,
            ))),
            Ty::Map(k, v) => Ty::Map(
                Box::new(Self::resolve_ty_with(types, entities, generic_types, k)),
                Box::new(Self::resolve_ty_with(types, entities, generic_types, v)),
            ),
            Ty::Fn(a, b) => Ty::Fn(
                Box::new(Self::resolve_ty_with(types, entities, generic_types, a)),
                Box::new(Self::resolve_ty_with(types, entities, generic_types, b)),
            ),
            Ty::Tuple(ts) => Ty::Tuple(
                ts.iter()
                    .map(|t| Self::resolve_ty_with(types, entities, generic_types, t))
                    .collect(),
            ),
            Ty::Refinement(base, pred) => Ty::Refinement(
                Box::new(Self::resolve_ty_with(types, entities, generic_types, base)),
                pred.clone(),
            ),
            _ => ty.clone(),
        }
    }

    pub fn lookup_type(&self, name: &str) -> Option<&Ty> {
        self.types.get(name)
    }

    pub fn lookup_entity(&self, name: &str) -> Option<&EEntity> {
        self.entities.get(name)
    }

    /// Collect errors in insertion order (reversed from accumulation order).
    pub fn take_errors(&self) -> Vec<ElabError> {
        let mut errs = self.errors.clone();
        errs.reverse();
        errs
    }
}
