//! Pass 1: Collect all top-level declarations into the environment.
//!
//! Walks the parsed AST and registers every type, entity, system,
//! pred, prop, verify, scene, theorem, axiom, lemma, const, and fn declaration.

mod entity;
mod expr;
mod system;

use entity::{collect_entity, collect_invoc_arg};
use expr::collect_expr;
use system::{
    collect_extern, collect_interface, collect_program, collect_reusable_proc, collect_system,
};

use crate::ast::{self, Visibility};

use super::env::{DeclKind, Env};
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EActivation, EAxiom, EConst, EContract, EExpr, EFn, ELemma, ELetBinding, EPred,
    EProcBoundDecl, EProp, EScene, ESceneGiven, ESceneWhen, EStoreDecl, ETheorem, EVerify,
    EnumVariantFields, Ty,
};

/// Collect all declarations from a parsed program into a new `Env`.
pub fn collect(program: &ast::Program) -> Env {
    let mut env = Env::new();
    collect_into(&mut env, program);
    env
}

/// Collect a standalone expression into its elaboration-level form.
///
/// This is a narrow helper for tools that need to synthesize verifier-facing
/// declarations from ad hoc expressions while still reusing the normal
/// resolve/check/lower pipeline over an existing `Env`.
#[must_use]
pub fn collect_query_expr(expr: &ast::Expr) -> EExpr {
    collect_expr(expr)
}

/// Collect declarations from a parsed program into an existing `Env`.
///
/// Used by the multi-file loader to merge declarations from multiple files
/// into a shared environment.
pub fn collect_into(env: &mut Env, program: &ast::Program) {
    // Track how many use_decls exist before this file's declarations
    let use_decls_before = env.use_decls.len();

    for decl in &program.decls {
        collect_top_decl(env, decl);
    }

    // Retroactively fix use-before-module: if this file's `use` declarations
    // were recorded with source_module=None (because `use` appeared before
    // `module` in the file), patch them now that module_name is set.
    if let Some(ref module) = env.module_name {
        for entry in &mut env.use_decls[use_decls_before..] {
            if entry.source_module.is_none() {
                entry.source_module = Some(module.clone());
            }
        }
    }
}

fn collect_top_decl(env: &mut Env, decl: &ast::TopDecl) {
    match decl {
        ast::TopDecl::Module(d) => {
            env.known_modules.insert(d.name.clone());
            match &env.module_name {
                Some(existing) if existing != &d.name => {
                    if env.module_inherited {
                        // The current module was inherited from a parent include.
                        // This file declares its own module — override the inherited one.
                        env.module_name = Some(d.name.clone());
                        env.module_inherited = false;
                    } else {
                        // Genuine conflict: two explicit module declarations in
                        // the same file or compilation scope.
                        env.errors.push(ElabError::with_span(
                            ErrorKind::DuplicateDecl,
                            format!(
                                "conflicting module declaration: '{}' (already declared as '{}')",
                                d.name, existing
                            ),
                            String::new(),
                            d.span,
                        ));
                    }
                }
                None => {
                    env.module_name = Some(d.name.clone());
                }
                _ => {} // Same name repeated — idempotent
            }
        }
        ast::TopDecl::Include(d) => {
            env.includes.push(d.path.clone());
        }
        ast::TopDecl::Use(ud) => {
            // Pair with current module so resolve knows which module is importing.
            // If module_name is None (use before module decl, or no module decl),
            // the use still gets recorded — resolve handles None source gracefully
            // by skipping same-module visibility shortcuts.
            let source_module = env.module_name.clone();
            let source_file = env.current_file.clone();
            env.use_decls.push(crate::elab::env::UseDeclEntry {
                decl: ud.clone(),
                source_module,
                source_file,
            });
        }
        ast::TopDecl::Const(d) => collect_const(env, d),
        ast::TopDecl::Fn(d) => collect_fn(env, d),
        ast::TopDecl::Type(d) => collect_type(env, d),
        ast::TopDecl::Record(d) => collect_record(env, d),
        ast::TopDecl::Entity(d) => collect_entity(env, d),
        ast::TopDecl::Interface(d) => collect_interface(env, d),
        ast::TopDecl::Extern(d) => collect_extern(env, d),
        ast::TopDecl::System(d) => collect_system(env, d),
        ast::TopDecl::Proc(d) => collect_reusable_proc(env, d),
        ast::TopDecl::Program(d) => collect_program(env, d),
        ast::TopDecl::Pred(d) => collect_pred(env, d),
        ast::TopDecl::Prop(d) => collect_prop(env, d),
        ast::TopDecl::Verify(d) => collect_verify(env, d),
        ast::TopDecl::Scene(d) => collect_scene(env, d),
        ast::TopDecl::Theorem(d) => collect_theorem(env, d),
        ast::TopDecl::Axiom(d) => collect_axiom(env, d),
        ast::TopDecl::Lemma(d) => collect_lemma(env, d),
        ast::TopDecl::Alias(d) => collect_alias(env, d),
        ast::TopDecl::Newtype(d) => collect_newtype(env, d),
        ast::TopDecl::Under(d) => collect_under(env, d),
        ast::TopDecl::Error(_) => {}
    }
}

// ── Type declarations ────────────────────────────────────────────────

fn collect_type(env: &mut Env, td: &ast::TypeDecl) {
    let name = &td.name;
    // TypeDecl always represents an enum (sum type with constructors).
    // Type aliases are handled separately via TopDecl::Alias → collect_alias.
    let variant_names: Vec<String> = td
        .variants
        .iter()
        .map(|v| match v {
            ast::TypeVariant::Simple { name, .. }
            | ast::TypeVariant::Tuple { name, .. }
            | ast::TypeVariant::Record { name, .. }
            | ast::TypeVariant::Param { name, .. } => name.clone(),
        })
        .collect();

    // Store constructor field info for record variants (used by IR lowering
    // to produce IRVariant::fields for Z3 ADT encoding).
    let field_info: EnumVariantFields = td
        .variants
        .iter()
        .map(|v| match v {
            ast::TypeVariant::Simple { name, .. } => (name.clone(), vec![]),
            ast::TypeVariant::Tuple { name, fields, .. } => {
                // Tuple variants store positional fields as "_0", "_1", etc.
                let fs: Vec<(String, Ty)> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (format!("_{i}"), resolve_type_ref(f)))
                    .collect();
                (name.clone(), fs)
            }
            ast::TypeVariant::Record { name, fields, .. } => {
                let fs: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), resolve_type_ref(&f.ty)))
                    .collect();
                (name.clone(), fs)
            }
            ast::TypeVariant::Param { name, .. } => (name.clone(), vec![]),
        })
        .collect();

    // Generic enum: store definition for on-demand monomorphization, don't register
    // as a concrete type. Concrete instances are created by resolve_ty.
    if !td.type_params.is_empty() {
        let gdef = crate::elab::types::GenericTypeDef {
            name: name.clone(),
            type_params: td.type_params.clone(),
            variant_names: variant_names.clone(),
            variant_fields: field_info,
            visibility: td.visibility,
            span: td.span,
        };
        env.insert_generic_type(name, gdef);
        // Register in decls so import/visibility works, but not in env.types
        let ty = Ty::Param(
            name.clone(),
            td.type_params
                .iter()
                .map(|p| Ty::Named(p.clone()))
                .collect(),
        );
        let info = env.make_decl_info(
            DeclKind::Type,
            name.clone(),
            Some(ty),
            td.visibility,
            td.span,
        );
        env.add_decl(name, info);
        return;
    }

    if field_info.iter().any(|(_, fs)| !fs.is_empty()) {
        env.variant_fields.insert(name.clone(), field_info);
    }

    let ty = Ty::Enum(name.clone(), variant_names);
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        td.visibility,
        td.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

fn collect_record(env: &mut Env, rd: &ast::RecordDecl) {
    let name = &rd.name;
    let fields: Vec<(String, Ty)> = rd
        .fields
        .iter()
        .map(|f| (f.name.clone(), resolve_type_ref(&f.ty)))
        .collect();
    let ty = Ty::Record(name.clone(), fields);
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        rd.visibility,
        rd.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

fn collect_alias(env: &mut Env, ad: &ast::AliasDecl) {
    let name = &ad.name;
    let resolved = resolve_type_ref(&ad.target);
    let ty = Ty::Alias(name.clone(), Box::new(resolved));
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        ad.visibility,
        ad.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

fn collect_newtype(env: &mut Env, nd: &ast::NewtypeDecl) {
    let name = &nd.name;
    let inner = resolve_type_ref(&nd.inner);
    let ty = Ty::Newtype(name.clone(), Box::new(inner.clone()));
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        nd.visibility,
        nd.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);

    // Register a synthetic constructor function so `UserId("alice")`
    // resolves as a function call during the resolve pass.
    let constructor = EFn {
        name: name.clone(),
        params: vec![("_0".to_owned(), inner.clone())],
        ret_ty: Ty::Newtype(name.clone(), Box::new(inner)),
        body: EExpr::Var(Ty::Error, "_0".to_owned(), None),
        contracts: vec![],
        span: Some(nd.span),
        file: None,
    };
    env.insert_fn(name, constructor);
}

/// Convert a parse-level `TypeRef` to a semantic `Ty`.
/// Resolves builtins and preserves other names for semantic resolution.
pub fn resolve_type_ref(tr: &ast::TypeRef) -> Ty {
    match &tr.kind {
        ast::TypeRefKind::Simple(n) => match resolve_builtin(n) {
            Some(b) => Ty::Builtin(b),
            None => Ty::Named(n.clone()),
        },
        ast::TypeRefKind::Param(n, args) => {
            let resolved_args: Vec<Ty> = args.iter().map(resolve_type_ref).collect();
            match (n.as_str(), resolved_args.as_slice()) {
                ("Set", [a]) => Ty::Set(Box::new(a.clone())),
                ("Seq", [a]) => Ty::Seq(Box::new(a.clone())),
                ("Map", [k, v]) => Ty::Map(Box::new(k.clone()), Box::new(v.clone())),
                ("Store", [Ty::Named(entity) | Ty::Entity(entity)]) => Ty::Store(entity.clone()),
                ("Rel", [Ty::Tuple(columns)]) => Ty::Relation(columns.clone()),
                ("Rel", columns) if !columns.is_empty() => Ty::Relation(columns.to_vec()),
                _ => Ty::Param(n.clone(), resolved_args),
            }
        }
        ast::TypeRefKind::Tuple(ts) => Ty::Tuple(ts.iter().map(resolve_type_ref).collect()),
        ast::TypeRefKind::Fn(a, b) => {
            Ty::Fn(Box::new(resolve_type_ref(a)), Box::new(resolve_type_ref(b)))
        }
        ast::TypeRefKind::Paren(inner) => resolve_type_ref(inner),
        ast::TypeRefKind::Refine(base, pred) | ast::TypeRefKind::RefineParam(base, pred) => {
            let base_ty = resolve_type_ref(base);
            let pred_expr = collect_expr(pred);
            Ty::Refinement(Box::new(base_ty), Box::new(pred_expr))
        }
        ast::TypeRefKind::NamedRefine(param_name, base, pred) => {
            // Named refinement: `b: bool{b == true}`.
            // Rewrite param references to `$` so the resolve pass can
            // bind `$` uniformly. Also bind the original name.
            let base_ty = resolve_type_ref(base);
            let mut pred_expr = collect_expr(pred);
            rename_var_in_expr(&mut pred_expr, param_name, "$");
            Ty::Refinement(Box::new(base_ty), Box::new(pred_expr))
        }
    }
}

/// Rename all occurrences of variable `from` to `to` in an expression.
/// Used by named refinements: `b: bool{b == true}` → `$: bool{$ == true}`.
fn rename_var_in_expr(e: &mut EExpr, from: &str, to: &str) {
    match e {
        EExpr::Var(_, name, _) if name == from => {
            to.clone_into(name);
        }
        EExpr::BinOp(_, _, a, b, _) => {
            rename_var_in_expr(a, from, to);
            rename_var_in_expr(b, from, to);
        }
        EExpr::UnOp(_, _, a, _) => {
            rename_var_in_expr(a, from, to);
        }
        EExpr::Call(_, f, args, _) => {
            rename_var_in_expr(f, from, to);
            for arg in args {
                rename_var_in_expr(arg, from, to);
            }
        }
        _ => {}
    }
}

fn resolve_builtin(name: &str) -> Option<BuiltinTy> {
    match name {
        "int" => Some(BuiltinTy::Int),
        "bool" => Some(BuiltinTy::Bool),
        "string" => Some(BuiltinTy::String),
        "identity" => Some(BuiltinTy::Identity),
        "real" => Some(BuiltinTy::Real),
        "float" => Some(BuiltinTy::Float),
        _ => None,
    }
}

fn resolve_param_ty(p: &ast::Param) -> Ty {
    resolve_type_ref(&p.ty)
}

// ── Predicates, properties, verify, scene, theorem, axiom, lemma ─────

fn collect_pred(env: &mut Env, pd: &ast::PredDecl) {
    let name = &pd.name;
    let params: Vec<(String, Ty)> = pd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let ep = EPred {
        name: name.clone(),
        params,
        body: collect_expr(&pd.body),
        span: Some(pd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Pred, name.clone(), None, pd.visibility, pd.span);
    env.add_decl(name, info);
    env.insert_pred(name, ep);
}

fn collect_prop(env: &mut Env, pd: &ast::PropDecl) {
    let name = &pd.name;
    let target = if pd.systems.is_empty() {
        None
    } else {
        Some(pd.systems.join(","))
    };
    let ep = EProp {
        name: name.clone(),
        target,
        body: collect_expr(&pd.body),
        span: Some(pd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Prop, name.clone(), None, pd.visibility, pd.span);
    env.add_decl(name, info);
    env.insert_prop(name, ep);
}

fn collect_verify(env: &mut Env, vd: &ast::VerifyDecl) {
    let name = &vd.name;
    // extract stores and let bindings from assume block.
    let mut stores = Vec::new();
    let mut proc_bounds = Vec::new();
    let mut let_bindings = Vec::new();
    if let Some(ref ab) = vd.assume_block {
        for item in &ab.items {
            match item {
                ast::AssumeItem::Store(sd) => stores.push(EStoreDecl {
                    name: sd.name.clone(),
                    entity_type: sd.entity_type.clone(),
                    lo: sd.lo,
                    hi: sd.hi,
                }),
                ast::AssumeItem::Let(ld) => let_bindings.push(ELetBinding {
                    name: ld.name.clone(),
                    system_type: ld.system_type.clone(),
                    store_bindings: ld.fields.clone(),
                }),
                _ => {} // Fair/StrongFair/Stutter/NoStutter handled by resolve pass
            }
        }
        for item in &ab.items {
            if let ast::AssumeItem::Proc(pd) = item {
                if let Some(bound) = resolve_proc_bound(env, pd, &let_bindings) {
                    proc_bounds.push(bound);
                }
            }
        }
    }
    let asserts: Vec<EExpr> = vd.asserts.iter().map(collect_expr).collect();
    let ev = EVerify {
        name: name.clone(),
        depth: vd.depth,
        stores,
        proc_bounds,
        let_bindings,
        assume_block: vd.assume_block.clone(),
        // collect installs the construct default. The resolve
        // pass walks `assume_block` and populates the rest after all
        // systems are visible (see `resolve_assumption_sets`).
        assumption_set: crate::elab::types::AssumptionSet::default_for_verify(),
        asserts,
        span: Some(vd.span),
        file: env.current_file.clone(),
    };
    let key = format!("verify:{name}");
    let info = env.make_decl_info(
        DeclKind::Verify,
        key.clone(),
        None,
        Visibility::Public,
        vd.span,
    );
    env.add_decl(&key, info);
    env.verifies.push(ev);
}

fn resolve_proc_bound(
    env: &mut Env,
    pd: &ast::ProcBoundDecl,
    let_bindings: &[ELetBinding],
) -> Option<EProcBoundDecl> {
    fn lookup_system<'a>(env: &'a Env, name: &str) -> Option<&'a crate::elab::types::ESystem> {
        env.systems.get(name).or_else(|| {
            let mut matches = env
                .systems
                .iter()
                .filter(|(key, _)| key.rsplit("::").next().is_some_and(|bare| bare == name))
                .map(|(_, system)| system)
                .collect::<Vec<_>>();
            match matches.len() {
                1 => matches.pop(),
                _ => None,
            }
        })
    }

    let (proc_name, owner_segments) = pd.path.segments.split_last()?;
    let system_type = match owner_segments {
        [] => {
            let mut matches = let_bindings
                .iter()
                .filter(|lb| {
                    env.systems
                        .get(lb.system_type.as_str())
                        .is_some_and(|sys| sys.procs.iter().any(|proc| proc.name == *proc_name))
                })
                .map(|lb| lb.system_type.clone())
                .collect::<Vec<_>>();
            matches.sort();
            matches.dedup();
            match matches.as_slice() {
                [system_type] => system_type.clone(),
                [] => {
                    env.errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!("unknown proc bound target `{}`", pd.path.segments.join(".")),
                        "bind the owning system with `let` first or qualify the proc with `System::proc`"
                            .to_owned(),
                        pd.span,
                    ));
                    return None;
                }
                _ => {
                    env.errors.push(ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!("ambiguous bare proc bound `{}`", pd.path.segments.join(".")),
                        "qualify the proc bound with `instance.proc` or `System::proc`".to_owned(),
                        pd.span,
                    ));
                    return None;
                }
            }
        }
        [owner] => {
            if let Some(lb) = let_bindings.iter().find(|lb| lb.name == *owner) {
                lb.system_type.clone()
            } else {
                owner.clone()
            }
        }
        _ => {
            env.errors.push(ElabError::with_span(
                ErrorKind::InvalidScope,
                format!("invalid proc bound target `{}`", pd.path.segments.join(".")),
                "use `proc instance.proc[lo..hi]` or `proc System::proc[lo..hi]`".to_owned(),
                pd.span,
            ));
            return None;
        }
    };

    let Some(system) = lookup_system(env, system_type.as_str()) else {
        env.errors.push(ElabError::with_span(
            ErrorKind::UndefinedRef,
            format!("unknown system `{system_type}` in proc bound"),
            String::new(),
            pd.span,
        ));
        return None;
    };
    if !system.procs.iter().any(|proc| proc.name == *proc_name) {
        env.errors.push(ElabError::with_span(
            ErrorKind::UndefinedRef,
            format!("system `{system_type}` has no proc `{proc_name}`"),
            String::new(),
            pd.span,
        ));
        return None;
    }

    Some(EProcBoundDecl {
        system_type,
        proc: proc_name.clone(),
        lo: pd.lo,
        hi: pd.hi,
    })
}

fn collect_scene(env: &mut Env, sd: &ast::SceneDecl) {
    let name = &sd.name;
    let mut stores = Vec::new();
    let mut let_bindings = Vec::new();
    let mut givens = Vec::new();
    let mut whens = Vec::new();
    let mut thens = Vec::new();
    let mut given_constraints = Vec::new();
    let mut activations = Vec::new();

    // Track event var name counts for deduplication (e.g. two calls to
    // auth.login_failed become auth_login_failed and auth_login_failed_2).
    let mut var_name_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for item in &sd.items {
        match item {
            ast::SceneItem::WhenAssume { expr, .. } => {
                whens.push(ESceneWhen::Assume(collect_expr(expr)));
            }
            ast::SceneItem::ThenAssert { expr, .. } => {
                thens.push(collect_expr(expr));
            }
            ast::SceneItem::GivenBlock { items, .. } => {
                for gi in items {
                    match gi {
                        ast::GivenItem::EntityBinding {
                            name,
                            entity_type,
                            store_name,
                            condition,
                            ..
                        } => givens.push(ESceneGiven {
                            var: name.clone(),
                            entity_type: entity_type.clone(),
                            store_name: store_name.clone(),
                            condition: condition.as_ref().map(collect_expr),
                        }),
                        ast::GivenItem::Store(sd) => stores.push(EStoreDecl {
                            name: sd.name.clone(),
                            entity_type: sd.entity_type.clone(),
                            lo: sd.lo,
                            hi: sd.hi,
                        }),
                        ast::GivenItem::Let(ld) => let_bindings.push(ELetBinding {
                            name: ld.name.clone(),
                            system_type: ld.system_type.clone(),
                            store_bindings: ld.fields.clone(),
                        }),
                        ast::GivenItem::Activate(ad) => {
                            activations.push(EActivation {
                                instances: ad.instances.clone(),
                                store_name: ad.store_name.clone(),
                            });
                        }
                        ast::GivenItem::Constraint { expr, .. } => {
                            // Constraint expressions in given blocks are initial-state
                            // assumptions, not end-state assertions (then).
                            given_constraints.push(collect_expr(expr));
                        }
                        ast::GivenItem::Error(_) => {}
                    }
                }
            }
            ast::SceneItem::WhenBlock { items, .. } => {
                for wi in items {
                    match wi {
                        ast::WhenItem::InstanceCall {
                            instance,
                            command,
                            args,
                            card,
                            ..
                        } => {
                            // instance-qualified calls.
                            // Resolve instance name to system type through let bindings.
                            let system_type = let_bindings
                                .iter()
                                .find(|lb| lb.name == *instance)
                                .map_or_else(|| instance.clone(), |lb| lb.system_type.clone());
                            let eargs: Vec<EExpr> = args.iter().map(collect_invoc_arg).collect();

                            // Deduplicate event var names: first occurrence gets
                            // "inst_cmd", subsequent get "inst_cmd_2", "inst_cmd_3", etc.
                            let base_var = format!("{instance}_{command}");
                            let count = var_name_counts.entry(base_var.clone()).or_insert(0);
                            *count += 1;
                            let var = if *count == 1 {
                                base_var
                            } else {
                                format!("{base_var}_{count}")
                            };

                            whens.push(ESceneWhen::Action {
                                var,
                                system: system_type,
                                event: command.clone(),
                                args: eargs,
                                card: card.clone().or_else(|| Some("one".to_owned())),
                            });
                        }
                        ast::WhenItem::LetCall {
                            name,
                            instance,
                            command,
                            args,
                            card,
                            ..
                        } => {
                            let system_type = let_bindings
                                .iter()
                                .find(|lb| lb.name == *instance)
                                .map_or_else(|| instance.clone(), |lb| lb.system_type.clone());
                            let eargs: Vec<EExpr> = args.iter().map(collect_invoc_arg).collect();

                            whens.push(ESceneWhen::Action {
                                var: name.clone(),
                                system: system_type,
                                event: command.clone(),
                                args: eargs,
                                card: card.clone().or_else(|| Some("one".to_owned())),
                            });
                        }
                        ast::WhenItem::Assume { expr, .. } => {
                            whens.push(ESceneWhen::Assume(collect_expr(expr)));
                        }
                        ast::WhenItem::Error(_) => {}
                    }
                }
            }
            ast::SceneItem::ThenBlock { items, .. } => {
                for ti in items {
                    thens.push(collect_expr(&ti.expr));
                }
            }
            ast::SceneItem::Error(_) => {}
        }
    }

    let es = EScene {
        name: name.clone(),
        stores,
        let_bindings,
        givens,
        whens,
        thens,
        given_constraints,
        activations,
        span: Some(sd.span),
        file: env.current_file.clone(),
    };
    let key = format!("scene:{name}");
    let info = env.make_decl_info(
        DeclKind::Scene,
        key.clone(),
        None,
        Visibility::Public,
        sd.span,
    );
    env.add_decl(&key, info);
    env.scenes.push(es);
}

fn collect_theorem(env: &mut Env, td: &ast::TheoremDecl) {
    collect_theorem_with_under(env, td, None);
}

/// collect a theorem, optionally inside an
/// enclosing `under` block. The `enclosing_under_idx` references a
/// canonical `EUnderBlock` already pushed onto `env.under_blocks`.
/// The resolve pass uses that block's `resolved_set` as the floor.
fn collect_theorem_with_under(
    env: &mut Env,
    td: &ast::TheoremDecl,
    enclosing_under_idx: Option<usize>,
) {
    if let Some(ab) = td.assume_block.as_ref() {
        for item in &ab.items {
            if let ast::AssumeItem::Proc(pd) = item {
                env.errors.push(ElabError::with_span(
                    ErrorKind::InvalidScope,
                    "proc bounds are only allowed in verify blocks".to_owned(),
                    "move this `proc ...[lo..hi]` item to a `verify` block".to_owned(),
                    pd.span,
                ));
            }
        }
    }
    let name = &td.name;
    let et = ETheorem {
        name: name.clone(),
        targets: td.systems.clone(),
        assume_block: td.assume_block.clone(),
        enclosing_under_idx,
        // theorems default to stutter on. Resolve pass populates
        // the rest of the set from `assume_block` and `enclosing_under_idx`.
        assumption_set: crate::elab::types::AssumptionSet::default_for_theorem_or_lemma(),
        invariants: td.invariants.iter().map(collect_expr).collect(),
        shows: td.shows.iter().map(collect_expr).collect(),
        by_file: td.by_file.clone(),
        by_lemmas: td.by_lemmas.clone(),
        span: Some(td.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Theorem,
        name.clone(),
        None,
        Visibility::Public,
        td.span,
    );
    env.add_decl(name, info);
    env.theorems.push(et);
}

fn collect_axiom(env: &mut Env, ad: &ast::AxiomDecl) {
    let name = &ad.name;
    let ea = EAxiom {
        name: name.clone(),
        body: collect_expr(&ad.body),
        by_file: ad.by_file.clone(),
        span: Some(ad.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Axiom,
        name.clone(),
        None,
        Visibility::Public,
        ad.span,
    );
    env.add_decl(name, info);
    env.axioms.push(ea);
}

fn collect_lemma(env: &mut Env, ld: &ast::LemmaDecl) {
    collect_lemma_with_under(env, ld, None);
}

/// collect a lemma, optionally inside an
/// enclosing `under` block. See `collect_theorem_with_under`.
fn collect_lemma_with_under(
    env: &mut Env,
    ld: &ast::LemmaDecl,
    enclosing_under_idx: Option<usize>,
) {
    if let Some(ab) = ld.assume_block.as_ref() {
        for item in &ab.items {
            if let ast::AssumeItem::Proc(pd) = item {
                env.errors.push(ElabError::with_span(
                    ErrorKind::InvalidScope,
                    "proc bounds are only allowed in verify blocks".to_owned(),
                    "move this `proc ...[lo..hi]` item to a `verify` block".to_owned(),
                    pd.span,
                ));
            }
        }
    }
    let name = &ld.name;
    let el = ELemma {
        name: name.clone(),
        assume_block: ld.assume_block.clone(),
        enclosing_under_idx,
        // lemmas default to stutter on. Resolve pass populates
        // the rest of the set from `assume_block` and `enclosing_under_idx`.
        assumption_set: crate::elab::types::AssumptionSet::default_for_theorem_or_lemma(),
        body: ld.body.iter().map(collect_expr).collect(),
        span: Some(ld.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Lemma,
        name.clone(),
        None,
        Visibility::Public,
        ld.span,
    );
    env.add_decl(name, info);
    env.lemmas.push(el);
}

/// collect an `under { }` block. The block is
/// represented as a single canonical `EUnderBlock` on `env.under_blocks`,
/// and each member theorem/lemma is registered with that block's index.
/// The resolve pass resolves the under's items exactly once with the
/// shared scope, then every member shares the same canonical
/// `resolved_set` — siblings cannot diverge on what `fair tick` means
/// the way they would if the raw items were re-resolved per member.
///
/// Shared scope: the union of all member theorems' target systems.
/// When the under contains only lemmas, the scope is empty and the
/// resolve pass falls back to the full system list (the same scope a
/// standalone lemma would use).
fn collect_under(env: &mut Env, ub: &ast::UnderBlock) {
    // Compute the shared resolution scope: union of theorem targets
    // (deduped, preserving first-seen order so diagnostics list
    // systems in user-visible order).
    let mut scope: Vec<String> = Vec::new();
    for td in &ub.theorems {
        for sys in &td.systems {
            if !scope.contains(sys) {
                scope.push(sys.clone());
            }
        }
    }

    let under_idx = env.under_blocks.len();
    env.under_blocks.push(crate::elab::types::EUnderBlock {
        items: ub.items.clone(),
        scope,
        span: ub.span,
        // review fix: capture module/file provenance at
        // collect time so `build_working_namespace` can filter
        // foreign-module under blocks the same way it filters
        // theorems/lemmas, and so multi-module loads do not leak
        // foreign environments into a local resolution.
        module: env.module_name.clone(),
        file: env.current_file.clone(),
        // Resolve pass populates this. The construct default
        // (stutter on for theorems/lemmas) is applied at resolve time.
        resolved_set: crate::elab::types::AssumptionSet::default_for_theorem_or_lemma(),
    });

    for td in &ub.theorems {
        collect_theorem_with_under(env, td, Some(under_idx));
    }
    for ld in &ub.lemmas {
        collect_lemma_with_under(env, ld, Some(under_idx));
    }
}

fn collect_const(env: &mut Env, cd: &ast::ConstDecl) {
    let name = &cd.name;
    let ec = EConst {
        name: name.clone(),
        body: collect_expr(&cd.value),
        span: Some(cd.span),
    };
    let info = env.make_decl_info(DeclKind::Const, name.clone(), None, cd.visibility, cd.span);
    env.add_decl(name, info);
    env.insert_const(name, ec);
}

fn collect_fn(env: &mut Env, fd: &ast::FnDecl) {
    let name = &fd.name;
    let params: Vec<(String, Ty)> = fd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
        .collect();
    let ret = resolve_type_ref(&fd.ret_type);
    let contracts = fd.contracts.iter().map(collect_contract).collect();
    let ef = EFn {
        name: name.clone(),
        params,
        ret_ty: ret,
        contracts,
        body: collect_expr(&fd.body),
        span: Some(fd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Fn, name.clone(), None, fd.visibility, fd.span);
    env.add_decl(name, info);
    env.insert_fn(name, ef);
}

fn collect_contract(c: &ast::Contract) -> EContract {
    match c {
        ast::Contract::Requires { expr, .. } => EContract::Requires(collect_expr(expr)),
        ast::Contract::Ensures { expr, .. } => EContract::Ensures(collect_expr(expr)),
        ast::Contract::Decreases { measures, star, .. } => EContract::Decreases {
            measures: measures.iter().map(collect_expr).collect(),
            star: *star,
        },
        ast::Contract::Invariant { expr, .. } => EContract::Invariant(collect_expr(expr)),
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::lex;
    use crate::parse::Parser;

    fn collect_src(src: &str) -> Env {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        let prog = parser.parse_program().expect("parse error");
        collect(&prog)
    }

    #[test]
    fn module_name_tracked() {
        let env = collect_src("module Commerce");
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
    }

    #[test]
    fn duplicate_module_errors_and_keeps_first() {
        let env = collect_src("module Commerce\nmodule Billing");
        // First module name wins — not overwritten on conflict
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        assert!(
            env.errors
                .iter()
                .any(|e| format!("{e:?}").contains("conflicting module")),
            "expected conflicting module error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn same_module_twice_no_error() {
        let env = collect_src("module Commerce\nmodule Commerce");
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        assert!(
            env.errors.is_empty(),
            "duplicate same-name module should not error"
        );
    }

    #[test]
    fn include_paths_tracked() {
        let env = collect_src(r#"include "billing.ab""#);
        assert_eq!(env.includes, vec!["billing.ab"]);
    }

    #[test]
    fn include_preserves_order() {
        let env = collect_src(
            r#"include "first.ab"
include "second.ab""#,
        );
        assert_eq!(env.includes, vec!["first.ab", "second.ab"]);
    }

    #[test]
    fn use_decls_tracked() {
        let env = collect_src("use Commerce::Order\nuse Billing::*\nuse Fulfillment::Ship as S");
        assert_eq!(env.use_decls.len(), 3);
    }

    #[test]
    fn use_decls_preserve_order() {
        let env = collect_src("use A::X\nuse B::Y\nuse C::Z");
        assert_eq!(env.use_decls.len(), 3);
        // First should be A::X
        if let ast::UseDecl::Single { module, name, .. } = &env.use_decls[0].decl {
            assert_eq!(module, "A");
            assert_eq!(name, "X");
        } else {
            panic!("expected Single");
        }
        // Third should be C::Z
        if let ast::UseDecl::Single { module, name, .. } = &env.use_decls[2].decl {
            assert_eq!(module, "C");
            assert_eq!(name, "Z");
        } else {
            panic!("expected Single");
        }
    }

    #[test]
    fn type_visibility_private_by_default() {
        let env = collect_src("enum Status = Active | Inactive");
        let info = env.decls.get("Status").expect("Status decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn type_visibility_without_modifier() {
        let env = collect_src("enum Status = Active | Inactive");
        let info = env.decls.get("Status").expect("Status decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn entity_visibility_private_by_default() {
        let env = collect_src("entity Order { id: identity }");
        let info = env.decls.get("Order").expect("Order decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    /// derived fields declared on an entity are
    /// collected into `EEntity::derived_fields` with their bodies
    /// elaborated and types inferred from the body expression.
    #[test]
    fn entity_derived_field_collected() {
        let env = collect_src("entity Order { id: identity\nderived total = 0 }");
        let ee = env.entities.get("Order").expect("Order entity");
        assert_eq!(ee.derived_fields.len(), 1, "expected one derived field");
        assert_eq!(ee.derived_fields[0].name, "total");
    }

    /// derived fields declared on a system are
    /// collected into `ESystem::derived_fields`.
    #[test]
    fn system_derived_field_collected() {
        let env = collect_src("system Shop(orders: Store<Order>) { derived total = 0 }");
        let es = env.systems.get("Shop").expect("Shop system");
        assert_eq!(es.derived_fields.len(), 1);
        assert_eq!(es.derived_fields[0].name, "total");
    }

    /// a self-referential derived field is rejected
    /// with `CyclicDefinition`. The cycle path is included in the message
    /// (`derived_cycle` helper from messages.rs).
    #[test]
    fn entity_derived_field_self_reference_rejected() {
        let env = collect_src("entity X { derived a = a }");
        assert!(
            env.errors
                .iter()
                .any(|e| e.kind == ErrorKind::CyclicDefinition
                    && e.message.contains("derived field cycle")
                    && e.message.contains("a -> a")),
            "expected CyclicDefinition for `a -> a`, got: {:?}",
            env.errors
        );
    }

    /// a two-derived cycle (`a -> b -> a`) is rejected.
    #[test]
    fn entity_derived_field_two_cycle_rejected() {
        let env = collect_src("entity X { derived a = b\nderived b = a }");
        assert!(
            env.errors
                .iter()
                .any(|e| e.kind == ErrorKind::CyclicDefinition
                    && e.message.contains("derived field cycle")),
            "expected CyclicDefinition for two-derived cycle, got: {:?}",
            env.errors
        );
    }

    /// a non-cyclic chain (`a -> b -> c`) is accepted.
    #[test]
    fn entity_derived_field_chain_no_cycle() {
        let env = collect_src("entity X { derived a = b\nderived b = c\nderived c = 1 }");
        assert!(
            !env.errors
                .iter()
                .any(|e| e.kind == ErrorKind::CyclicDefinition),
            "non-cyclic chain should not produce CyclicDefinition, got: {:?}",
            env.errors
        );
    }

    /// a quantifier-bound variable that
    /// shadows the derived field's own name must NOT be reported as a
    /// self-cycle. The inner `a` here is the quantifier binder, not a
    /// reference to the outer derived field `a`.
    #[test]
    fn entity_derived_field_quant_binder_does_not_self_cycle() {
        let env = collect_src("entity X { id: int\nderived a = all a: int | a > 0 }");
        assert!(
            !env.errors
                .iter()
                .any(|e| e.kind == ErrorKind::CyclicDefinition),
            "quantifier binder shadowing derived name must not produce \
             CyclicDefinition, got: {:?}",
            env.errors
        );
    }

    /// a `let`-bound variable that shadows
    /// the derived field's own name must NOT be reported as a
    /// self-cycle.
    #[test]
    fn entity_derived_field_let_binder_does_not_self_cycle() {
        let env = collect_src("entity X { id: int\nderived a = let a = 0 in a }");
        assert!(
            !env.errors
                .iter()
                .any(|e| e.kind == ErrorKind::CyclicDefinition),
            "let binder shadowing derived name must not produce \
             CyclicDefinition, got: {:?}",
            env.errors
        );
    }

    /// two derived fields on the same
    /// entity with the same name must produce a `DuplicateDecl`
    /// diagnostic, not silently collapse.
    #[test]
    fn entity_derived_field_duplicate_name_rejected() {
        let env = collect_src("entity X { derived a = 0\nderived a = 1 }");
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("derived")
                && e.message.contains('a')),
            "expected DuplicateDecl for two derived fields named `a`, got: {:?}",
            env.errors
        );
    }

    /// a derived field that shares a name
    /// with a regular entity field must be rejected. says names
    /// are unique across fields, derived fields, and actions.
    #[test]
    fn entity_derived_field_collides_with_regular_field() {
        let env = collect_src("entity X { id: int\nderived id = 0 }");
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("derived")
                && e.message.contains("id")),
            "expected DuplicateDecl for derived `id` colliding with field `id`, \
             got: {:?}",
            env.errors
        );
    }

    /// same uniqueness rule applies to
    /// system-level derived fields.
    #[test]
    fn system_derived_field_duplicate_name_rejected() {
        let env = collect_src("system Shop(orders: Store<Order>) { derived a = 0\nderived a = 1 }");
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("derived")
                && e.message.contains('a')),
            "expected DuplicateDecl for two system derived fields named `a`, \
             got: {:?}",
            env.errors
        );
    }

    /// an entity invariant is collected into
    /// `EEntity::invariants` with its name and elaborated body.
    #[test]
    fn entity_invariant_collected() {
        let env = collect_src(
            "entity Account { balance: int = 0\ninvariant non_negative { balance >= 0 } }",
        );
        let ee = env.entities.get("Account").expect("Account entity");
        assert_eq!(ee.invariants.len(), 1);
        assert_eq!(ee.invariants[0].name, "non_negative");
    }

    /// a system invariant is collected into
    /// `ESystem::invariants`.
    #[test]
    fn system_invariant_collected() {
        let env = collect_src(
            "system Banking(accounts: Store<Account>) { invariant solvent { all a: Account | a.balance >= 0 } }",
        );
        let es = env.systems.get("Banking").expect("Banking system");
        assert_eq!(es.invariants.len(), 1);
        assert_eq!(es.invariants[0].name, "solvent");
    }

    /// multiple invariants on the same entity
    /// are collected separately.
    #[test]
    fn entity_multiple_invariants_collected() {
        let env = collect_src(
            "entity Account { balance: int = 0\nis_frozen: bool = false\n\
             invariant non_negative { balance >= 0 }\n\
             invariant frozen_zero { is_frozen implies balance == 0 } }",
        );
        let ee = env.entities.get("Account").expect("Account entity");
        assert_eq!(ee.invariants.len(), 2);
    }

    /// two invariants with the same name on
    /// the same entity must be rejected as a duplicate declaration.
    #[test]
    fn entity_duplicate_invariant_name_rejected() {
        let env = collect_src(
            "entity X { balance: int = 0\n\
             invariant a { balance >= 0 }\n\
             invariant a { balance >= 1 } }",
        );
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("invariant")
                && e.message.contains('a')),
            "expected DuplicateDecl for two invariants named `a`, got: {:?}",
            env.errors
        );
    }

    /// an invariant whose name collides with a
    /// regular field, derived field, or action must be rejected.
    #[test]
    fn entity_invariant_name_collides_with_field() {
        let env = collect_src(
            "entity X { balance: int = 0\n\
             invariant balance { balance >= 0 } }",
        );
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("invariant")
                && e.message.contains("balance")),
            "expected DuplicateDecl for invariant `balance` colliding with \
             field `balance`, got: {:?}",
            env.errors
        );
    }

    /// same uniqueness rule applies to system
    /// invariants.
    #[test]
    fn system_duplicate_invariant_name_rejected() {
        let env = collect_src(
            "system S(accounts: Store<Account>) {\
             invariant a { all x: Account | x.balance >= 0 }\n\
             invariant a { all x: Account | x.balance >= 1 } }",
        );
        assert!(
            env.errors.iter().any(|e| e.kind == ErrorKind::DuplicateDecl
                && e.message.contains("invariant")
                && e.message.contains('a')),
            "expected DuplicateDecl for two system invariants named `a`, \
             got: {:?}",
            env.errors
        );
    }

    #[test]
    fn entity_visibility_without_modifier() {
        let env = collect_src("entity Order { id: identity }");
        let info = env.decls.get("Order").expect("Order decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn system_always_public() {
        let env = collect_src("system S { }");
        let info = env.decls.get("S").expect("S decl");
        assert_eq!(info.visibility, Visibility::Public);
    }

    #[test]
    fn fn_visibility_without_modifier() {
        let env = collect_src("fn total(x: int): int = x");
        let info = env.decls.get("total").expect("total");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn const_visibility() {
        let env = collect_src("const A = 1\nconst B = 2");
        assert_eq!(env.decls.get("A").unwrap().visibility, Visibility::Private);
        assert_eq!(env.decls.get("B").unwrap().visibility, Visibility::Private);
    }

    #[test]
    fn decl_module_tagged() {
        let env = collect_src("module Commerce\nenum Status = Active | Inactive");
        let info = env
            .lookup_decl_qualified("Commerce", "Status")
            .expect("Commerce::Status decl");
        assert_eq!(info.module.as_deref(), Some("Commerce"));
    }

    #[test]
    fn decl_module_none_without_module_decl() {
        let env = collect_src("enum Status = Active | Inactive");
        let info = env.lookup_decl("Status").expect("Status decl");
        assert_eq!(info.module, None);
    }

    #[test]
    fn multi_file_collect_into() {
        let mut env = Env::new();
        let prog1 = {
            let tokens = lex::lex("module Commerce\nenum Status = Active").unwrap();
            let mut p = Parser::new(tokens);
            p.parse_program().unwrap()
        };
        let prog2 = {
            let tokens = lex::lex("module Commerce\nenum Payment = Pending | Done").unwrap();
            let mut p = Parser::new(tokens);
            p.parse_program().unwrap()
        };
        collect_into(&mut env, &prog1);
        collect_into(&mut env, &prog2);
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        // Types are stored with qualified keys during collection
        assert!(env.types.contains_key("Commerce::Status"));
        assert!(env.types.contains_key("Commerce::Payment"));
        // After building working namespace, bare names are available
        env.build_working_namespace();
        assert!(env.types.contains_key("Status"));
        assert!(env.types.contains_key("Payment"));
        assert!(env.errors.is_empty());
    }

    #[test]
    fn visibility_error_on_private_import() {
        // Simulate: module A defines private type, module B imports it.
        // In a single file, we test the resolve pass catches it.
        let env = collect_src("module TestMod\nenum Secret = X | Y\nuse TestMod::Secret");
        // Collector doesn't enforce visibility — that's resolve's job.
        // But we can verify the declaration is tagged private.
        let info = env
            .lookup_decl_qualified("TestMod", "Secret")
            .expect("TestMod::Secret decl");
        assert_eq!(info.visibility, Visibility::Private);
        assert_eq!(info.module.as_deref(), Some("TestMod"));
    }

    // ──: Alias elaboration tests ─────────────────────────

    #[test]
    fn alias_to_builtin() {
        let env = collect_src("type Money = real");
        let ty = env.types.get("Money").expect("Money type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Money" && matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::Real))),
            "expected Alias(Money, Builtin(real)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_tuple() {
        let env = collect_src("type Coord = (int, int)");
        let ty = env.types.get("Coord").expect("Coord type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Coord" && matches!(inner.as_ref(), Ty::Tuple(_))),
            "expected Alias(Coord, Tuple(...)), got {ty:?}"
        );
        if let Ty::Alias(_, inner) = ty {
            if let Ty::Tuple(ts) = inner.as_ref() {
                assert_eq!(ts.len(), 2);
            }
        }
    }

    #[test]
    fn alias_to_collection() {
        let env = collect_src("type Users = Set<identity>");
        let ty = env.types.get("Users").expect("Users type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Users" && matches!(inner.as_ref(), Ty::Set(_))),
            "expected Alias(Users, Set(...)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_map() {
        let env = collect_src("type Ledger = Map<identity, real>");
        let ty = env.types.get("Ledger").expect("Ledger type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Ledger" && matches!(inner.as_ref(), Ty::Map(_, _))),
            "expected Alias(Ledger, Map(...)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_function_type() {
        let env = collect_src("type Handler = int -> bool");
        let ty = env.types.get("Handler").expect("Handler type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Handler" && matches!(inner.as_ref(), Ty::Fn(_, _))),
            "expected Alias(Handler, Fn(...)), got {ty:?}"
        );
    }

    #[test]
    fn enum_single_variant() {
        // `enum Status = Pending` → single-variant enum
        let env = collect_src("enum Status = Pending");
        let ty = env.types.get("Status").expect("Status type");
        assert!(
            matches!(ty, Ty::Enum(n, ctors) if n == "Status" && ctors == &["Pending"]),
            "expected Enum(Status, [Pending]), got {ty:?}"
        );
    }

    #[test]
    fn enum_via_enum_keyword() {
        let env = collect_src("enum Color = Red | Green | Blue");
        let ty = env.types.get("Color").expect("Color type");
        assert!(
            matches!(ty, Ty::Enum(n, ctors) if n == "Color" && ctors.len() == 3),
            "expected Enum(Color, [Red, Green, Blue]), got {ty:?}"
        );
    }

    #[test]
    fn struct_via_struct_keyword() {
        let env = collect_src("struct Point { x: int, y: int }");
        let ty = env.types.get("Point").expect("Point type");
        assert!(
            matches!(ty, Ty::Record(n, fields) if n == "Point" && fields.len() == 2),
            "expected Record(Point, [x, y]), got {ty:?}"
        );
    }
}
