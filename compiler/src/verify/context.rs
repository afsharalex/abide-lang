//! Verification context — metadata extracted from IR for Z3 encoding.
//!
//! Built once per verification run, shared across all checks.

use std::collections::HashMap;

use crate::ir::types::{IRProgram, IRType};

// ── Variant ID mapping ──────────────────────────────────────────────

/// Maps enum variant names to sequential integer IDs for Z3 encoding.
///
/// Enum types are encoded as Z3 Int values where each variant is a
/// unique integer. This enables efficient equality checking and
/// domain constraints (`min_id` <= var <= `max_id`).
#[derive(Debug, Default)]
pub struct VariantMap {
    /// (`type_name`, `variant_name`) → unique i64 ID
    pub to_id: HashMap<(String, String), i64>,
    /// i64 ID → (`type_name`, `variant_name`) — for counterexample display
    pub from_id: HashMap<i64, (String, String)>,
    /// Next available ID
    next_id: i64,
}

impl VariantMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register all variants of an enum type. Returns (`min_id`, `max_id`).
    pub fn register_enum(&mut self, type_name: &str, variants: &[String]) -> (i64, i64) {
        let min_id = self.next_id;
        for v in variants {
            self.to_id
                .insert((type_name.to_owned(), v.clone()), self.next_id);
            self.from_id
                .insert(self.next_id, (type_name.to_owned(), v.clone()));
            self.next_id += 1;
        }
        let max_id = self.next_id - 1;
        (min_id, max_id)
    }

    /// Look up the ID for a variant. Panics if not registered.
    pub fn id_of(&self, type_name: &str, variant_name: &str) -> i64 {
        *self
            .to_id
            .get(&(type_name.to_owned(), variant_name.to_owned()))
            .unwrap_or_else(|| panic!("unknown variant: {type_name}::{variant_name}"))
    }

    /// Look up the variant name for an ID. Returns None if not found.
    pub fn name_of(&self, id: i64) -> Option<&(String, String)> {
        self.from_id.get(&id)
    }
}

// ── Entity field metadata ───────────────────────────────────────────

/// Metadata about a single entity field for Z3 encoding.
#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub ty: IRType,
    pub default: Option<String>, // default value as string (for initial state)
}

/// Metadata about an entity for Z3 encoding.
#[derive(Debug)]
pub struct EntityInfo {
    pub name: String,
    pub fields: Vec<FieldInfo>,
    pub actions: Vec<ActionInfo>,
}

/// Metadata about an entity action for Z3 encoding.
#[derive(Debug)]
pub struct ActionInfo {
    pub name: String,
    pub entity: String,
    /// Number of ref params + value params
    pub param_count: usize,
}

// ── Verification context ────────────────────────────────────────────

/// All metadata needed for Z3 encoding, extracted from the IR.
///
/// Built once per verification run. Shared across all verify/scene/theorem checks.
pub struct VerifyContext {
    /// Enum variant → integer ID mapping (for fieldless enums)
    pub variants: VariantMap,
    /// Enum type → (`min_id`, `max_id`) for domain constraints
    pub enum_ranges: HashMap<String, (i64, i64)>,
    /// Entity name → field/action metadata
    pub entities: HashMap<String, EntityInfo>,
    /// Z3 algebraic datatypes for enums with constructor fields.
    /// Maps enum name → DatatypeSort (sort + variant constructors/testers/accessors).
    pub adt_sorts: HashMap<String, z3::DatatypeSort>,
}

impl VerifyContext {
    /// Build a `VerifyContext` from an IR program.
    pub fn from_ir(ir: &IRProgram) -> Self {
        let mut variants = VariantMap::new();
        let mut enum_ranges = HashMap::new();
        let mut entities = HashMap::new();
        let mut adt_sorts = HashMap::new();

        // Register all enum types
        for ty_entry in &ir.types {
            if let IRType::Enum {
                name, variants: vs, ..
            } = &ty_entry.ty
            {
                let ctor_names: Vec<String> = vs.iter().map(|v| v.name.clone()).collect();
                let (min, max) = variants.register_enum(name, &ctor_names);
                enum_ranges.insert(name.clone(), (min, max));

                // Build Z3 ADT for enums with constructor fields
                if vs.iter().any(|v| !v.fields.is_empty()) {
                    let mut builder = z3::DatatypeBuilder::new(name.as_str());
                    for v in vs {
                        let fields: Vec<(&str, z3::DatatypeAccessor)> = v
                            .fields
                            .iter()
                            .map(|f| {
                                (
                                    f.name.as_str(),
                                    z3::DatatypeAccessor::Sort(
                                        crate::verify::smt::ir_type_to_sort(&f.ty),
                                    ),
                                )
                            })
                            .collect();
                        builder = builder.variant(&v.name, fields);
                    }
                    let dt = builder.finish();
                    adt_sorts.insert(name.clone(), dt);
                }
            }
        }

        // Register all entities
        for entity in &ir.entities {
            let fields = entity
                .fields
                .iter()
                .map(|f| FieldInfo {
                    name: f.name.clone(),
                    ty: f.ty.clone(),
                    default: None, // TODO: extract from IR
                })
                .collect();

            let actions = entity
                .transitions
                .iter()
                .map(|t| ActionInfo {
                    name: t.name.clone(),
                    entity: entity.name.clone(),
                    param_count: t.refs.len() + t.params.len(),
                })
                .collect();

            entities.insert(
                entity.name.clone(),
                EntityInfo {
                    name: entity.name.clone(),
                    fields,
                    actions,
                },
            );
        }

        Self {
            variants,
            enum_ranges,
            entities,
            adt_sorts,
        }
    }
}
