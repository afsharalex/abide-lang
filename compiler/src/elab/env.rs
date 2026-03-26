//! Symbol table and scope management for the Abide elaborator.

use std::collections::HashMap;

use super::error::{ElabError, ErrorKind};
use super::types::{
    EAxiom, EConst, EEntity, EFn, ELemma, EPred, EProp, EScene, ESystem, ETheorem, EVerify, Ty,
};

/// What kind of top-level declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Entity,
    System,
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

/// Information about a declaration in the symbol table.
#[derive(Debug, Clone)]
pub struct DeclInfo {
    pub kind: DeclKind,
    pub name: String,
    pub ty: Option<Ty>,
}

/// The elaboration environment (symbol table).
#[derive(Debug, Clone)]
pub struct Env {
    pub module_name: Option<String>,
    pub includes: Vec<String>,
    pub decls: HashMap<String, DeclInfo>,
    pub types: HashMap<String, Ty>,
    pub entities: HashMap<String, EEntity>,
    pub systems: HashMap<String, ESystem>,
    pub preds: HashMap<String, EPred>,
    pub props: HashMap<String, EProp>,
    pub verifies: Vec<EVerify>,
    pub scenes: Vec<EScene>,
    pub theorems: Vec<ETheorem>,
    pub axioms: Vec<EAxiom>,
    pub lemmas: Vec<ELemma>,
    pub consts: Vec<EConst>,
    pub fns: Vec<EFn>,
    pub errors: Vec<ElabError>,
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
            includes: Vec::new(),
            decls: HashMap::new(),
            types: HashMap::new(),
            entities: HashMap::new(),
            systems: HashMap::new(),
            preds: HashMap::new(),
            props: HashMap::new(),
            verifies: Vec::new(),
            scenes: Vec::new(),
            theorems: Vec::new(),
            axioms: Vec::new(),
            lemmas: Vec::new(),
            consts: Vec::new(),
            fns: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Add a declaration, reporting duplicates.
    pub fn add_decl(&mut self, name: &str, info: DeclInfo) {
        if let Some(existing) = self.decls.get(name) {
            self.errors.push(ElabError::new(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate declaration: {name} (already declared as {:?})",
                    existing.kind
                ),
                String::new(),
            ));
        } else {
            self.decls.insert(name.to_owned(), info);
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
