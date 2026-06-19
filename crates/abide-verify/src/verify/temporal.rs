//! Temporal formula normalization and compiled temporal summaries.

use serde::Serialize;

use crate::ir::types::{
    IRAction, IRActionMatchScrutinee, IREntity, IRExpr, IRSystem, IRVerify, LitVal,
};

use super::defenv;
use super::ltl::{Formula as LtlFormula, GeneralizedBuchi};

#[derive(Clone)]
pub enum LivenessPattern {
    Response {
        trigger: IRExpr,
        response: IRExpr,
    },
    Recurrence {
        response: IRExpr,
    },
    Eventuality {
        response: IRExpr,
    },
    Persistence {
        condition: IRExpr,
    },
    QuantifiedResponse {
        var: String,
        entity: String,
        trigger: IRExpr,
        response: IRExpr,
    },
    QuantifiedRecurrence {
        var: String,
        entity: String,
        response: IRExpr,
    },
    QuantifiedEventuality {
        var: String,
        entity: String,
        response: IRExpr,
    },
    QuantifiedPersistence {
        var: String,
        entity: String,
        condition: IRExpr,
    },
}

impl LivenessPattern {
    pub fn quantified_binding(&self) -> (Option<&str>, Option<&str>) {
        match self {
            LivenessPattern::Response { .. }
            | LivenessPattern::Recurrence { .. }
            | LivenessPattern::Eventuality { .. }
            | LivenessPattern::Persistence { .. } => (None, None),
            LivenessPattern::QuantifiedResponse { var, entity, .. }
            | LivenessPattern::QuantifiedRecurrence { var, entity, .. }
            | LivenessPattern::QuantifiedEventuality { var, entity, .. }
            | LivenessPattern::QuantifiedPersistence { var, entity, .. } => {
                (Some(var.as_str()), Some(entity.as_str()))
            }
        }
    }

    pub fn is_oneshot(&self) -> bool {
        matches!(
            self,
            LivenessPattern::Eventuality { .. } | LivenessPattern::QuantifiedEventuality { .. }
        )
    }
}

#[derive(Clone)]
pub struct PatternExtraction {
    pub pattern: LivenessPattern,
    pub safety_conjuncts: Vec<IRExpr>,
}

#[derive(Clone)]
pub struct CompiledTemporalFormula {
    expanded: IRExpr,
    contains_liveness: bool,
    contains_temporal: bool,
    contains_past_time: bool,
    extraction: Option<PatternExtraction>,
    spot: Option<CompiledSpotFormula>,
    buchi: Option<CompiledBuchiFormula>,
}

impl CompiledTemporalFormula {
    pub fn from_expr(expr: &IRExpr, defs: &defenv::DefEnv) -> Self {
        let expanded = super::expand_through_defs(expr, defs);
        Self::from_expanded(expanded)
    }

    pub fn from_expanded(expanded: IRExpr) -> Self {
        // `until` is *not* desugared into `eventually`/`always`: strong until is
        // not expressible with only F/G, so any such rewrite is unsound (it
        // forces the left operand to hold at every step where the right is
        // absent, even after the right has already occurred). Instead `until`
        // flows through to the native LTL→Büchi automaton and the Spot `U`
        // operator, and the liveness-pattern extractor declines to reduce it
        // (returning `None` → conservative Büchi fallback).
        let contains_liveness = contains_liveness(&expanded);
        let contains_temporal = contains_temporal(&expanded);
        let contains_past_time = contains_past_time(&expanded);
        let extraction = extract_liveness_pattern_inner(&expanded);
        let spot = compile_spot_formula(&expanded, contains_past_time);
        let buchi = compile_buchi_formula(&expanded, contains_past_time);
        Self {
            expanded,
            contains_liveness,
            contains_temporal,
            contains_past_time,
            extraction,
            spot,
            buchi,
        }
    }

    pub fn expanded(&self) -> &IRExpr {
        &self.expanded
    }

    pub fn contains_liveness(&self) -> bool {
        self.contains_liveness
    }

    pub fn contains_temporal(&self) -> bool {
        self.contains_temporal
    }

    pub fn contains_past_time(&self) -> bool {
        self.contains_past_time
    }

    pub fn extraction(&self) -> Option<&PatternExtraction> {
        self.extraction.as_ref()
    }

    pub fn spot(&self) -> Option<&CompiledSpotFormula> {
        self.spot.as_ref()
    }

    pub fn buchi(&self) -> Option<&CompiledBuchiFormula> {
        self.buchi.as_ref()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemporalFormula {
    True,
    False,
    Atom(String),
    Not(Box<TemporalFormula>),
    And(Vec<TemporalFormula>),
    Or(Vec<TemporalFormula>),
    Implies(Box<TemporalFormula>, Box<TemporalFormula>),
    Always(Box<TemporalFormula>),
    Eventually(Box<TemporalFormula>),
    Until(Box<TemporalFormula>, Box<TemporalFormula>),
}

#[derive(Clone)]
pub struct CompiledSpotFormula {
    root: TemporalFormula,
    atoms: Vec<SpotAtomBinding>,
}

#[derive(Clone)]
pub struct CompiledBuchiFormula {
    automaton: GeneralizedBuchi,
    atoms: Vec<BuchiAtomBinding>,
}

#[derive(Clone)]
struct SpotAtomBinding {
    label: String,
    expr: IRExpr,
}

#[derive(Clone)]
struct BuchiAtomBinding {
    expr: IRExpr,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TemporalFormulaExport {
    pub spot_formula: String,
    pub atoms: Vec<TemporalAtomExport>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BuchiAutomatonExport {
    pub format: &'static str,
    pub version: &'static str,
    pub automaton_kind: &'static str,
    pub acceptance: &'static str,
    pub hoa: String,
    pub state_count: usize,
    pub acceptance_set_count: usize,
    pub atoms: Vec<TemporalAtomExport>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TemporalAtomExport {
    pub label: String,
    pub expr_debug: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VerifyTemporalExport {
    pub assert_index: usize,
    pub contains_temporal: bool,
    pub contains_liveness: bool,
    pub contains_past_time: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub spot: Option<TemporalFormulaExport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub buchi: Option<BuchiAutomatonExport>,
}

impl CompiledSpotFormula {
    pub fn formula(&self) -> &TemporalFormula {
        &self.root
    }

    pub fn atoms(&self) -> usize {
        self.atoms.len()
    }

    pub fn to_spot_input(&self) -> String {
        render_spot_formula(&self.root)
    }

    pub fn export(&self) -> TemporalFormulaExport {
        TemporalFormulaExport {
            spot_formula: self.to_spot_input(),
            atoms: self
                .atoms
                .iter()
                .map(|binding| TemporalAtomExport {
                    label: binding.label.clone(),
                    expr_debug: format!("{:?}", binding.expr),
                })
                .collect(),
        }
    }
}

impl CompiledBuchiFormula {
    pub fn atoms(&self) -> usize {
        self.atoms.len()
    }

    pub fn state_count(&self) -> usize {
        self.automaton.state_count()
    }

    pub fn acceptance_set_count(&self) -> usize {
        self.automaton.acceptance_set_count()
    }

    pub(super) fn automaton(&self) -> &GeneralizedBuchi {
        &self.automaton
    }

    pub(super) fn atom_expr(&self, atom: usize) -> Option<&IRExpr> {
        self.atoms.get(atom).map(|binding| &binding.expr)
    }

    pub fn export(&self) -> BuchiAutomatonExport {
        let atom_labels = (0..self.atoms.len())
            .map(|atom| format!("p{atom}"))
            .collect::<Vec<_>>();
        BuchiAutomatonExport {
            format: "hoa",
            version: "v1",
            automaton_kind: "generalized-buchi",
            acceptance: "state",
            hoa: self.automaton.to_hoa(&atom_labels),
            state_count: self.automaton.state_count(),
            acceptance_set_count: self.automaton.acceptance_set_count(),
            atoms: self
                .atoms
                .iter()
                .enumerate()
                .map(|(atom, binding)| TemporalAtomExport {
                    label: format!("p{atom}"),
                    expr_debug: format!("{:?}", binding.expr),
                })
                .collect(),
        }
    }
}

pub fn export_verify_temporal_formulas(
    verify_block: &IRVerify,
    defs: &defenv::DefEnv,
) -> Vec<VerifyTemporalExport> {
    verify_block
        .asserts
        .iter()
        .enumerate()
        .map(|(assert_index, expr)| {
            let compiled = CompiledTemporalFormula::from_expr(expr, defs);
            VerifyTemporalExport {
                assert_index,
                contains_temporal: compiled.contains_temporal(),
                contains_liveness: compiled.contains_liveness(),
                contains_past_time: compiled.contains_past_time(),
                spot: compiled.spot().map(CompiledSpotFormula::export),
                buchi: compiled.buchi().map(CompiledBuchiFormula::export),
            }
        })
        .collect()
}

fn compile_spot_formula(
    normalized: &IRExpr,
    contains_past_time: bool,
) -> Option<CompiledSpotFormula> {
    if contains_past_time {
        return None;
    }
    let mut atoms = Vec::new();
    let mut next_atom = 0usize;
    let root = lower_to_temporal_formula(normalized, &mut atoms, &mut next_atom)?;
    Some(CompiledSpotFormula { root, atoms })
}

fn compile_buchi_formula(
    expanded: &IRExpr,
    _contains_past_time: bool,
) -> Option<CompiledBuchiFormula> {
    let mut atoms = Vec::new();
    let mut next_atom = 0usize;
    let root = lower_to_buchi_formula(expanded, &mut atoms, &mut next_atom)?;
    let automaton = GeneralizedBuchi::from_formula(&root, atoms.len());
    Some(CompiledBuchiFormula { automaton, atoms })
}

fn lower_to_buchi_formula(
    expr: &IRExpr,
    atoms: &mut Vec<BuchiAtomBinding>,
    next_atom: &mut usize,
) -> Option<LtlFormula> {
    if let IRExpr::Lit {
        value: LitVal::Bool { value },
        ..
    } = expr
    {
        return Some(if *value {
            LtlFormula::True
        } else {
            LtlFormula::False
        });
    }

    let lowered = match expr {
        IRExpr::Always { body, .. } => Some(LtlFormula::always(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Eventually { body, .. } => Some(LtlFormula::eventually(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Historically { body, .. } => Some(LtlFormula::historically(
            lower_to_buchi_formula(body, atoms, next_atom)?,
        )),
        IRExpr::Once { body, .. } => Some(LtlFormula::once(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Previously { body, .. } => Some(LtlFormula::previously(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Until { left, right, .. } => Some(LtlFormula::until(
            lower_to_buchi_formula(left, atoms, next_atom)?,
            lower_to_buchi_formula(right, atoms, next_atom)?,
        )),
        IRExpr::Since { left, right, .. } => Some(LtlFormula::since(
            lower_to_buchi_formula(left, atoms, next_atom)?,
            lower_to_buchi_formula(right, atoms, next_atom)?,
        )),
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => Some(LtlFormula::not(
            lower_to_buchi_formula(operand, atoms, next_atom)?,
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => Some(LtlFormula::and(
            lower_to_buchi_formula(left, atoms, next_atom)?,
            lower_to_buchi_formula(right, atoms, next_atom)?,
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpOr" => Some(LtlFormula::or(
            lower_to_buchi_formula(left, atoms, next_atom)?,
            lower_to_buchi_formula(right, atoms, next_atom)?,
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if is_implies_op(op) => Some(LtlFormula::implies(
            lower_to_buchi_formula(left, atoms, next_atom)?,
            lower_to_buchi_formula(right, atoms, next_atom)?,
        )),
        _ => None,
    };
    if lowered.is_some() {
        return lowered;
    }

    if !contains_temporal(expr) {
        return Some(LtlFormula::atom(buchi_atom_for(expr, atoms, next_atom)));
    }

    None
}

fn lower_to_temporal_formula(
    expr: &IRExpr,
    atoms: &mut Vec<SpotAtomBinding>,
    next_atom: &mut usize,
) -> Option<TemporalFormula> {
    if let IRExpr::Lit {
        value: LitVal::Bool { value },
        ..
    } = expr
    {
        return Some(if *value {
            TemporalFormula::True
        } else {
            TemporalFormula::False
        });
    }

    let lowered = match expr {
        IRExpr::Always { body, .. } => Some(TemporalFormula::Always(Box::new(
            lower_to_temporal_formula(body, atoms, next_atom)?,
        ))),
        IRExpr::Eventually { body, .. } => Some(TemporalFormula::Eventually(Box::new(
            lower_to_temporal_formula(body, atoms, next_atom)?,
        ))),
        IRExpr::Until { left, right, .. } => Some(TemporalFormula::Until(
            Box::new(lower_to_temporal_formula(left, atoms, next_atom)?),
            Box::new(lower_to_temporal_formula(right, atoms, next_atom)?),
        )),
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => Some(TemporalFormula::Not(Box::new(
            lower_to_temporal_formula(operand, atoms, next_atom)?,
        ))),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => Some(TemporalFormula::And(vec![
            lower_to_temporal_formula(left, atoms, next_atom)?,
            lower_to_temporal_formula(right, atoms, next_atom)?,
        ])),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpOr" => Some(TemporalFormula::Or(vec![
            lower_to_temporal_formula(left, atoms, next_atom)?,
            lower_to_temporal_formula(right, atoms, next_atom)?,
        ])),
        IRExpr::BinOp {
            op, left, right, ..
        } if is_implies_op(op) => Some(TemporalFormula::Implies(
            Box::new(lower_to_temporal_formula(left, atoms, next_atom)?),
            Box::new(lower_to_temporal_formula(right, atoms, next_atom)?),
        )),
        _ => None,
    };
    if lowered.is_some() {
        return lowered;
    }

    if !contains_temporal(expr) {
        return Some(TemporalFormula::Atom(spot_atom_for(expr, atoms, next_atom)));
    }

    None
}

fn buchi_atom_for(
    expr: &IRExpr,
    atoms: &mut Vec<BuchiAtomBinding>,
    next_atom: &mut usize,
) -> usize {
    if let Some(atom) = atoms.iter().position(|binding| binding.expr == *expr) {
        return atom;
    }

    let atom = *next_atom;
    *next_atom += 1;
    atoms.push(BuchiAtomBinding { expr: expr.clone() });
    atom
}

fn spot_atom_for(expr: &IRExpr, atoms: &mut Vec<SpotAtomBinding>, next_atom: &mut usize) -> String {
    if let Some(binding) = atoms.iter().find(|binding| binding.expr == *expr) {
        return binding.label.clone();
    }

    let label = format!("p{}", *next_atom);
    *next_atom += 1;
    atoms.push(SpotAtomBinding {
        label: label.clone(),
        expr: expr.clone(),
    });
    label
}

fn render_spot_formula(formula: &TemporalFormula) -> String {
    match formula {
        TemporalFormula::True => "1".to_owned(),
        TemporalFormula::False => "0".to_owned(),
        TemporalFormula::Atom(label) => label.clone(),
        TemporalFormula::Not(inner) => format!("!({})", render_spot_formula(inner)),
        TemporalFormula::And(parts) => format!(
            "({})",
            parts
                .iter()
                .map(render_spot_formula)
                .collect::<Vec<_>>()
                .join(" & ")
        ),
        TemporalFormula::Or(parts) => format!(
            "({})",
            parts
                .iter()
                .map(render_spot_formula)
                .collect::<Vec<_>>()
                .join(" | ")
        ),
        TemporalFormula::Implies(left, right) => format!(
            "({} -> {})",
            render_spot_formula(left),
            render_spot_formula(right)
        ),
        TemporalFormula::Always(inner) => format!("G({})", render_spot_formula(inner)),
        TemporalFormula::Eventually(inner) => format!("F({})", render_spot_formula(inner)),
        TemporalFormula::Until(left, right) => format!(
            "({} U {})",
            render_spot_formula(left),
            render_spot_formula(right)
        ),
    }
}

fn extract_liveness_pattern_inner(expr: &IRExpr) -> Option<PatternExtraction> {
    let pattern = extract_liveness_pattern_with_always(expr, false)?;
    let safety_conjuncts = strip_liveness_from_conjunction(expr).into_iter().collect();
    Some(PatternExtraction {
        pattern,
        safety_conjuncts,
    })
}

/// Walk an expression tree and extract the safety side of any conjunction
/// where one side is liveness and the other is safety.
///
/// Preserves surrounding structure (Always, Forall) so the result can be
/// verified as a standalone safety property.
///
/// Returns `None` if no such conjunction exists (pure liveness or no conjunction).
fn strip_liveness_from_conjunction(expr: &IRExpr) -> Option<IRExpr> {
    match expr {
        IRExpr::Always { body, span } => {
            strip_liveness_from_conjunction(body).map(|inner| IRExpr::Always {
                body: Box::new(inner),
                span: *span,
            })
        }
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => strip_liveness_from_conjunction(body).map(|inner| IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(inner),
            span: *span,
        }),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            let l = contains_liveness(left);
            let r = contains_liveness(right);
            match (l, r) {
                (true, false) => Some(*right.clone()),
                (false, true) => Some(*left.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn extract_liveness_pattern_with_always(
    expr: &IRExpr,
    inside_always: bool,
) -> Option<LivenessPattern> {
    match expr {
        IRExpr::Always { body, .. } => extract_liveness_pattern_with_always(body, true),
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let entity = match domain {
                crate::ir::types::IRType::Entity { name } => name.clone(),
                _ => return extract_liveness_pattern_with_always(body, inside_always),
            };
            match body.as_ref() {
                IRExpr::BinOp {
                    op, left, right, ..
                } if is_implies_op(op) => {
                    if let IRExpr::Eventually { body: resp, .. } = right.as_ref() {
                        if inside_always {
                            Some(LivenessPattern::QuantifiedResponse {
                                var: var.clone(),
                                entity,
                                trigger: *left.clone(),
                                response: *resp.clone(),
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                IRExpr::Eventually { body: ev_body, .. }
                    if matches!(ev_body.as_ref(), IRExpr::Always { .. }) =>
                {
                    if let IRExpr::Always { body: inner, .. } = ev_body.as_ref() {
                        Some(LivenessPattern::QuantifiedPersistence {
                            var: var.clone(),
                            entity,
                            condition: *inner.clone(),
                        })
                    } else {
                        None
                    }
                }
                IRExpr::Eventually { body: resp, .. } => {
                    if inside_always {
                        Some(LivenessPattern::QuantifiedRecurrence {
                            var: var.clone(),
                            entity,
                            response: *resp.clone(),
                        })
                    } else {
                        Some(LivenessPattern::QuantifiedEventuality {
                            var: var.clone(),
                            entity,
                            response: *resp.clone(),
                        })
                    }
                }
                _ => {
                    let inner = extract_liveness_pattern_with_always(body, inside_always)?;
                    Some(match inner {
                        LivenessPattern::Response { trigger, response } => {
                            if inside_always {
                                LivenessPattern::QuantifiedResponse {
                                    var: var.clone(),
                                    entity,
                                    trigger,
                                    response,
                                }
                            } else {
                                return None;
                            }
                        }
                        LivenessPattern::Recurrence { response } => {
                            LivenessPattern::QuantifiedRecurrence {
                                var: var.clone(),
                                entity,
                                response,
                            }
                        }
                        LivenessPattern::Eventuality { response } => {
                            LivenessPattern::QuantifiedEventuality {
                                var: var.clone(),
                                entity,
                                response,
                            }
                        }
                        LivenessPattern::Persistence { condition } => {
                            LivenessPattern::QuantifiedPersistence {
                                var: var.clone(),
                                entity,
                                condition,
                            }
                        }
                        other => other,
                    })
                }
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if is_implies_op(op) => {
            if let IRExpr::Eventually { body: resp, .. } = right.as_ref() {
                if inside_always {
                    Some(LivenessPattern::Response {
                        trigger: *left.clone(),
                        response: *resp.clone(),
                    })
                } else {
                    None
                }
            } else {
                None
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => {
            let l = contains_liveness(left);
            let r = contains_liveness(right);
            match (l, r) {
                (true, false) => extract_liveness_pattern_with_always(left, inside_always),
                (false, true) => extract_liveness_pattern_with_always(right, inside_always),
                _ => None,
            }
        }
        IRExpr::Eventually { body, .. } if matches!(body.as_ref(), IRExpr::Always { .. }) => {
            if let IRExpr::Always { body: inner, .. } = body.as_ref() {
                if let IRExpr::Forall {
                    var,
                    domain: crate::ir::types::IRType::Entity { name },
                    body: qb,
                    ..
                } = inner.as_ref()
                {
                    return Some(LivenessPattern::QuantifiedPersistence {
                        var: var.clone(),
                        entity: name.clone(),
                        condition: *qb.clone(),
                    });
                }
                Some(LivenessPattern::Persistence {
                    condition: *inner.clone(),
                })
            } else {
                None
            }
        }
        IRExpr::Eventually { body, .. } => {
            if let IRExpr::Forall {
                var,
                domain: crate::ir::types::IRType::Entity { name },
                body: qb,
                ..
            } = body.as_ref()
            {
                return if inside_always {
                    Some(LivenessPattern::QuantifiedRecurrence {
                        var: var.clone(),
                        entity: name.clone(),
                        response: *qb.clone(),
                    })
                } else {
                    Some(LivenessPattern::QuantifiedEventuality {
                        var: var.clone(),
                        entity: name.clone(),
                        response: *qb.clone(),
                    })
                };
            }
            if inside_always {
                Some(LivenessPattern::Recurrence {
                    response: *body.clone(),
                })
            } else {
                Some(LivenessPattern::Eventuality {
                    response: *body.clone(),
                })
            }
        }
        _ => None,
    }
}

fn is_implies_op(op: &str) -> bool {
    matches!(op, "OpImplies" | "implies" | "=>")
}

pub(super) fn contains_liveness(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Eventually { .. } | IRExpr::Until { .. } => true,
        IRExpr::Always { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. } => contains_liveness(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Since { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_liveness(left) || contains_liveness(right),
        IRExpr::Tuple { elements, .. } => elements.iter().any(contains_liveness),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Lam { body, .. } => contains_liveness(body),
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|pred| contains_liveness(pred)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            contains_liveness(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(contains_liveness) || contains_liveness(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => contains_liveness(map) || contains_liveness(key) || contains_liveness(value),
        IRExpr::Index { map, key, .. } => contains_liveness(map) || contains_liveness(key),
        IRExpr::SetComp {
            source,
            filter,
            projection,
            ..
        } => {
            source
                .as_ref()
                .is_some_and(|source| contains_liveness(source))
                || contains_liveness(filter)
                || projection.as_ref().is_some_and(|p| contains_liveness(p))
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            contains_liveness(projection)
                || contains_liveness(filter)
                || bindings.iter().any(|binding| {
                    binding
                        .source
                        .as_ref()
                        .is_some_and(|source| contains_liveness(source))
                })
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(contains_liveness)
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| contains_liveness(k) || contains_liveness(v)),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| contains_liveness(&b.expr)) || contains_liveness(body)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_liveness),
        IRExpr::VarDecl { init, rest, .. } => contains_liveness(init) || contains_liveness(rest),
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            contains_liveness(cond)
                || invariants.iter().any(contains_liveness)
                || contains_liveness(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            contains_liveness(cond)
                || contains_liveness(then_body)
                || else_body.as_ref().is_some_and(|e| contains_liveness(e))
        }
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, v)| contains_liveness(v)),
        IRExpr::Saw { args, .. } => args
            .iter()
            .any(|a| a.as_ref().is_some_and(|e| contains_liveness(e))),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => contains_liveness(body) || in_filter.as_ref().is_some_and(|f| contains_liveness(f)),
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {
            false
        }
    }
}

pub(super) fn contains_temporal(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Always { .. }
        | IRExpr::Eventually { .. }
        | IRExpr::Until { .. }
        | IRExpr::Historically { .. }
        | IRExpr::Once { .. }
        | IRExpr::Previously { .. }
        | IRExpr::Since { .. }
        | IRExpr::Saw { .. } => true,
        IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. } => contains_temporal(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_temporal(left) || contains_temporal(right),
        IRExpr::Tuple { elements, .. } => elements.iter().any(contains_temporal),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Lam { body, .. } => contains_temporal(body),
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|pred| contains_temporal(pred)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            contains_temporal(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(contains_temporal) || contains_temporal(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => contains_temporal(map) || contains_temporal(key) || contains_temporal(value),
        IRExpr::Index { map, key, .. } => contains_temporal(map) || contains_temporal(key),
        IRExpr::SetComp {
            source,
            filter,
            projection,
            ..
        } => {
            source
                .as_ref()
                .is_some_and(|source| contains_temporal(source))
                || contains_temporal(filter)
                || projection.as_ref().is_some_and(|p| contains_temporal(p))
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            contains_temporal(projection)
                || contains_temporal(filter)
                || bindings.iter().any(|binding| {
                    binding
                        .source
                        .as_ref()
                        .is_some_and(|source| contains_temporal(source))
                })
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(contains_temporal)
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| contains_temporal(k) || contains_temporal(v)),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| contains_temporal(&b.expr)) || contains_temporal(body)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_temporal),
        IRExpr::VarDecl { init, rest, .. } => contains_temporal(init) || contains_temporal(rest),
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            contains_temporal(cond)
                || invariants.iter().any(contains_temporal)
                || contains_temporal(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            contains_temporal(cond)
                || contains_temporal(then_body)
                || else_body.as_ref().is_some_and(|e| contains_temporal(e))
        }
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, v)| contains_temporal(v)),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => contains_temporal(body) || in_filter.as_ref().is_some_and(|f| contains_temporal(f)),
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {
            false
        }
    }
}

/// Structural scan for any integer `/` or `%` anywhere in an expression,
/// descending through temporal operators (`always`/`eventually`/`until`/…),
/// quantifiers, branches, and every other sub-expression. Used to gate the
/// div-by-zero well-definedness discharge: unlike a single-step property
/// encoding (which does not descend into temporal bodies), this never misses a
/// division hidden inside a liveness body.
pub(super) fn contains_integer_div(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            matches!(op.as_str(), "OpDiv" | "OpMod")
                || contains_integer_div(left)
                || contains_integer_div(right)
        }
        IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_integer_div(left) || contains_integer_div(right),
        IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Lam { body, .. } => contains_integer_div(body),
        IRExpr::Saw { args, .. } => args.iter().flatten().any(|a| contains_integer_div(a)),
        IRExpr::Tuple { elements, .. }
        | IRExpr::SetLit { elements, .. }
        | IRExpr::SeqLit { elements, .. } => elements.iter().any(contains_integer_div),
        IRExpr::Choose { predicate, .. } => {
            predicate.as_ref().is_some_and(|p| contains_integer_div(p))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            contains_integer_div(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(contains_integer_div)
                        || contains_integer_div(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => contains_integer_div(map) || contains_integer_div(key) || contains_integer_div(value),
        IRExpr::Index { map, key, .. } => contains_integer_div(map) || contains_integer_div(key),
        IRExpr::SetComp {
            source,
            filter,
            projection,
            ..
        } => {
            source.as_ref().is_some_and(|s| contains_integer_div(s))
                || contains_integer_div(filter)
                || projection.as_ref().is_some_and(|p| contains_integer_div(p))
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            contains_integer_div(projection)
                || contains_integer_div(filter)
                || bindings
                    .iter()
                    .any(|b| b.source.as_ref().is_some_and(|s| contains_integer_div(s)))
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| contains_integer_div(k) || contains_integer_div(v)),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| contains_integer_div(&b.expr)) || contains_integer_div(body)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_integer_div),
        IRExpr::VarDecl { init, rest, .. } => {
            contains_integer_div(init) || contains_integer_div(rest)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            contains_integer_div(cond)
                || invariants.iter().any(contains_integer_div)
                || contains_integer_div(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            contains_integer_div(cond)
                || contains_integer_div(then_body)
                || else_body.as_ref().is_some_and(|e| contains_integer_div(e))
        }
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, v)| contains_integer_div(v)),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            contains_integer_div(body)
                || in_filter.as_ref().is_some_and(|f| contains_integer_div(f))
        }
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {
            false
        }
    }
}

/// Whether any integer `/`/`%` appears in a body-level action (a command/action
/// body statement), descending through nested `choose`/`for`/`match` blocks.
fn action_contains_integer_div(action: &IRAction) -> bool {
    match action {
        IRAction::ExprStmt { expr } => contains_integer_div(expr),
        IRAction::Choose { filter, ops, .. } => {
            contains_integer_div(filter) || ops.iter().any(action_contains_integer_div)
        }
        IRAction::ForAll { ops, .. } => ops.iter().any(action_contains_integer_div),
        IRAction::Create { fields, .. } => fields.iter().any(|f| contains_integer_div(&f.value)),
        IRAction::Apply { args, .. }
        | IRAction::CrossCall { args, .. }
        | IRAction::LetCrossCall { args, .. } => args.iter().any(contains_integer_div),
        IRAction::Match { scrutinee, arms } => {
            let scrutinee_div = match scrutinee {
                IRActionMatchScrutinee::Var { .. } => false,
                IRActionMatchScrutinee::CrossCall { args, .. } => {
                    args.iter().any(contains_integer_div)
                }
            };
            scrutinee_div
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(contains_integer_div)
                        || a.body.iter().any(action_contains_integer_div)
                })
        }
    }
}

/// Whether any integer `/`/`%` appears in a transition guard or update value of
/// the given entities/systems. Used to gate the div-by-zero discharge on
/// transition-side div/mod (a division in `x' = a / b` that never appears in a
/// property).
pub(super) fn transitions_contain_integer_div(entities: &[IREntity], systems: &[IRSystem]) -> bool {
    entities.iter().any(|entity| {
        entity.transitions.iter().any(|transition| {
            contains_integer_div(&transition.guard)
                || transition
                    .updates
                    .iter()
                    .any(|update| contains_integer_div(&update.value))
        })
    }) || systems.iter().any(|system| {
        system.actions.iter().any(|action| {
            contains_integer_div(&action.guard)
                || action.body.iter().any(action_contains_integer_div)
        })
    })
}

pub(super) fn contains_past_time(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Historically { .. }
        | IRExpr::Once { .. }
        | IRExpr::Previously { .. }
        | IRExpr::Since { .. }
        | IRExpr::Saw { .. } => true,
        IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. } => contains_past_time(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_past_time(left) || contains_past_time(right),
        IRExpr::Tuple { elements, .. } => elements.iter().any(contains_past_time),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Lam { body, .. } => contains_past_time(body),
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|pred| contains_past_time(pred)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            contains_past_time(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(contains_past_time) || contains_past_time(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => contains_past_time(map) || contains_past_time(key) || contains_past_time(value),
        IRExpr::Index { map, key, .. } => contains_past_time(map) || contains_past_time(key),
        IRExpr::SetComp {
            source,
            filter,
            projection,
            ..
        } => {
            source
                .as_ref()
                .is_some_and(|source| contains_past_time(source))
                || contains_past_time(filter)
                || projection.as_ref().is_some_and(|p| contains_past_time(p))
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            contains_past_time(projection)
                || contains_past_time(filter)
                || bindings.iter().any(|binding| {
                    binding
                        .source
                        .as_ref()
                        .is_some_and(|source| contains_past_time(source))
                })
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(contains_past_time)
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| contains_past_time(k) || contains_past_time(v)),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| contains_past_time(&b.expr)) || contains_past_time(body)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_past_time),
        IRExpr::VarDecl { init, rest, .. } => contains_past_time(init) || contains_past_time(rest),
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            contains_past_time(cond)
                || invariants.iter().any(contains_past_time)
                || contains_past_time(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            contains_past_time(cond)
                || contains_past_time(then_body)
                || else_body.as_ref().is_some_and(|e| contains_past_time(e))
        }
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, v)| contains_past_time(v)),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => contains_past_time(body) || in_filter.as_ref().is_some_and(|f| contains_past_time(f)),
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{IRAssumptionSet, IRProgram, IRType, IRVerify};

    fn bool_var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Bool,
            span: None,
        }
    }

    /// A liveness formula with more than 128 distinct subformulas exceeds the
    /// u128 Büchi state width, so construction caps to an empty automaton. The
    /// lasso encoder must treat that empty automaton as a construction failure
    /// (Unprovable), not as "no counterexample found" (a vacuous CHECKED).
    #[test]
    fn oversized_temporal_formula_caps_to_empty_buchi() {
        use crate::ir::types::LitVal;
        let atom = |i: i64| IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: i },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };
        // `eventually (x == 0 and x == 1 and ... and x == 129)` — 130 distinct
        // atoms, so the closure is well over 128.
        let mut conj = atom(0);
        for i in 1..130 {
            conj = IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(atom(i)),
                right: Box::new(conj),
                ty: IRType::Bool,
                span: None,
            };
        }
        let formula = IRExpr::Eventually {
            body: Box::new(conj),
            span: None,
        };
        let compiled = CompiledTemporalFormula::from_expanded(formula);
        let buchi = compiled
            .buchi()
            .expect("a liveness formula compiles to a Büchi automaton");
        assert_eq!(
            buchi.automaton().state_count(),
            0,
            "oversized temporal formula must cap to an empty automaton"
        );
    }

    /// `P until Q` must preserve true LTL until, not be rewritten into the
    /// non-equivalent `eventually Q and always(not Q implies P)`. Concrete
    /// counterexample distinguishing the two: a run where P holds at step 0,
    /// Q first holds at step 1, then both stay false forever.
    ///
    /// * true until `P U Q`: satisfied (Q occurs at step 1; P held at every
    ///   step strictly before, i.e. step 0).
    /// * naive desugaring `F Q & G(¬Q ⇒ P)`: violated, because after Q at
    ///   step 1 the run reaches a state with ¬Q and ¬P, so `G(¬Q ⇒ P)` fails.
    ///
    /// The native LTL→Büchi automaton must accept this run while the naive
    /// desugaring's automaton rejects it.
    #[test]
    fn surface_until_buchi_distinguishes_from_naive_desugaring() {
        use super::super::ltl::LassoWord;

        // atom 0 = P, atom 1 = Q
        let until = LtlFormula::until(LtlFormula::atom(0), LtlFormula::atom(1));
        // F Q & G(¬Q ⇒ P) ≡ F Q & G(Q ∨ P)
        let naive = LtlFormula::and(
            LtlFormula::eventually(LtlFormula::atom(1)),
            LtlFormula::always(LtlFormula::or(LtlFormula::atom(1), LtlFormula::atom(0))),
        );

        let until_buchi = GeneralizedBuchi::from_formula(&until, 2);
        let naive_buchi = GeneralizedBuchi::from_formula(&naive, 2);

        // Run: {P} · {Q} · ({} )^ω  — P at step 0, Q at step 1, then neither.
        let word = LassoWord::new(vec![vec![0], vec![1]], vec![vec![]]);

        assert!(
            until_buchi.accepts_lasso(&word),
            "true `P until Q` must accept the run where P holds until Q first occurs"
        );
        assert!(
            !naive_buchi.accepts_lasso(&word),
            "the naive desugaring rejects this run, proving it is not equivalent to until"
        );
    }

    /// The Spot export of `P until Q` must render Spot's native `U` operator,
    /// not the unsound `F`/`G` desugaring.
    #[test]
    fn compiled_until_renders_native_spot_until() {
        let until = IRExpr::Until {
            left: Box::new(bool_var("p")),
            right: Box::new(bool_var("q")),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(until);
        assert!(compiled.contains_liveness());
        let spot = compiled
            .spot()
            .expect("until should compile to a Spot formula");
        let rendered = spot.to_spot_input();
        assert!(
            rendered.contains(" U "),
            "until must render Spot's native U operator, got `{rendered}`"
        );
    }

    /// `P until Q` is not a flat liveness pattern (eventuality/recurrence/
    /// persistence/response). The earlier desugaring turned it into
    /// `F Q & G(…)` and pattern extraction then picked off the `F Q` part,
    /// silently dropping the P-until-Q safety obligation. With true until
    /// preserved, extraction must yield nothing so the verdict falls back to
    /// the native Büchi until rather than a weaker reduced obligation.
    #[test]
    fn compiled_until_does_not_misextract_liveness_pattern() {
        let until = IRExpr::Until {
            left: Box::new(bool_var("p")),
            right: Box::new(bool_var("q")),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(until);
        assert!(
            compiled.extraction().is_none(),
            "until must not be reduced to a flat liveness pattern"
        );
    }

    #[test]
    fn compiled_temporal_formula_builds_buchi_for_full_future_ltl() {
        let expr = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(bool_var("p")),
                right: Box::new(IRExpr::Until {
                    left: Box::new(bool_var("q")),
                    right: Box::new(IRExpr::Eventually {
                        body: Box::new(bool_var("r")),
                        span: None,
                    }),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(expr);
        let buchi = compiled.buchi().expect("future LTL compiles to Buchi");

        assert_eq!(buchi.atoms(), 3);
        assert!(buchi.state_count() > 0);
        assert!(buchi.acceptance_set_count() > 0);
    }

    #[test]
    fn compiled_temporal_formula_builds_buchi_for_past_time_ltl() {
        let compiled = CompiledTemporalFormula::from_expanded(IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(IRExpr::Previously {
                    body: Box::new(bool_var("p")),
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::Once {
                        body: Box::new(bool_var("q")),
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::Historically {
                            body: Box::new(bool_var("r")),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Since {
                            left: Box::new(bool_var("s")),
                            right: Box::new(bool_var("t")),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        });

        assert!(compiled.contains_past_time());
        let buchi = compiled.buchi().expect("past-time LTL compiles to Buchi");
        assert_eq!(buchi.atoms(), 5);
        assert!(buchi.state_count() > 0);
    }

    #[test]
    fn compiled_temporal_formula_extracts_response_pattern() {
        let expr = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(bool_var("p")),
                right: Box::new(IRExpr::Eventually {
                    body: Box::new(bool_var("q")),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(expr);

        let Some(extraction) = compiled.extraction() else {
            panic!("expected liveness pattern extraction");
        };
        assert!(extraction.safety_conjuncts.is_empty());
        match &extraction.pattern {
            LivenessPattern::Response { trigger, response } => {
                assert!(matches!(trigger, IRExpr::Var { name, .. } if name == "p"));
                assert!(matches!(response, IRExpr::Var { name, .. } if name == "q"));
            }
            _ => panic!("expected response pattern"),
        }
    }

    #[test]
    fn compiled_temporal_formula_extracts_response_pattern_from_textual_implies() {
        let expr = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "implies".to_owned(),
                left: Box::new(bool_var("p")),
                right: Box::new(IRExpr::Eventually {
                    body: Box::new(bool_var("q")),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(expr);

        let Some(extraction) = compiled.extraction() else {
            panic!("expected liveness pattern extraction");
        };
        match &extraction.pattern {
            LivenessPattern::Response { trigger, response } => {
                assert!(matches!(trigger, IRExpr::Var { name, .. } if name == "p"));
                assert!(matches!(response, IRExpr::Var { name, .. } if name == "q"));
            }
            _ => panic!("expected response pattern"),
        }
    }

    #[test]
    fn compiled_temporal_formula_extracts_all_liveness_pattern_shapes() {
        let recurrence = CompiledTemporalFormula::from_expanded(IRExpr::Always {
            body: Box::new(IRExpr::Eventually {
                body: Box::new(bool_var("p")),
                span: None,
            }),
            span: None,
        });
        assert!(matches!(
            recurrence.extraction().map(|e| &e.pattern),
            Some(LivenessPattern::Recurrence { .. })
        ));

        let eventuality = CompiledTemporalFormula::from_expanded(IRExpr::Eventually {
            body: Box::new(bool_var("p")),
            span: None,
        });
        assert!(matches!(
            eventuality.extraction().map(|e| &e.pattern),
            Some(LivenessPattern::Eventuality { .. })
        ));
        assert!(eventuality
            .extraction()
            .expect("eventuality")
            .pattern
            .is_oneshot());

        let persistence = CompiledTemporalFormula::from_expanded(IRExpr::Eventually {
            body: Box::new(IRExpr::Always {
                body: Box::new(bool_var("stable")),
                span: None,
            }),
            span: None,
        });
        assert!(matches!(
            persistence.extraction().map(|e| &e.pattern),
            Some(LivenessPattern::Persistence { .. })
        ));

        let quantified = CompiledTemporalFormula::from_expanded(IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Eventually {
                    body: Box::new(bool_var("done")),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        });
        let pattern = &quantified.extraction().expect("quantified").pattern;
        assert!(matches!(
            pattern,
            LivenessPattern::QuantifiedRecurrence { .. }
        ));
        assert_eq!(pattern.quantified_binding(), (Some("o"), Some("Order")));
    }

    #[test]
    fn compiled_temporal_formula_preserves_safety_conjunct_and_spot_export() {
        let expr = IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(bool_var("safe")),
                right: Box::new(IRExpr::Eventually {
                    body: Box::new(bool_var("done")),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(expr);
        let extraction = compiled.extraction().expect("extraction");

        assert_eq!(extraction.safety_conjuncts.len(), 1);
        assert!(matches!(
            extraction.safety_conjuncts[0],
            IRExpr::Always { .. }
        ));
        let spot = compiled.spot().expect("spot formula");
        assert_eq!(spot.atoms(), 2);
        assert_eq!(spot.to_spot_input(), "G((p0 & F(p1)))");
        assert_eq!(spot.export().spot_formula, "G((p0 & F(p1)))");
        let buchi = compiled.buchi().expect("buchi formula");
        let exported = buchi.export();
        assert_eq!(exported.format, "hoa");
        assert_eq!(exported.version, "v1");
        assert_eq!(exported.automaton_kind, "generalized-buchi");
        assert_eq!(exported.acceptance, "state");
        assert_eq!(exported.atoms.len(), 2);
        assert!(exported.hoa.starts_with("HOA: v1\n"));
        assert!(exported.hoa.contains("AP: 2 \"p0\" \"p1\"\n"));
    }

    #[test]
    fn temporal_export_marks_past_time_without_spot_formula() {
        let verify = IRVerify {
            name: "history".to_owned(),
            depth: None,
            systems: vec![],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts: vec![IRExpr::Since {
                left: Box::new(bool_var("p")),
                right: Box::new(bool_var("q")),
                span: None,
            }],
            span: None,
            file: None,
        };
        let defs = defenv::DefEnv::from_ir(&IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        });

        let exports = export_verify_temporal_formulas(&verify, &defs);

        assert_eq!(exports.len(), 1);
        assert!(exports[0].contains_temporal);
        assert!(!exports[0].contains_liveness);
        assert!(exports[0].contains_past_time);
        assert!(exports[0].spot.is_none());
        assert!(exports[0].buchi.is_some());
    }
}
