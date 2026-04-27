//! Temporal formula normalization and compiled temporal summaries.

use serde::Serialize;

use crate::ir::types::{IRExpr, IRVerify};

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
    normalized: IRExpr,
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
        let normalized = desugar_until(&expanded);
        let contains_liveness = contains_liveness(&expanded);
        let contains_temporal = contains_temporal(&expanded);
        let contains_past_time = contains_past_time(&expanded);
        let extraction = extract_liveness_pattern_inner(&normalized);
        let spot = compile_spot_formula(&normalized, contains_past_time);
        let buchi = compile_buchi_formula(&expanded, contains_past_time);
        Self {
            expanded,
            normalized,
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

    pub fn normalized(&self) -> &IRExpr {
        &self.normalized
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
    Atom(String),
    Not(Box<TemporalFormula>),
    And(Vec<TemporalFormula>),
    Or(Vec<TemporalFormula>),
    Implies(Box<TemporalFormula>, Box<TemporalFormula>),
    Always(Box<TemporalFormula>),
    Eventually(Box<TemporalFormula>),
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
    contains_past_time: bool,
) -> Option<CompiledBuchiFormula> {
    if contains_past_time {
        return None;
    }

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
    if !contains_temporal(expr) {
        let atom = *next_atom;
        *next_atom += 1;
        atoms.push(BuchiAtomBinding { expr: expr.clone() });
        return Some(LtlFormula::atom(atom));
    }

    match expr {
        IRExpr::Always { body, .. } => Some(LtlFormula::always(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Eventually { body, .. } => Some(LtlFormula::eventually(lower_to_buchi_formula(
            body, atoms, next_atom,
        )?)),
        IRExpr::Until { left, right, .. } => Some(LtlFormula::until(
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
    }
}

fn lower_to_temporal_formula(
    expr: &IRExpr,
    atoms: &mut Vec<SpotAtomBinding>,
    next_atom: &mut usize,
) -> Option<TemporalFormula> {
    if !contains_temporal(expr) {
        let label = format!("p{}", *next_atom);
        *next_atom += 1;
        atoms.push(SpotAtomBinding {
            label: label.clone(),
            expr: expr.clone(),
        });
        return Some(TemporalFormula::Atom(label));
    }

    match expr {
        IRExpr::Always { body, .. } => Some(TemporalFormula::Always(Box::new(
            lower_to_temporal_formula(body, atoms, next_atom)?,
        ))),
        IRExpr::Eventually { body, .. } => Some(TemporalFormula::Eventually(Box::new(
            lower_to_temporal_formula(body, atoms, next_atom)?,
        ))),
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
    }
}

fn render_spot_formula(formula: &TemporalFormula) -> String {
    match formula {
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

#[allow(clippy::match_same_arms)]
pub(super) fn desugar_until(expr: &IRExpr) -> IRExpr {
    match expr {
        IRExpr::Until { left, right, .. } => {
            let p = desugar_until(left);
            let q = desugar_until(right);
            let eventually_q = IRExpr::Eventually {
                body: Box::new(q.clone()),
                span: None,
            };
            let not_q = IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(q),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            };
            let not_q_implies_p = IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(not_q),
                right: Box::new(p),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            };
            let always_guard = IRExpr::Always {
                body: Box::new(not_q_implies_p),
                span: None,
            };
            IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(eventually_q),
                right: Box::new(always_guard),
                ty: crate::ir::types::IRType::Bool,
                span: None,
            }
        }
        IRExpr::Always { body, span } => IRExpr::Always {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Eventually { body, span } => IRExpr::Eventually {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Historically { body, span } => IRExpr::Historically {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Once { body, span } => IRExpr::Once {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Previously { body, span } => IRExpr::Previously {
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Since { left, right, span } => IRExpr::Since {
            left: Box::new(desugar_until(left)),
            right: Box::new(desugar_until(right)),
            span: *span,
        },
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Exists {
            var,
            domain,
            body,
            span,
        } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::One {
            var,
            domain,
            body,
            span,
        } => IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::Lone {
            var,
            domain,
            body,
            span,
        } => IRExpr::Lone {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(desugar_until(body)),
            span: *span,
        },
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(desugar_until(left)),
            right: Box::new(desugar_until(right)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::UnOp {
            op,
            operand,
            ty,
            span,
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(desugar_until(operand)),
            ty: ty.clone(),
            span: *span,
        },
        _ => expr.clone(),
    }
}

pub(super) fn contains_liveness(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Eventually { .. } | IRExpr::Until { .. } => true,
        IRExpr::Previously { .. } | IRExpr::Since { .. } => true,
        IRExpr::Always { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::UnOp { operand: body, .. }
        | IRExpr::Field { expr: body, .. }
        | IRExpr::Prime { expr: body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::Assert { expr: body, .. }
        | IRExpr::Assume { expr: body, .. } => contains_liveness(body),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => contains_liveness(left) || contains_liveness(right),
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
            filter, projection, ..
        } => contains_liveness(filter) || projection.as_ref().is_some_and(|p| contains_liveness(p)),
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
            filter, projection, ..
        } => contains_temporal(filter) || projection.as_ref().is_some_and(|p| contains_temporal(p)),
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
            filter, projection, ..
        } => {
            contains_past_time(filter) || projection.as_ref().is_some_and(|p| contains_past_time(p))
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

    #[test]
    fn compiled_temporal_formula_desugars_until() {
        let until = IRExpr::Until {
            left: Box::new(bool_var("p")),
            right: Box::new(bool_var("q")),
            span: None,
        };

        let compiled = CompiledTemporalFormula::from_expanded(until);

        assert!(compiled.contains_liveness());
        match compiled.normalized() {
            IRExpr::BinOp { op, .. } => assert_eq!(op, "OpAnd"),
            other => panic!("expected desugared conjunction, got {other:?}"),
        }
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
    fn compiled_temporal_formula_rejects_past_time_buchi() {
        let compiled = CompiledTemporalFormula::from_expanded(IRExpr::Since {
            left: Box::new(bool_var("p")),
            right: Box::new(bool_var("q")),
            span: None,
        });

        assert!(compiled.contains_past_time());
        assert!(compiled.buchi().is_none());
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
    }

    #[test]
    fn temporal_export_marks_past_time_without_spot_formula() {
        let verify = IRVerify {
            name: "history".to_owned(),
            depth: None,
            systems: vec![],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Since {
                left: Box::new(bool_var("p")),
                right: Box::new(bool_var("q")),
                span: None,
            }],
            span: None,
            file: None,
        };
        let defs = defenv::DefEnv::from_ir(&IRProgram {
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
        assert!(exports[0].contains_liveness);
        assert!(exports[0].contains_past_time);
        assert!(exports[0].spot.is_none());
    }
}
