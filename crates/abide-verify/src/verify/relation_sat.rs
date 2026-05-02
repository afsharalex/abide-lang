//! Finite bounded-relation SAT encoding.
//!
//! This is the Kodkod-like core used by the relational backend: given finite
//! atom domains and fixed relation symbols, it encodes relation algebra over
//! tuple membership literals.

use std::collections::{HashMap, HashSet};

use rustsat::instances::SatInstance;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::constraints::CardConstraint;
use rustsat::types::Lit;
use rustsat_batsat::BasicSolver;

use abide_witness::{rel, WitnessValue};

use crate::ir::relation::{
    IRRelationColumn, IRRelationExpr, IRRelationSymbol, IRRelationType, IRRelationTypeError,
};
use crate::ir::types::{IRExpr, IRType, LitVal};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RelationAtom(String);

impl RelationAtom {
    fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }
}

type RelationTuple = Vec<RelationAtom>;

#[derive(Debug, Clone)]
struct RelationSymbolInstance {
    relation_type: IRRelationType,
    members: HashSet<RelationTuple>,
}

#[derive(Debug, Default, Clone)]
struct RelationUniverse {
    domains: HashMap<String, Vec<RelationAtom>>,
}

impl RelationUniverse {
    fn add_domain(&mut self, ty: IRType, atoms: impl IntoIterator<Item = impl Into<String>>) {
        self.domains.insert(
            type_key(&ty),
            atoms.into_iter().map(RelationAtom::new).collect(),
        );
    }

    fn domain_for(&self, ty: &IRType) -> Result<&[RelationAtom], RelationSatError> {
        self.domains
            .get(&type_key(ty))
            .map(Vec::as_slice)
            .ok_or_else(|| RelationSatError::MissingFiniteDomain { ty: ty.clone() })
    }

    fn tuples_for_type(
        &self,
        relation_type: &IRRelationType,
    ) -> Result<Vec<RelationTuple>, RelationSatError> {
        let mut out = Vec::new();
        let mut current = Vec::with_capacity(relation_type.arity());
        self.collect_tuples(relation_type, 0, &mut current, &mut out)?;
        Ok(out)
    }

    fn collect_tuples(
        &self,
        relation_type: &IRRelationType,
        column: usize,
        current: &mut RelationTuple,
        out: &mut Vec<RelationTuple>,
    ) -> Result<(), RelationSatError> {
        if column == relation_type.arity() {
            out.push(current.clone());
            return Ok(());
        }
        for atom in self.domain_for(&relation_type.columns[column].ty)? {
            current.push(atom.clone());
            self.collect_tuples(relation_type, column + 1, current, out)?;
            current.pop();
        }
        Ok(())
    }
}

#[derive(Debug)]
struct RelationSatEncoder {
    sat: SatInstance,
    universe: RelationUniverse,
    symbols: HashMap<String, RelationSymbolInstance>,
    state_symbols: HashMap<(usize, String), RelationSymbolInstance>,
}

impl RelationSatEncoder {
    fn new(universe: RelationUniverse) -> Self {
        Self {
            sat: SatInstance::new(),
            universe,
            symbols: HashMap::new(),
            state_symbols: HashMap::new(),
        }
    }

    fn define_symbol(
        &mut self,
        symbol: IRRelationSymbol,
        tuples: impl IntoIterator<Item = RelationTuple>,
    ) {
        self.symbols.insert(
            symbol.name,
            RelationSymbolInstance {
                relation_type: symbol.relation_type,
                members: tuples.into_iter().collect(),
            },
        );
    }

    fn define_symbol_at_state(
        &mut self,
        state: usize,
        symbol: IRRelationSymbol,
        tuples: impl IntoIterator<Item = RelationTuple>,
    ) {
        self.state_symbols.insert(
            (state, symbol.name),
            RelationSymbolInstance {
                relation_type: symbol.relation_type,
                members: tuples.into_iter().collect(),
            },
        );
    }

    fn require_member(
        &mut self,
        expr: &IRRelationExpr,
        tuple: RelationTuple,
    ) -> Result<(), RelationSatError> {
        let lit = self.encode_member(expr, &tuple)?;
        self.sat.add_unit(lit);
        Ok(())
    }

    fn require_not_member(
        &mut self,
        expr: &IRRelationExpr,
        tuple: RelationTuple,
    ) -> Result<(), RelationSatError> {
        let lit = self.encode_member(expr, &tuple)?;
        self.sat.add_unit(!lit);
        Ok(())
    }

    fn require_member_at_state(
        &mut self,
        state: usize,
        expr: &IRRelationExpr,
        tuple: RelationTuple,
    ) -> Result<(), RelationSatError> {
        let lit = self.encode_member_at_state(expr, &tuple, state)?;
        self.sat.add_unit(lit);
        Ok(())
    }

    fn require_not_member_at_state(
        &mut self,
        state: usize,
        expr: &IRRelationExpr,
        tuple: RelationTuple,
    ) -> Result<(), RelationSatError> {
        let lit = self.encode_member_at_state(expr, &tuple, state)?;
        self.sat.add_unit(!lit);
        Ok(())
    }

    fn require_frame_between(
        &mut self,
        symbol: &IRRelationSymbol,
        from_state: usize,
        to_state: usize,
    ) -> Result<(), RelationSatError> {
        let relation_type = symbol.relation_type.clone();
        for tuple in self.universe.tuples_for_type(&relation_type)? {
            let before = self.encode_symbol_member(symbol, &tuple, Some(from_state))?;
            let after = self.encode_symbol_member(symbol, &tuple, Some(to_state))?;
            self.sat.add_binary(!before, after);
            self.sat.add_binary(!after, before);
        }
        Ok(())
    }

    fn relation_tuples_at_state(
        &self,
        symbol_name: &str,
        state: usize,
    ) -> Result<Vec<RelationTuple>, RelationSatError> {
        self.state_symbols
            .get(&(state, symbol_name.to_owned()))
            .map(|instance| instance.members.iter().cloned().collect())
            .ok_or_else(|| RelationSatError::UnknownStateSymbol {
                name: symbol_name.to_owned(),
                state,
            })
    }

    fn require_subset(
        &mut self,
        left: &IRRelationExpr,
        right: &IRRelationExpr,
    ) -> Result<(), RelationSatError> {
        let left_ty = left.relation_type()?;
        let right_ty = right.relation_type()?;
        if left_ty != right_ty {
            return Err(RelationSatError::Type(
                IRRelationTypeError::MismatchedRelationTypes {
                    left: left_ty,
                    right: right_ty,
                },
            ));
        }
        for tuple in self.universe.tuples_for_type(&left_ty)? {
            let left_member = self.encode_member(left, &tuple)?;
            let right_member = self.encode_member(right, &tuple)?;
            self.sat.add_binary(!left_member, right_member);
        }
        Ok(())
    }

    fn require_equal(
        &mut self,
        left: &IRRelationExpr,
        right: &IRRelationExpr,
    ) -> Result<(), RelationSatError> {
        self.require_subset(left, right)?;
        self.require_subset(right, left)
    }

    fn require_cardinality_eq(
        &mut self,
        expr: &IRRelationExpr,
        expected: usize,
    ) -> Result<(), RelationSatError> {
        let lits = self.membership_lits(expr)?;
        self.sat
            .add_card_constr(CardConstraint::new_eq(lits, expected));
        Ok(())
    }

    fn membership_lits(&mut self, expr: &IRRelationExpr) -> Result<Vec<Lit>, RelationSatError> {
        let ty = expr.relation_type()?;
        let tuples = self.universe.tuples_for_type(&ty)?;
        tuples
            .iter()
            .map(|tuple| self.encode_member(expr, tuple))
            .collect()
    }

    fn encode_member(
        &mut self,
        expr: &IRRelationExpr,
        tuple: &[RelationAtom],
    ) -> Result<Lit, RelationSatError> {
        self.encode_member_with_state(expr, tuple, None)
    }

    fn encode_member_at_state(
        &mut self,
        expr: &IRRelationExpr,
        tuple: &[RelationAtom],
        state: usize,
    ) -> Result<Lit, RelationSatError> {
        self.encode_member_with_state(expr, tuple, Some(state))
    }

    fn encode_member_with_state(
        &mut self,
        expr: &IRRelationExpr,
        tuple: &[RelationAtom],
        state: Option<usize>,
    ) -> Result<Lit, RelationSatError> {
        let relation_type = expr.relation_type()?;
        if tuple.len() != relation_type.arity() {
            return Err(RelationSatError::TupleArityMismatch {
                expected: relation_type.arity(),
                found: tuple.len(),
            });
        }

        match expr {
            IRRelationExpr::Symbol(symbol) => self.encode_symbol_member(symbol, tuple, state),
            IRRelationExpr::Empty(_) => Ok(self.const_lit(false)),
            IRRelationExpr::SingletonTuple { values, .. } => Ok(self.const_lit(
                values.len() == tuple.len()
                    && values
                        .iter()
                        .zip(tuple.iter())
                        .all(|(expected, actual)| expected == &actual.0),
            )),
            IRRelationExpr::Union(left, right) => {
                let left_lit = self.encode_member_with_state(left, tuple, state)?;
                let right_lit = self.encode_member_with_state(right, tuple, state)?;
                Ok(self.or_lit(&[left_lit, right_lit]))
            }
            IRRelationExpr::Intersection(left, right) => {
                let left_lit = self.encode_member_with_state(left, tuple, state)?;
                let right_lit = self.encode_member_with_state(right, tuple, state)?;
                Ok(self.and_lit(&[left_lit, right_lit]))
            }
            IRRelationExpr::Difference(left, right) => {
                let left_lit = self.encode_member_with_state(left, tuple, state)?;
                let right_lit = self.encode_member_with_state(right, tuple, state)?;
                Ok(self.and_lit(&[left_lit, !right_lit]))
            }
            IRRelationExpr::Product(left, right) => {
                let left_ty = left.relation_type()?;
                let split = left_ty.arity();
                let left_lit = self.encode_member_with_state(left, &tuple[..split], state)?;
                let right_lit = self.encode_member_with_state(right, &tuple[split..], state)?;
                Ok(self.and_lit(&[left_lit, right_lit]))
            }
            IRRelationExpr::Join(left, right) => self.encode_join_member(left, right, tuple, state),
            IRRelationExpr::Project { expr, columns } => {
                self.encode_projection_member(expr, columns, tuple, state)
            }
            IRRelationExpr::Transpose(inner) => {
                let swapped = vec![tuple[1].clone(), tuple[0].clone()];
                self.encode_member_with_state(inner, &swapped, state)
            }
            IRRelationExpr::TransitiveClosure(inner) => {
                self.encode_closure_member(inner, tuple, false, state)
            }
            IRRelationExpr::ReflexiveTransitiveClosure(inner) => {
                self.encode_closure_member(inner, tuple, true, state)
            }
        }
    }

    fn encode_symbol_member(
        &mut self,
        symbol: &IRRelationSymbol,
        tuple: &[RelationAtom],
        state: Option<usize>,
    ) -> Result<Lit, RelationSatError> {
        let instance = self.symbol_instance(symbol, state)?;
        Ok(self.const_lit(instance.members.contains(tuple)))
    }

    fn symbol_instance(
        &self,
        symbol: &IRRelationSymbol,
        state: Option<usize>,
    ) -> Result<RelationSymbolInstance, RelationSatError> {
        let instance = if let Some(state) = state.filter(|_| symbol.mutable) {
            self.state_symbols
                .get(&(state, symbol.name.clone()))
                .ok_or_else(|| RelationSatError::UnknownStateSymbol {
                    name: symbol.name.clone(),
                    state,
                })?
        } else {
            self.symbols
                .get(&symbol.name)
                .ok_or_else(|| RelationSatError::UnknownSymbol {
                    name: symbol.name.clone(),
                })?
        };
        if instance.relation_type != symbol.relation_type {
            return Err(RelationSatError::SymbolTypeChanged {
                name: symbol.name.clone(),
            });
        }
        Ok(instance.clone())
    }

    fn encode_join_member(
        &mut self,
        left: &IRRelationExpr,
        right: &IRRelationExpr,
        tuple: &[RelationAtom],
        state: Option<usize>,
    ) -> Result<Lit, RelationSatError> {
        let left_ty = left.relation_type()?;
        let right_ty = right.relation_type()?;
        let left_prefix_len = left_ty.arity() - 1;
        let right_suffix_len = right_ty.arity() - 1;
        if tuple.len() != left_prefix_len + right_suffix_len {
            return Err(RelationSatError::TupleArityMismatch {
                expected: left_prefix_len + right_suffix_len,
                found: tuple.len(),
            });
        }

        let join_ty = &left_ty.columns[left_prefix_len].ty;
        let mut reasons = Vec::new();
        for middle in self.universe.domain_for(join_ty)?.to_vec() {
            let mut left_tuple = tuple[..left_prefix_len].to_vec();
            left_tuple.push(middle.clone());
            let mut right_tuple = Vec::with_capacity(right_ty.arity());
            right_tuple.push(middle);
            right_tuple.extend(tuple[left_prefix_len..].iter().cloned());

            let left_lit = self.encode_member_with_state(left, &left_tuple, state)?;
            let right_lit = self.encode_member_with_state(right, &right_tuple, state)?;
            reasons.push(self.and_lit(&[left_lit, right_lit]));
        }
        Ok(self.or_lit(&reasons))
    }

    fn encode_closure_member(
        &mut self,
        expr: &IRRelationExpr,
        tuple: &[RelationAtom],
        reflexive: bool,
        state: Option<usize>,
    ) -> Result<Lit, RelationSatError> {
        let source_ty = expr.relation_type()?;
        if source_ty.arity() != 2 {
            return Err(RelationSatError::Type(
                IRRelationTypeError::RequiresBinaryRelation {
                    found: source_ty.arity(),
                },
            ));
        }
        if source_ty.columns[0].ty != source_ty.columns[1].ty {
            return Err(RelationSatError::Type(
                IRRelationTypeError::ClosureTypeMismatch {
                    left: source_ty.columns[0].ty.clone(),
                    right: source_ty.columns[1].ty.clone(),
                },
            ));
        }
        if tuple.len() != 2 {
            return Err(RelationSatError::TupleArityMismatch {
                expected: 2,
                found: tuple.len(),
            });
        }

        let domain = self.universe.domain_for(&source_ty.columns[0].ty)?.to_vec();
        let Some(source_idx) = domain.iter().position(|atom| atom == &tuple[0]) else {
            return Ok(self.const_lit(false));
        };
        let Some(target_idx) = domain.iter().position(|atom| atom == &tuple[1]) else {
            return Ok(self.const_lit(false));
        };

        let mut reach = Vec::with_capacity(domain.len());
        for from in &domain {
            let mut row = Vec::with_capacity(domain.len());
            for to in &domain {
                row.push(self.encode_member_with_state(
                    expr,
                    &[from.clone(), to.clone()],
                    state,
                )?);
            }
            reach.push(row);
        }

        for via in 0..domain.len() {
            let previous = reach.clone();
            for from in 0..domain.len() {
                for to in 0..domain.len() {
                    let through_via = self.and_lit(&[previous[from][via], previous[via][to]]);
                    reach[from][to] = self.or_lit(&[previous[from][to], through_via]);
                }
            }
        }

        let transitive = reach[source_idx][target_idx];
        if reflexive && source_idx == target_idx {
            let identity = self.const_lit(true);
            Ok(self.or_lit(&[identity, transitive]))
        } else {
            Ok(transitive)
        }
    }

    fn encode_projection_member(
        &mut self,
        expr: &IRRelationExpr,
        columns: &[usize],
        tuple: &[RelationAtom],
        state: Option<usize>,
    ) -> Result<Lit, RelationSatError> {
        if tuple.len() != columns.len() {
            return Err(RelationSatError::TupleArityMismatch {
                expected: columns.len(),
                found: tuple.len(),
            });
        }
        let source_ty = expr.relation_type()?;
        let source_tuples = self.universe.tuples_for_type(&source_ty)?;
        let mut reasons = Vec::new();
        for source_tuple in source_tuples {
            if columns
                .iter()
                .enumerate()
                .all(|(out_idx, source_idx)| source_tuple[*source_idx] == tuple[out_idx])
            {
                reasons.push(self.encode_member_with_state(expr, &source_tuple, state)?);
            }
        }
        Ok(self.or_lit(&reasons))
    }

    fn const_lit(&mut self, value: bool) -> Lit {
        let lit = self.sat.new_lit();
        self.sat.add_unit(if value { lit } else { !lit });
        lit
    }

    fn and_lit(&mut self, lits: &[Lit]) -> Lit {
        if lits.is_empty() {
            return self.const_lit(true);
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let out = self.sat.new_lit();
        for &lit in lits {
            self.sat.add_binary(!out, lit);
        }
        let mut clause = vec![out];
        clause.extend(lits.iter().map(|lit| !*lit));
        self.sat.add_clause(clause.as_slice().into());
        out
    }

    fn or_lit(&mut self, lits: &[Lit]) -> Lit {
        if lits.is_empty() {
            return self.const_lit(false);
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let out = self.sat.new_lit();
        for &lit in lits {
            self.sat.add_binary(!lit, out);
        }
        let mut clause = vec![!out];
        clause.extend(lits.iter().copied());
        self.sat.add_clause(clause.as_slice().into());
        out
    }
}

#[derive(Debug, PartialEq)]
enum RelationSatError {
    Type(IRRelationTypeError),
    MissingFiniteDomain { ty: IRType },
    UnknownSymbol { name: String },
    UnknownStateSymbol { name: String, state: usize },
    SymbolTypeChanged { name: String },
    TupleArityMismatch { expected: usize, found: usize },
}

impl From<IRRelationTypeError> for RelationSatError {
    fn from(value: IRRelationTypeError) -> Self {
        Self::Type(value)
    }
}

fn type_key(ty: &IRType) -> String {
    format!("{ty:?}")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum StaticRelationOutcome {
    Checked,
    Counterexample {
        witness: Option<rel::RelationalWitness>,
        witness_error: Option<String>,
    },
}

pub(super) fn try_check_static_relation_assertions(
    assertions: &[IRExpr],
) -> Option<Result<StaticRelationOutcome, String>> {
    if assertions.is_empty() || !assertions.iter().any(contains_relation_surface) {
        return None;
    }
    Some(check_static_relation_assertions(assertions))
}

fn check_static_relation_assertions(
    assertions: &[IRExpr],
) -> Result<StaticRelationOutcome, String> {
    for assertion in assertions {
        let mut universe = RelationUniverse::default();
        let mut obligations = Vec::new();
        encode_static_relation_assertion(assertion, &mut universe, &mut obligations)?;
        let witness = static_relation_counterexample_witness(&obligations, &universe);
        let mut encoder = RelationSatEncoder::new(universe);
        for obligation in &obligations {
            match obligation {
                StaticRelationObligation::Subset(left, right) => {
                    encoder
                        .require_subset(&left, &right)
                        .map_err(|err| format!("RustSAT relation subset failed: {err:?}"))?;
                }
                StaticRelationObligation::Equal(left, right) => {
                    encoder
                        .require_equal(&left, &right)
                        .map_err(|err| format!("RustSAT relation equality failed: {err:?}"))?;
                }
                StaticRelationObligation::CardinalityEq(expr, expected) => {
                    encoder
                        .require_cardinality_eq(expr, *expected)
                        .map_err(|err| format!("RustSAT relation cardinality failed: {err:?}"))?;
                }
            }
        }
        if !matches!(solve_static_relation(encoder)?, SolverResult::Sat) {
            let (witness, witness_error) = match witness {
                Ok(witness) => (Some(witness), None),
                Err(err) => (None, Some(err)),
            };
            return Ok(StaticRelationOutcome::Counterexample {
                witness,
                witness_error,
            });
        }
    }
    Ok(StaticRelationOutcome::Checked)
}

#[derive(Clone)]
enum StaticRelationObligation {
    Subset(IRRelationExpr, IRRelationExpr),
    Equal(IRRelationExpr, IRRelationExpr),
    CardinalityEq(IRRelationExpr, usize),
}

fn encode_static_relation_assertion(
    assertion: &IRExpr,
    universe: &mut RelationUniverse,
    obligations: &mut Vec<StaticRelationObligation>,
) -> Result<(), String> {
    match assertion {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSetSubset"
            || (op == "OpLe"
                && ir_expr_ty(left).is_some_and(is_ir_relation_type)
                && ir_expr_ty(right).is_some_and(is_ir_relation_type)) =>
        {
            obligations.push(StaticRelationObligation::Subset(
                lower_static_relation_expr(left, universe)?,
                lower_static_relation_expr(right, universe)?,
            ));
            Ok(())
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq"
            && ir_expr_ty(left).is_some_and(is_ir_relation_type)
            && ir_expr_ty(right).is_some_and(is_ir_relation_type) =>
        {
            obligations.push(StaticRelationObligation::Equal(
                lower_static_relation_expr(left, universe)?,
                lower_static_relation_expr(right, universe)?,
            ));
            Ok(())
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => {
            if let Some((relation, expected)) =
                parse_relation_cardinality_eq(left, right, universe)?
            {
                obligations.push(StaticRelationObligation::CardinalityEq(relation, expected));
                return Ok(());
            }
            Err(format!(
                "unsupported static relation assertion `{assertion:?}`"
            ))
        }
        _ if contains_relation_surface(assertion) => Err(format!(
            "unsupported static relation assertion `{assertion:?}`"
        )),
        _ => Err("static relation verify block contains a non-relation assertion".to_owned()),
    }
}

fn parse_relation_cardinality_eq(
    left: &IRExpr,
    right: &IRExpr,
    universe: &mut RelationUniverse,
) -> Result<Option<(IRRelationExpr, usize)>, String> {
    match (left, right) {
        (
            IRExpr::Card {
                expr: relation_expr,
                ..
            },
            IRExpr::Lit {
                value: LitVal::Int { value },
                ..
            },
        )
        | (
            IRExpr::Lit {
                value: LitVal::Int { value },
                ..
            },
            IRExpr::Card {
                expr: relation_expr,
                ..
            },
        ) if *value >= 0 && contains_relation_surface(relation_expr) => Ok(Some((
            lower_static_relation_expr(relation_expr, universe)?,
            (*value)
                .try_into()
                .map_err(|_| format!("relation cardinality bound `{value}` cannot fit in usize"))?,
        ))),
        _ => Ok(None),
    }
}

fn lower_static_relation_expr(
    expr: &IRExpr,
    universe: &mut RelationUniverse,
) -> Result<IRRelationExpr, String> {
    match expr {
        IRExpr::SetLit { elements, ty, .. } if is_ir_relation_type(ty) => {
            let relation_ty = relation_type_from_ir_type(ty)?;
            let mut lowered = Vec::with_capacity(elements.len());
            for element in elements {
                let values = tuple_values_for_relation_element(element, relation_ty.arity())?;
                register_tuple_domains(universe, &relation_ty, &values);
                lowered.push(IRRelationExpr::SingletonTuple {
                    tuple_type: relation_ty.clone(),
                    values,
                });
            }
            let mut iter = lowered.into_iter();
            let Some(first) = iter.next() else {
                register_empty_relation_domains(universe, &relation_ty);
                return Ok(IRRelationExpr::Empty(relation_ty));
            };
            Ok(iter.fold(first, |acc, elem| {
                IRRelationExpr::Union(Box::new(acc), Box::new(elem))
            }))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if is_relation_op(op, "Join") => Ok(IRRelationExpr::Join(
            Box::new(lower_static_relation_expr(left, universe)?),
            Box::new(lower_static_relation_expr(right, universe)?),
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if is_relation_op(op, "Product") => Ok(IRRelationExpr::Product(
            Box::new(lower_static_relation_expr(left, universe)?),
            Box::new(lower_static_relation_expr(right, universe)?),
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if is_relation_op(op, "Project") => Ok(IRRelationExpr::Project {
            expr: Box::new(lower_static_relation_expr(left, universe)?),
            columns: relation_project_columns(right)?,
        }),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSetUnion" => Ok(IRRelationExpr::Union(
            Box::new(lower_static_relation_expr(left, universe)?),
            Box::new(lower_static_relation_expr(right, universe)?),
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSetIntersect" => Ok(IRRelationExpr::Intersection(
            Box::new(lower_static_relation_expr(left, universe)?),
            Box::new(lower_static_relation_expr(right, universe)?),
        )),
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSetDiff" => Ok(IRRelationExpr::Difference(
            Box::new(lower_static_relation_expr(left, universe)?),
            Box::new(lower_static_relation_expr(right, universe)?),
        )),
        IRExpr::UnOp { op, operand, .. } if is_relation_op(op, "Transpose") => Ok(
            IRRelationExpr::Transpose(Box::new(lower_static_relation_expr(operand, universe)?)),
        ),
        IRExpr::UnOp { op, operand, .. } if is_relation_op(op, "Closure") => {
            Ok(IRRelationExpr::TransitiveClosure(Box::new(
                lower_static_relation_expr(operand, universe)?,
            )))
        }
        IRExpr::UnOp { op, operand, .. } if is_relation_op(op, "Reach") => {
            Ok(IRRelationExpr::ReflexiveTransitiveClosure(Box::new(
                lower_static_relation_expr(operand, universe)?,
            )))
        }
        _ => Err(format!("unsupported static relation expression `{expr:?}`")),
    }
}

fn relation_project_columns(expr: &IRExpr) -> Result<Vec<usize>, String> {
    let mut columns = Vec::new();
    collect_relation_project_columns(expr, &mut columns)?;
    if columns.is_empty() {
        return Err("relation project requires at least one column".to_owned());
    }
    Ok(columns)
}

fn collect_relation_project_columns(expr: &IRExpr, out: &mut Vec<usize>) -> Result<(), String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } => {
            if *value < 0 {
                return Err(format!(
                    "relation project column must not be negative: {value}"
                ));
            }
            out.push(
                (*value).try_into().map_err(|_| {
                    format!("relation project column `{value}` cannot fit in usize")
                })?,
            );
            Ok(())
        }
        IRExpr::App { func, arg, .. } if is_tuple_app(func) => {
            collect_relation_project_columns(func, out)?;
            collect_relation_project_columns(arg, out)
        }
        IRExpr::Var { name, .. } if name == "Tuple" => Ok(()),
        other => Err(format!(
            "relation project columns must be int literals, got `{other:?}`"
        )),
    }
}

fn is_tuple_app(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == "Tuple",
        IRExpr::App { func, .. } => is_tuple_app(func),
        _ => false,
    }
}

fn is_relation_op(op: &str, name: &str) -> bool {
    op.strip_prefix("OpRel") == Some(name) || op.strip_prefix("OpRelation") == Some(name)
}

fn relation_type_from_ir_type(ty: &IRType) -> Result<IRRelationType, String> {
    match ty {
        IRType::Set { element } => match element.as_ref() {
            IRType::Tuple { elements } => IRRelationType::new(
                elements
                    .iter()
                    .cloned()
                    .map(IRRelationColumn::unnamed)
                    .collect(),
            )
            .map_err(|err| format!("invalid relation type: {err:?}")),
            element_ty => Ok(IRRelationType::unary(element_ty.clone())),
        },
        _ => Err(format!("expected relation Set type, got `{ty:?}`")),
    }
}

fn is_ir_relation_type(ty: &IRType) -> bool {
    matches!(ty, IRType::Set { .. })
}

fn tuple_values_for_relation_element(expr: &IRExpr, arity: usize) -> Result<Vec<String>, String> {
    if arity == 1 {
        return Ok(vec![atom_value(expr)?]);
    }
    let values = tuple_app_values(expr)?;
    if values.len() == arity {
        Ok(values)
    } else {
        Err(format!(
            "relation tuple literal arity mismatch: expected {arity}, found {}",
            values.len()
        ))
    }
}

fn tuple_app_values(expr: &IRExpr) -> Result<Vec<String>, String> {
    let mut values = Vec::new();
    let mut current = expr;
    loop {
        match current {
            IRExpr::App { func, arg, .. } => {
                values.push(atom_value(arg)?);
                current = func;
            }
            IRExpr::Var { name, .. } if name == "Tuple" => {
                values.reverse();
                return Ok(values);
            }
            _ => return Err(format!("expected lowered tuple literal, got `{expr:?}`")),
        }
    }
}

fn atom_value(expr: &IRExpr) -> Result<String, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(match value {
            LitVal::Int { value } => value.to_string(),
            LitVal::Real { value } => value.to_string(),
            LitVal::Float { value } => value.to_string(),
            LitVal::Bool { value } => value.to_string(),
            LitVal::Str { value } => value.clone(),
        }),
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => Ok(format!("{enum_name}::{ctor}")),
        IRExpr::Var { name, .. } => Ok(name.clone()),
        _ => Err(format!("unsupported relation atom `{expr:?}`")),
    }
}

fn register_tuple_domains(
    universe: &mut RelationUniverse,
    relation_ty: &IRRelationType,
    values: &[String],
) {
    for (column, value) in relation_ty.columns.iter().zip(values) {
        add_domain_atom(universe, column.ty.clone(), value.clone());
    }
}

fn register_empty_relation_domains(universe: &mut RelationUniverse, relation_ty: &IRRelationType) {
    for column in &relation_ty.columns {
        universe
            .domains
            .entry(type_key(&column.ty))
            .or_insert_with(Vec::new);
    }
}

fn add_domain_atom(universe: &mut RelationUniverse, ty: IRType, value: String) {
    let domain = universe.domains.entry(type_key(&ty)).or_default();
    let atom = RelationAtom::new(value);
    if !domain.contains(&atom) {
        domain.push(atom);
    }
}

fn static_relation_counterexample_witness(
    obligations: &[StaticRelationObligation],
    universe: &RelationUniverse,
) -> Result<rel::RelationalWitness, String> {
    let Some(data) = obligations.iter().find_map(|obligation| {
        static_relation_witness_data(obligation, universe)
            .ok()
            .flatten()
    }) else {
        return Err("failed to reconstruct a violated relation obligation".to_owned());
    };

    match data {
        StaticRelationWitnessData::Binary { kind, left, right } => {
            binary_static_relation_witness(kind, left, right)
        }
        StaticRelationWitnessData::Cardinality {
            relation_type,
            tuples,
            expected,
            actual,
        } => cardinality_static_relation_witness(relation_type, tuples, expected, actual),
    }
}

enum StaticRelationWitnessData {
    Binary {
        kind: &'static str,
        left: (IRRelationType, HashSet<RelationTuple>),
        right: (IRRelationType, HashSet<RelationTuple>),
    },
    Cardinality {
        relation_type: IRRelationType,
        tuples: HashSet<RelationTuple>,
        expected: usize,
        actual: usize,
    },
}

fn static_relation_witness_data(
    obligation: &StaticRelationObligation,
    universe: &RelationUniverse,
) -> Result<Option<StaticRelationWitnessData>, RelationSatError> {
    match obligation {
        StaticRelationObligation::Subset(left, right)
        | StaticRelationObligation::Equal(left, right) => {
            let left_tuples = concrete_relation_tuples(left, universe)?;
            let right_tuples = concrete_relation_tuples(right, universe)?;
            let violated = match obligation {
                StaticRelationObligation::Subset(_, _) => !left_tuples.is_subset(&right_tuples),
                StaticRelationObligation::Equal(_, _) => left_tuples != right_tuples,
                StaticRelationObligation::CardinalityEq(_, _) => unreachable!(),
            };
            if !violated {
                return Ok(None);
            }
            Ok(Some(StaticRelationWitnessData::Binary {
                kind: match obligation {
                    StaticRelationObligation::Subset(_, _) => "subset",
                    StaticRelationObligation::Equal(_, _) => "equality",
                    StaticRelationObligation::CardinalityEq(_, _) => unreachable!(),
                },
                left: (left.relation_type()?, left_tuples),
                right: (right.relation_type()?, right_tuples),
            }))
        }
        StaticRelationObligation::CardinalityEq(expr, expected) => {
            let tuples = concrete_relation_tuples(expr, universe)?;
            let actual = tuples.len();
            if actual == *expected {
                return Ok(None);
            }
            Ok(Some(StaticRelationWitnessData::Cardinality {
                relation_type: expr.relation_type()?,
                tuples,
                expected: *expected,
                actual,
            }))
        }
    }
}

fn binary_static_relation_witness(
    kind: &'static str,
    left: (IRRelationType, HashSet<RelationTuple>),
    right: (IRRelationType, HashSet<RelationTuple>),
) -> Result<rel::RelationalWitness, String> {
    let left_missing = left.1.difference(&right.1).cloned().collect::<HashSet<_>>();
    let right_extra = right.1.difference(&left.1).cloned().collect::<HashSet<_>>();

    let mut builder = rel::RelationalState::builder()
        .derived_relation("left", relation_instance_from_tuples(&left.0, &left.1)?)
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .derived_relation("right", relation_instance_from_tuples(&right.0, &right.1)?)
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .derived_relation(
            "left_minus_right",
            relation_instance_from_tuples(&left.0, &left_missing)?,
        )
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .evaluation("relation_obligation", WitnessValue::String(kind.to_owned()))
        .map_err(|err| format!("static relation witness validation failed: {err}"))?;

    if kind == "equality" {
        builder = builder
            .derived_relation(
                "right_minus_left",
                relation_instance_from_tuples(&right.0, &right_extra)?,
            )
            .map_err(|err| format!("static relation witness validation failed: {err}"))?;
    }

    let state = builder
        .build()
        .map_err(|err| format!("static relation witness validation failed: {err}"))?;
    rel::RelationalWitness::snapshot(state)
        .map_err(|err| format!("static relation witness validation failed: {err}"))
}

fn cardinality_static_relation_witness(
    relation_type: IRRelationType,
    tuples: HashSet<RelationTuple>,
    expected: usize,
    actual: usize,
) -> Result<rel::RelationalWitness, String> {
    let state = rel::RelationalState::builder()
        .derived_relation(
            "relation",
            relation_instance_from_tuples(&relation_type, &tuples)?,
        )
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .evaluation("expected_cardinality", WitnessValue::Int(expected as i64))
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .evaluation("actual_cardinality", WitnessValue::Int(actual as i64))
        .map_err(|err| format!("static relation witness validation failed: {err}"))?
        .build()
        .map_err(|err| format!("static relation witness validation failed: {err}"))?;
    rel::RelationalWitness::snapshot(state)
        .map_err(|err| format!("static relation witness validation failed: {err}"))
}

fn concrete_relation_tuples(
    expr: &IRRelationExpr,
    universe: &RelationUniverse,
) -> Result<HashSet<RelationTuple>, RelationSatError> {
    match expr {
        IRRelationExpr::Symbol(symbol) => Err(RelationSatError::UnknownSymbol {
            name: symbol.name.clone(),
        }),
        IRRelationExpr::Empty(_) => Ok(HashSet::new()),
        IRRelationExpr::SingletonTuple { values, .. } => Ok([values
            .iter()
            .cloned()
            .map(RelationAtom::new)
            .collect::<Vec<_>>()]
        .into_iter()
        .collect()),
        IRRelationExpr::Union(left, right) => {
            let mut tuples = concrete_relation_tuples(left, universe)?;
            tuples.extend(concrete_relation_tuples(right, universe)?);
            Ok(tuples)
        }
        IRRelationExpr::Intersection(left, right) => {
            let left = concrete_relation_tuples(left, universe)?;
            let right = concrete_relation_tuples(right, universe)?;
            Ok(left.intersection(&right).cloned().collect())
        }
        IRRelationExpr::Difference(left, right) => {
            let left = concrete_relation_tuples(left, universe)?;
            let right = concrete_relation_tuples(right, universe)?;
            Ok(left.difference(&right).cloned().collect())
        }
        IRRelationExpr::Product(left, right) => {
            let left_tuples = concrete_relation_tuples(left, universe)?;
            let right_tuples = concrete_relation_tuples(right, universe)?;
            let mut out = HashSet::new();
            for left_tuple in &left_tuples {
                for right_tuple in &right_tuples {
                    let mut tuple = left_tuple.clone();
                    tuple.extend(right_tuple.iter().cloned());
                    out.insert(tuple);
                }
            }
            Ok(out)
        }
        IRRelationExpr::Join(left, right) => {
            let left_tuples = concrete_relation_tuples(left, universe)?;
            let right_tuples = concrete_relation_tuples(right, universe)?;
            let mut out = HashSet::new();
            for left_tuple in &left_tuples {
                let Some(middle) = left_tuple.last() else {
                    continue;
                };
                for right_tuple in &right_tuples {
                    if right_tuple.first() == Some(middle) {
                        let mut tuple = left_tuple[..left_tuple.len() - 1].to_vec();
                        tuple.extend(right_tuple[1..].iter().cloned());
                        out.insert(tuple);
                    }
                }
            }
            Ok(out)
        }
        IRRelationExpr::Project { expr, columns } => {
            let source = concrete_relation_tuples(expr, universe)?;
            Ok(source
                .into_iter()
                .map(|tuple| columns.iter().map(|idx| tuple[*idx].clone()).collect())
                .collect())
        }
        IRRelationExpr::Transpose(inner) => Ok(concrete_relation_tuples(inner, universe)?
            .into_iter()
            .map(|tuple| vec![tuple[1].clone(), tuple[0].clone()])
            .collect()),
        IRRelationExpr::TransitiveClosure(inner) => concrete_closure_tuples(inner, universe, false),
        IRRelationExpr::ReflexiveTransitiveClosure(inner) => {
            concrete_closure_tuples(inner, universe, true)
        }
    }
}

fn concrete_closure_tuples(
    expr: &IRRelationExpr,
    universe: &RelationUniverse,
    reflexive: bool,
) -> Result<HashSet<RelationTuple>, RelationSatError> {
    let relation_type = expr.relation_type()?;
    if relation_type.arity() != 2 {
        return Err(RelationSatError::Type(
            IRRelationTypeError::RequiresBinaryRelation {
                found: relation_type.arity(),
            },
        ));
    }
    if relation_type.columns[0].ty != relation_type.columns[1].ty {
        return Err(RelationSatError::Type(
            IRRelationTypeError::ClosureTypeMismatch {
                left: relation_type.columns[0].ty.clone(),
                right: relation_type.columns[1].ty.clone(),
            },
        ));
    }

    let domain = universe.domain_for(&relation_type.columns[0].ty)?;
    let mut closure = concrete_relation_tuples(expr, universe)?;
    if reflexive {
        for atom in domain {
            closure.insert(vec![atom.clone(), atom.clone()]);
        }
    }

    loop {
        let mut changed = false;
        let current = closure.clone();
        for left in &current {
            for right in &current {
                if left[1] == right[0] {
                    changed |= closure.insert(vec![left[0].clone(), right[1].clone()]);
                }
            }
        }
        if !changed {
            return Ok(closure);
        }
    }
}

fn relation_instance_from_tuples(
    relation_type: &IRRelationType,
    tuples: &HashSet<RelationTuple>,
) -> Result<rel::RelationInstance, String> {
    let mut builder = rel::RelationInstance::builder(relation_type.arity());
    let mut tuples = tuples.iter().collect::<Vec<_>>();
    tuples.sort_by_key(|tuple| {
        tuple
            .iter()
            .map(|atom| atom.0.as_str())
            .collect::<Vec<_>>()
            .join("\u{0}")
    });
    for tuple in tuples {
        builder = builder
            .tuple(rel::TupleValue::new(
                tuple
                    .iter()
                    .zip(&relation_type.columns)
                    .map(|(atom, column)| witness_value_for_atom(atom, &column.ty))
                    .collect(),
            ))
            .map_err(|err| format!("static relation witness tuple is invalid: {err}"))?;
    }
    builder
        .build()
        .map_err(|err| format!("static relation witness relation is invalid: {err}"))
}

fn witness_value_for_atom(atom: &RelationAtom, ty: &IRType) -> WitnessValue {
    match ty {
        IRType::Int => atom
            .0
            .parse::<i64>()
            .map(WitnessValue::Int)
            .unwrap_or_else(|_| WitnessValue::Opaque {
                display: atom.0.clone(),
                ty: Some("int".to_owned()),
            }),
        IRType::Bool => match atom.0.as_str() {
            "true" => WitnessValue::Bool(true),
            "false" => WitnessValue::Bool(false),
            _ => WitnessValue::Opaque {
                display: atom.0.clone(),
                ty: Some("bool".to_owned()),
            },
        },
        IRType::Real => WitnessValue::Real(atom.0.clone()),
        IRType::Float => WitnessValue::Float(atom.0.clone()),
        IRType::String => WitnessValue::String(atom.0.clone()),
        IRType::Identity => WitnessValue::Identity(atom.0.clone()),
        IRType::Entity { name } => WitnessValue::Opaque {
            display: atom.0.clone(),
            ty: Some(name.clone()),
        },
        IRType::Enum { name, .. } => {
            let variant = atom.0.rsplit("::").next().unwrap_or(&atom.0).to_owned();
            WitnessValue::EnumVariant {
                enum_name: name.clone(),
                variant,
            }
        }
        _ => WitnessValue::Opaque {
            display: atom.0.clone(),
            ty: Some(format!("{ty:?}")),
        },
    }
}

fn solve_static_relation(encoder: RelationSatEncoder) -> Result<SolverResult, String> {
    let (cnf, _) = encoder.sat.into_cnf();
    let mut solver = BasicSolver::default();
    solver
        .add_cnf(cnf)
        .map_err(|err| format!("RustSAT relation CNF load failed: {err}"))?;
    solver
        .solve()
        .map_err(|err| format!("RustSAT relation solve failed: {err}"))
}

fn contains_relation_surface(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            is_any_relation_op(op)
                || (matches!(
                    op.as_str(),
                    "OpSetSubset" | "OpSetUnion" | "OpSetIntersect" | "OpSetDiff" | "OpEq"
                ) && (ir_expr_ty(left).is_some_and(is_ir_relation_type)
                    || ir_expr_ty(right).is_some_and(is_ir_relation_type)))
                || contains_relation_surface(left)
                || contains_relation_surface(right)
        }
        IRExpr::UnOp { op, operand, .. } => {
            is_any_relation_op(op) || contains_relation_surface(operand)
        }
        IRExpr::SetLit { ty, .. } => is_ir_relation_type(ty),
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            contains_relation_surface(projection)
                || contains_relation_surface(filter)
                || bindings.iter().any(|binding| {
                    binding
                        .source
                        .as_ref()
                        .is_some_and(|source| contains_relation_surface(source))
                })
        }
        IRExpr::App { func, arg, .. } => {
            contains_relation_surface(func) || contains_relation_surface(arg)
        }
        IRExpr::Card { expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. }
        | IRExpr::Prime { expr, .. } => contains_relation_surface(expr),
        _ => false,
    }
}

fn is_any_relation_op(op: &str) -> bool {
    op.starts_with("OpRel") || op.starts_with("OpRelation")
}

fn ir_expr_ty(expr: &IRExpr) -> Option<&IRType> {
    match expr {
        IRExpr::Lit { ty, .. }
        | IRExpr::Var { ty, .. }
        | IRExpr::BinOp { ty, .. }
        | IRExpr::UnOp { ty, .. }
        | IRExpr::App { ty, .. }
        | IRExpr::Choose { ty, .. }
        | IRExpr::MapUpdate { ty, .. }
        | IRExpr::Index { ty, .. }
        | IRExpr::SetLit { ty, .. }
        | IRExpr::SeqLit { ty, .. }
        | IRExpr::MapLit { ty, .. }
        | IRExpr::SetComp { ty, .. }
        | IRExpr::RelComp { ty, .. }
        | IRExpr::VarDecl { ty, .. } => Some(ty),
        IRExpr::Ctor { .. } => None,
        IRExpr::Lam { .. }
        | IRExpr::Let { .. }
        | IRExpr::Forall { .. }
        | IRExpr::Exists { .. }
        | IRExpr::One { .. }
        | IRExpr::Lone { .. }
        | IRExpr::Field { .. }
        | IRExpr::Prime { .. }
        | IRExpr::Always { .. }
        | IRExpr::Eventually { .. }
        | IRExpr::Until { .. }
        | IRExpr::Historically { .. }
        | IRExpr::Once { .. }
        | IRExpr::Previously { .. }
        | IRExpr::Since { .. }
        | IRExpr::Aggregate { .. }
        | IRExpr::Saw { .. }
        | IRExpr::Match { .. }
        | IRExpr::Card { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. }
        | IRExpr::Assert { .. }
        | IRExpr::Assume { .. }
        | IRExpr::Block { .. }
        | IRExpr::While { .. }
        | IRExpr::IfElse { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use rustsat::solvers::{Solve, SolverResult};
    use rustsat_batsat::BasicSolver;

    use crate::ir::relation::{IRRelationColumn, IRRelationExpr, IRRelationSymbol, IRRelationType};

    use super::*;

    fn entity(name: &str) -> IRType {
        IRType::Entity {
            name: name.to_owned(),
        }
    }

    fn tuple(values: &[&str]) -> RelationTuple {
        values.iter().copied().map(RelationAtom::new).collect()
    }

    fn binary_symbol(name: &str, left: &str, right: &str) -> IRRelationSymbol {
        IRRelationSymbol {
            name: name.to_owned(),
            relation_type: IRRelationType::binary(entity(left), entity(right)),
            mutable: false,
            source: crate::ir::relation::IRRelationSource::UserRelation {
                name: name.to_owned(),
            },
        }
    }

    fn mutable_binary_symbol(name: &str, left: &str, right: &str) -> IRRelationSymbol {
        IRRelationSymbol {
            name: name.to_owned(),
            relation_type: IRRelationType::binary(entity(left), entity(right)),
            mutable: true,
            source: crate::ir::relation::IRRelationSource::UserRelation {
                name: name.to_owned(),
            },
        }
    }

    fn unary_symbol(name: &str, ty: &str) -> IRRelationSymbol {
        IRRelationSymbol {
            name: name.to_owned(),
            relation_type: IRRelationType::unary(entity(ty)),
            mutable: false,
            source: crate::ir::relation::IRRelationSource::UserRelation {
                name: name.to_owned(),
            },
        }
    }

    fn universe() -> RelationUniverse {
        let mut universe = RelationUniverse::default();
        universe.add_domain(entity("Order"), ["o0", "o1"]);
        universe.add_domain(entity("Customer"), ["c0", "c1", "c2"]);
        universe.add_domain(entity("Segment"), ["vip", "standard"]);
        universe
    }

    fn solve(encoder: RelationSatEncoder) -> SolverResult {
        let (cnf, _) = encoder.sat.into_cnf();
        let mut solver = BasicSolver::default();
        solver.add_cnf(cnf).expect("test CNF should load");
        solver.solve().expect("test solve should complete")
    }

    #[test]
    fn join_membership_follows_matching_middle_atom() {
        let order_customer = binary_symbol("order_customer", "Order", "Customer");
        let customer_segment = binary_symbol("customer_segment", "Customer", "Segment");
        let join = IRRelationExpr::Join(
            Box::new(IRRelationExpr::Symbol(order_customer.clone())),
            Box::new(IRRelationExpr::Symbol(customer_segment.clone())),
        );

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(order_customer, [tuple(&["o0", "c0"]), tuple(&["o1", "c1"])]);
        encoder.define_symbol(customer_segment, [tuple(&["c0", "vip"])]);
        encoder
            .require_member(&join, tuple(&["o0", "vip"]))
            .expect("join member encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(
            binary_symbol("order_customer", "Order", "Customer"),
            [tuple(&["o0", "c0"]), tuple(&["o1", "c1"])],
        );
        encoder.define_symbol(
            binary_symbol("customer_segment", "Customer", "Segment"),
            [tuple(&["c0", "vip"])],
        );
        encoder
            .require_member(&join, tuple(&["o1", "vip"]))
            .expect("join member encodes");
        assert!(matches!(solve(encoder), SolverResult::Unsat));
    }

    #[test]
    fn product_and_projection_encode_relation_equality() {
        let customers = unary_symbol("customers", "Customer");
        let segments = unary_symbol("segments", "Segment");
        let product = IRRelationExpr::Product(
            Box::new(IRRelationExpr::Symbol(customers.clone())),
            Box::new(IRRelationExpr::Symbol(segments.clone())),
        );
        let segment_projection = IRRelationExpr::Project {
            expr: Box::new(product),
            columns: vec![1],
        };

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(customers, [tuple(&["c0"]), tuple(&["c1"])]);
        encoder.define_symbol(segments.clone(), [tuple(&["vip"])]);
        encoder
            .require_equal(&segment_projection, &IRRelationExpr::Symbol(segments))
            .expect("projection equality encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));
    }

    #[test]
    fn union_difference_subset_and_cardinality_are_encoded() {
        let left = unary_symbol("left_customers", "Customer");
        let right = unary_symbol("right_customers", "Customer");
        let union = IRRelationExpr::Union(
            Box::new(IRRelationExpr::Symbol(left.clone())),
            Box::new(IRRelationExpr::Symbol(right.clone())),
        );
        let difference = IRRelationExpr::Difference(
            Box::new(union.clone()),
            Box::new(IRRelationExpr::Symbol(right.clone())),
        );

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(left.clone(), [tuple(&["c0"])]);
        encoder.define_symbol(right.clone(), [tuple(&["c1"])]);
        encoder
            .require_cardinality_eq(&union, 2)
            .expect("union cardinality encodes");
        encoder
            .require_subset(&IRRelationExpr::Symbol(left), &difference)
            .expect("subset encodes");
        encoder
            .require_not_member(&difference, tuple(&["c1"]))
            .expect("difference non-member encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));
    }

    #[test]
    fn singleton_tuple_membership_uses_literal_tuple_values() {
        let singleton = IRRelationExpr::SingletonTuple {
            tuple_type: IRRelationType::binary(entity("Order"), entity("Customer")),
            values: vec!["o0".to_owned(), "c0".to_owned()],
        };

        let mut encoder = RelationSatEncoder::new(universe());
        encoder
            .require_member(&singleton, tuple(&["o0", "c0"]))
            .expect("matching singleton tuple should encode");
        assert!(matches!(solve(encoder), SolverResult::Sat));

        let mut encoder = RelationSatEncoder::new(universe());
        encoder
            .require_member(&singleton, tuple(&["o0", "c1"]))
            .expect("non-matching singleton tuple should encode");
        assert!(matches!(solve(encoder), SolverResult::Unsat));
    }

    #[test]
    fn transitive_closure_encodes_finite_reachability() {
        let edge = binary_symbol("edge", "Customer", "Customer");
        let closure =
            IRRelationExpr::TransitiveClosure(Box::new(IRRelationExpr::Symbol(edge.clone())));

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(edge.clone(), [tuple(&["c0", "c1"]), tuple(&["c1", "c2"])]);
        encoder
            .require_member(&closure, tuple(&["c0", "c2"]))
            .expect("closure reachability encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(edge, [tuple(&["c0", "c1"]), tuple(&["c1", "c2"])]);
        encoder
            .require_member(&closure, tuple(&["c2", "c0"]))
            .expect("closure reachability encodes");
        assert!(matches!(solve(encoder), SolverResult::Unsat));
    }

    #[test]
    fn reflexive_transitive_closure_includes_identity() {
        let edge = binary_symbol("edge", "Customer", "Customer");
        let closure = IRRelationExpr::ReflexiveTransitiveClosure(Box::new(IRRelationExpr::Symbol(
            edge.clone(),
        )));

        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol(edge, [tuple(&["c0", "c1"])]);
        encoder
            .require_member(&closure, tuple(&["c2", "c2"]))
            .expect("reflexive closure identity encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));
    }

    #[test]
    fn closure_rejects_non_binary_relations_before_sat_encoding() {
        let unary = IRRelationExpr::Empty(
            IRRelationType::new(vec![IRRelationColumn::unnamed(entity("Customer"))])
                .expect("unary type"),
        );
        let closure = IRRelationExpr::TransitiveClosure(Box::new(unary));
        let mut encoder = RelationSatEncoder::new(universe());
        let err = encoder
            .require_member(&closure, tuple(&["c0"]))
            .expect_err("closure requires binary relation");
        assert!(matches!(
            err,
            RelationSatError::Type(IRRelationTypeError::RequiresBinaryRelation { found: 1 })
        ));
    }

    #[test]
    fn mutable_relation_membership_reads_state_specific_symbols() {
        let owns = mutable_binary_symbol("owns", "Customer", "Order");
        let expr = IRRelationExpr::Symbol(owns.clone());
        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol_at_state(0, owns.clone(), []);
        encoder.define_symbol_at_state(1, owns, [tuple(&["c0", "o0"])]);

        encoder
            .require_not_member_at_state(0, &expr, tuple(&["c0", "o0"]))
            .expect("state 0 non-membership encodes");
        encoder
            .require_member_at_state(1, &expr, tuple(&["c0", "o0"]))
            .expect("state 1 membership encodes");

        assert!(matches!(solve(encoder), SolverResult::Sat));
    }

    #[test]
    fn mutable_relation_frame_constraint_requires_unchanged_tuple_set() {
        let owns = mutable_binary_symbol("owns", "Customer", "Order");

        let mut framed = RelationSatEncoder::new(universe());
        framed.define_symbol_at_state(0, owns.clone(), [tuple(&["c0", "o0"])]);
        framed.define_symbol_at_state(1, owns.clone(), [tuple(&["c0", "o0"])]);
        framed
            .require_frame_between(&owns, 0, 1)
            .expect("matching states frame");
        assert!(matches!(solve(framed), SolverResult::Sat));

        let mut changed = RelationSatEncoder::new(universe());
        changed.define_symbol_at_state(0, owns.clone(), [tuple(&["c0", "o0"])]);
        changed.define_symbol_at_state(1, owns.clone(), [tuple(&["c1", "o1"])]);
        changed
            .require_frame_between(&owns, 0, 1)
            .expect("mismatching states frame into unsat constraints");
        assert!(matches!(solve(changed), SolverResult::Unsat));
    }

    #[test]
    fn mutable_relation_closure_is_evaluated_per_state() {
        let edge = mutable_binary_symbol("edge", "Customer", "Customer");
        let closure =
            IRRelationExpr::TransitiveClosure(Box::new(IRRelationExpr::Symbol(edge.clone())));
        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol_at_state(0, edge.clone(), [tuple(&["c0", "c1"])]);
        encoder.define_symbol_at_state(1, edge, [tuple(&["c0", "c1"]), tuple(&["c1", "c2"])]);

        encoder
            .require_not_member_at_state(0, &closure, tuple(&["c0", "c2"]))
            .expect("state 0 closure encodes");
        encoder
            .require_member_at_state(1, &closure, tuple(&["c0", "c2"]))
            .expect("state 1 closure encodes");
        assert!(matches!(solve(encoder), SolverResult::Sat));
    }

    #[test]
    fn mutable_relation_state_tuples_are_reconstructable_for_witnesses() {
        let owns = mutable_binary_symbol("owns", "Customer", "Order");
        let mut encoder = RelationSatEncoder::new(universe());
        encoder.define_symbol_at_state(1, owns, [tuple(&["c0", "o0"])]);

        assert_eq!(
            encoder
                .relation_tuples_at_state("owns", 1)
                .expect("state tuples should be reconstructable"),
            vec![tuple(&["c0", "o0"])]
        );
    }
}
