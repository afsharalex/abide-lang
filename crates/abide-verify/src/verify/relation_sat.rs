//! Finite bounded-relation SAT encoding.
//!
//! This is the Kodkod-like core used by the relational backend: given finite
//! atom domains and fixed relation symbols, it encodes relation algebra over
//! tuple membership literals.

use std::collections::{HashMap, HashSet};

use rustsat::instances::SatInstance;
use rustsat::types::constraints::CardConstraint;
use rustsat::types::Lit;

use crate::ir::relation::{IRRelationExpr, IRRelationSymbol, IRRelationType, IRRelationTypeError};
use crate::ir::types::IRType;

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

#[derive(Debug, Default)]
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
            IRRelationExpr::SingletonTuple { .. } => {
                Err(RelationSatError::UnsupportedRelationExpr("singleton tuple"))
            }
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
    UnsupportedRelationExpr(&'static str),
}

impl From<IRRelationTypeError> for RelationSatError {
    fn from(value: IRRelationTypeError) -> Self {
        Self::Type(value)
    }
}

fn type_key(ty: &IRType) -> String {
    format!("{ty:?}")
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
