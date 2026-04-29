use super::*;
use crate::ast::{EventItem, Pattern, SceneItem, SystemItem, TypeRefKind, TypeVariant, WhenItem};
use crate::lex;

fn parse_expr(src: &str) -> Expr {
    let tokens = lex::lex(src).expect("lex error");
    let mut parser = Parser::new(tokens);
    parser.expr().expect("parse error")
}

fn parse_program(src: &str) -> Program {
    let tokens = lex::lex(src).expect("lex error");
    let mut parser = Parser::new(tokens);
    parser.parse_program().expect("parse error")
}

fn first_scene_when_item(src: &str) -> WhenItem {
    let program = parse_program(src);
    let scene = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::Scene(scene) => Some(scene),
            _ => None,
        })
        .expect("expected scene");
    let when_block = scene
        .items
        .iter()
        .find_map(|item| match item {
            SceneItem::WhenBlock { items, .. } => Some(items),
            _ => None,
        })
        .expect("expected when block");
    when_block.first().expect("expected when item").clone()
}

/// Parse a program expecting a parse error; returns the error so the
/// caller can assert on it.
fn parse_program_err(src: &str) -> ParseError {
    let tokens = lex::lex(src).expect("lex error");
    let mut parser = Parser::new(tokens);
    parser
        .parse_program()
        .expect_err("expected parse error, got successful parse")
}

// ── Expression precedence tests ──────────────────────────────────

#[test]
fn atom_int() {
    let e = parse_expr("42");
    assert!(matches!(e.kind, ExprKind::Int(42)));
}

#[test]
fn atom_var() {
    let e = parse_expr("status");
    assert!(matches!(e.kind, ExprKind::Var(ref s) if s == "status"));
}

#[test]
fn atom_true_false() {
    assert!(matches!(parse_expr("true").kind, ExprKind::True));
    assert!(matches!(parse_expr("false").kind, ExprKind::False));
}

#[test]
fn atom_state() {
    let e = parse_expr("@Pending");
    assert!(matches!(e.kind, ExprKind::State1(ref s) if s == "Pending"));
}

#[test]
fn atom_state2() {
    let e = parse_expr("@OrderStatus::Paid");
    assert!(matches!(e.kind, ExprKind::State2(ref a, ref b) if a == "OrderStatus" && b == "Paid"));
}

#[test]
fn atom_qual2() {
    let e = parse_expr("Commerce::confirm_payment");
    assert!(
        matches!(e.kind, ExprKind::Qual2(ref a, ref b) if a == "Commerce" && b == "confirm_payment")
    );
}

#[test]
fn binary_add() {
    let e = parse_expr("a + b");
    assert!(matches!(e.kind, ExprKind::Add(_, _)));
}

#[test]
fn precedence_add_mul() {
    // a + b * c → a + (b * c)
    let e = parse_expr("a + b * c");
    match &e.kind {
        ExprKind::Add(lhs, rhs) => {
            assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s == "a"));
            assert!(matches!(rhs.kind, ExprKind::Mul(_, _)));
        }
        other => panic!("expected Add, got {other:?}"),
    }
}

#[test]
fn precedence_and_or() {
    // a or b and c → a or (b and c)
    let e = parse_expr("a or b and c");
    match &e.kind {
        ExprKind::Or(_, rhs) => {
            assert!(matches!(rhs.kind, ExprKind::And(_, _)));
        }
        other => panic!("expected Or, got {other:?}"),
    }
}

#[test]
fn precedence_implies_and() {
    // a and b implies c → (a and b) implies c
    let e = parse_expr("a and b implies c");
    assert!(matches!(e.kind, ExprKind::Impl(_, _)));
}

#[test]
fn right_assoc_seq() {
    // a -> b -> c → a -> (b -> c)
    let e = parse_expr("a -> b -> c");
    match &e.kind {
        ExprKind::Seq(lhs, rhs) => {
            assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s == "a"));
            assert!(matches!(rhs.kind, ExprKind::Seq(_, _)));
        }
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn right_assoc_assign() {
    // a = b = c → a = (b = c)
    let e = parse_expr("a = b = c");
    match &e.kind {
        ExprKind::Assign(_, rhs) => {
            assert!(matches!(rhs.kind, ExprKind::Assign(_, _)));
        }
        other => panic!("expected Assign, got {other:?}"),
    }
}

#[test]
fn prefix_neg() {
    let e = parse_expr("-x");
    assert!(matches!(e.kind, ExprKind::Neg(_)));
}

#[test]
fn prefix_not() {
    let e = parse_expr("not x");
    assert!(matches!(e.kind, ExprKind::Not(_)));
}

#[test]
fn prefix_card() {
    let e = parse_expr("#s");
    assert!(matches!(e.kind, ExprKind::Card(_)));
}

#[test]
fn postfix_prime() {
    let e = parse_expr("status'");
    match &e.kind {
        ExprKind::Prime(inner) => {
            assert!(matches!(inner.kind, ExprKind::Var(ref s) if s == "status"));
        }
        other => panic!("expected Prime, got {other:?}"),
    }
}

#[test]
fn postfix_field() {
    let e = parse_expr("o.status");
    match &e.kind {
        ExprKind::Field(inner, name) => {
            assert!(matches!(inner.kind, ExprKind::Var(ref s) if s == "o"));
            assert_eq!(name, "status");
        }
        other => panic!("expected Field, got {other:?}"),
    }
}

#[test]
fn postfix_call() {
    let e = parse_expr("f(x, y)");
    match &e.kind {
        ExprKind::Call(callee, args) => {
            assert!(matches!(callee.kind, ExprKind::Var(ref s) if s == "f"));
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn method_call() {
    let e = parse_expr("o.submit()");
    match &e.kind {
        ExprKind::Call(callee, args) => {
            assert!(matches!(callee.kind, ExprKind::Field(_, _)));
            assert!(args.is_empty());
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn primed_assign() {
    let e = parse_expr("status' = @Paid");
    match &e.kind {
        ExprKind::Assign(lhs, rhs) => {
            assert!(matches!(lhs.kind, ExprKind::Prime(_)));
            assert!(matches!(rhs.kind, ExprKind::State1(_)));
        }
        other => panic!("expected Assign, got {other:?}"),
    }
}

#[test]
fn always_all() {
    let e = parse_expr("always all o: Order | o.total >= 0");
    assert!(matches!(e.kind, ExprKind::Always(_)));
}

#[test]
fn exists_quantifier() {
    let e = parse_expr("exists o: Order | o.id == order_id");
    assert!(matches!(e.kind, ExprKind::Exists(_, _, _, _)));
}

#[test]
fn choose_expr_with_binding_and_where() {
    let e = parse_expr("choose id: ChargeId where valid(id) and starts_with($, \"ch_\")");
    match &e.kind {
        ExprKind::Choose(binder, ty, Some(pred)) => {
            assert_eq!(binder, "id");
            assert!(matches!(&ty.kind, TypeRefKind::Simple(name) if name == "ChargeId"));
            assert!(matches!(pred.kind, ExprKind::And(_, _)));
        }
        other => panic!("expected Choose, got {other:?}"),
    }
}

#[test]
fn parse_extern_with_may_and_assume() {
    let program = parse_program(
        r#"
extern Stripe {
  command charge(customer: string, amount: int) -> Result<ChargeId, StripeError>

  may charge {
    return @Ok(choose id: ChargeId where valid(id) and starts_with($, "ch_"))
    return @Err(@card_declined)
  }

  assume {
    fair Stripe::charge
  }
}
"#,
    );

    let ext = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::Extern(ext) => Some(ext),
            _ => None,
        })
        .expect("expected extern");

    assert_eq!(ext.name, "Stripe");
    assert_eq!(ext.items.len(), 3);
    assert!(matches!(ext.items[0], crate::ast::ExternItem::Command(_)));
    match &ext.items[1] {
        crate::ast::ExternItem::May(may) => {
            assert_eq!(may.command, "charge");
            assert_eq!(may.returns.len(), 2);
        }
        other => panic!("expected may decl, got {other:?}"),
    }
    match &ext.items[2] {
        crate::ast::ExternItem::Assume(block) => {
            assert_eq!(block.items.len(), 1);
            assert!(matches!(
                block.items[0],
                crate::ast::ExternAssumeItem::Fair { .. }
            ));
        }
        other => panic!("expected assume block, got {other:?}"),
    }
}

#[test]
fn parse_system_dep_and_implements() {
    let program = parse_program(
        r#"
interface PaymentProcessor {
  command charge(customer: string, amount: int) -> Result<ChargeId, StripeError>
}

system StripeAdapter implements PaymentProcessor {
  dep Stripe
  command charge(customer: string, amount: int) -> Result<ChargeId, StripeError>
}
"#,
    );

    let system = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::System(system) => Some(system),
            _ => None,
        })
        .expect("expected system");

    assert_eq!(system.implements.as_deref(), Some("PaymentProcessor"));
    assert!(matches!(system.items[0], SystemItem::Dep(_)));
    assert!(matches!(system.items[1], SystemItem::Command(_)));
}

#[test]
fn parse_action_macro_let_call_and_match() {
    let program = parse_program(
        r#"
system Billing {
  action submit() {
    let result = Stripe::charge(1)
    match result {
      ok { value: id } => { charged' = true }
      err => { charged' = false }
    }
  }
}
"#,
    );

    let system = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::System(system) => Some(system),
            _ => None,
        })
        .expect("expected system");

    let step = match &system.items[0] {
        SystemItem::Action(step) => step,
        other => panic!("expected Action, got {other:?}"),
    };

    assert!(matches!(step.items[0], crate::ast::EventItem::LetCall(_)));
    match &step.items[1] {
        crate::ast::EventItem::Match(block) => {
            assert_eq!(block.arms.len(), 2);
            assert!(matches!(
                block.scrutinee,
                crate::ast::EventMatchScrutinee::Var(_, _)
            ));
        }
        other => panic!("expected Match event item, got {other:?}"),
    }
}

#[test]
fn parse_action_macro_direct_call_match() {
    let program = parse_program(
        r#"
system Billing {
  action submit() {
    match Stripe::charge(1) {
      ok { value: id } => { charged' = true }
    }
  }
}
"#,
    );

    let system = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::System(system) => Some(system),
            _ => None,
        })
        .expect("expected system");

    let step = match &system.items[0] {
        SystemItem::Action(step) => step,
        other => panic!("expected Action, got {other:?}"),
    };

    match &step.items[0] {
        crate::ast::EventItem::Match(block) => {
            assert!(matches!(
                block.scrutinee,
                crate::ast::EventMatchScrutinee::Call { .. }
            ));
            assert_eq!(block.arms.len(), 1);
        }
        other => panic!("expected Match event item, got {other:?}"),
    }
}

#[test]
fn parse_system_command_clause_with_body() {
    let program = parse_program(
        r#"
system Billing {
  command submit() requires true {
    let result = Provider::charge(1)
    match result {
      ok { value: id } => { charged' = id == 1 }
      err => { charged' = false }
    }
  }
}
"#,
    );

    let system = program
        .decls
        .iter()
        .find_map(|decl| match decl {
            crate::ast::TopDecl::System(system) => Some(system),
            _ => None,
        })
        .expect("expected system");

    let command = match &system.items[0] {
        SystemItem::Command(command) => command,
        other => panic!("expected Command, got {other:?}"),
    };

    let body = command.body.as_ref().expect("expected inline command body");
    assert_eq!(body.contracts.len(), 1);
    assert!(matches!(body.items[0], crate::ast::EventItem::LetCall(_)));
    assert!(matches!(body.items[1], crate::ast::EventItem::Match(_)));
}

#[test]
fn scene_when_instance_call_parses_cardinality() {
    let item = first_scene_when_item(
        r#"
scene s {
  when {
    auth.login_failed(u.id){5}
  }
}
"#,
    );
    match item {
        WhenItem::InstanceCall {
            instance,
            command,
            card,
            ..
        } => {
            assert_eq!(instance, "auth");
            assert_eq!(command, "login_failed");
            assert_eq!(card.as_deref(), Some("5"));
        }
        other => panic!("expected instance call, got {other:?}"),
    }
}

#[test]
fn scene_when_instance_call_parses_named_cardinality() {
    let item = first_scene_when_item(
        r#"
scene s {
  when {
    auth.login_failed(u.id){some}
  }
}
"#,
    );
    match item {
        WhenItem::InstanceCall { card, .. } => {
            assert_eq!(card.as_deref(), Some("some"));
        }
        other => panic!("expected instance call, got {other:?}"),
    }
}

#[test]
fn scene_when_let_call_binds_name_and_cardinality() {
    let item = first_scene_when_item(
        r#"
scene s {
  when {
    let auth_login_failed = auth.login_failed(u.id){5}
  }
}
"#,
    );
    match item {
        WhenItem::LetCall {
            name,
            instance,
            command,
            card,
            ..
        } => {
            assert_eq!(name, "auth_login_failed");
            assert_eq!(instance, "auth");
            assert_eq!(command, "login_failed");
            assert_eq!(card.as_deref(), Some("5"));
        }
        other => panic!("expected let call, got {other:?}"),
    }
}

#[test]
fn named_pair() {
    let e = parse_expr("order_id: order_id");
    assert!(matches!(e.kind, ExprKind::NamedPair(_, _)));
}

#[test]
fn let_expr() {
    let e = parse_expr("let x = 1 in x + 1");
    match &e.kind {
        ExprKind::Let(binds, body) => {
            assert_eq!(binds.len(), 1);
            assert_eq!(binds[0].name, "x");
            assert!(matches!(body.kind, ExprKind::Add(_, _)));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn lambda() {
    let e = parse_expr("fn(x: int) => x + 1");
    assert!(matches!(e.kind, ExprKind::Lambda(_, _)));
}

#[test]
fn tuple_literal() {
    let e = parse_expr("(a, b, c)");
    match &e.kind {
        ExprKind::TupleLit(elems) => assert_eq!(elems.len(), 3),
        other => panic!("expected TupleLit, got {other:?}"),
    }
}

#[test]
fn paren_expr() {
    let e = parse_expr("(a + b)");
    assert!(matches!(e.kind, ExprKind::Add(_, _)));
}

#[test]
fn pipe_and_composition() {
    let e = parse_expr("a | b");
    assert!(matches!(e.kind, ExprKind::Unord(_, _)));

    let e = parse_expr("a || b");
    assert!(matches!(e.kind, ExprKind::Conc(_, _)));

    let e = parse_expr("a ^| b");
    assert!(matches!(e.kind, ExprKind::Xor(_, _)));

    let e = parse_expr("a |> b");
    assert!(matches!(e.kind, ExprKind::Pipe(_, _)));
}

#[test]
fn equality_and_membership() {
    assert!(matches!(parse_expr("a == b").kind, ExprKind::Eq(_, _)));
    assert!(matches!(parse_expr("a != b").kind, ExprKind::NEq(_, _)));
    assert!(matches!(parse_expr("a in b").kind, ExprKind::In(_, _)));
}

#[test]
fn comparison() {
    assert!(matches!(parse_expr("a < b").kind, ExprKind::Lt(_, _)));
    assert!(matches!(parse_expr("a > b").kind, ExprKind::Gt(_, _)));
    assert!(matches!(parse_expr("a <= b").kind, ExprKind::Le(_, _)));
    assert!(matches!(parse_expr("a >= b").kind, ExprKind::Ge(_, _)));
}

#[test]
fn same_step() {
    assert!(matches!(parse_expr("a & b").kind, ExprKind::SameStep(_, _)));
}

#[test]
fn eventually() {
    assert!(matches!(
        parse_expr("eventually p").kind,
        ExprKind::Eventually(_)
    ));
}

// ── Type reference tests ─────────────────────────────────────────

#[test]
fn type_ref_simple() {
    let src = "fn id(x: int): int = x";
    let prog = parse_program(src);
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Fn(f) = &prog.decls[0] {
        assert_eq!(f.name, "id");
        assert!(matches!(f.ret_type.kind, TypeRefKind::Simple(ref s) if s == "int"));
    } else {
        panic!("expected Fn");
    }
}

#[test]
fn type_ref_fn() {
    let src = "fn apply(f: int -> bool, x: int): bool = f(x)";
    let prog = parse_program(src);
    if let TopDecl::Fn(f) = &prog.decls[0] {
        assert!(matches!(f.params[0].ty.kind, TypeRefKind::Fn(_, _)));
    } else {
        panic!("expected Fn");
    }
}

// ── Declaration tests ────────────────────────────────────────────

#[test]
fn module_decl() {
    let prog = parse_program("module Commerce");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Module(m) = &prog.decls[0] {
        assert_eq!(m.name, "Commerce");
    } else {
        panic!("expected Module");
    }
}

#[test]
fn module_decl_with_semicolon() {
    let prog = parse_program("module Commerce;");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Module(m) = &prog.decls[0] {
        assert_eq!(m.name, "Commerce");
    } else {
        panic!("expected Module");
    }
}

#[test]
fn include_decl() {
    let prog = parse_program(r#"include "billing.ab""#);
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Include(i) = &prog.decls[0] {
        assert_eq!(i.path, "billing.ab");
    } else {
        panic!("expected Include");
    }
}

#[test]
fn private_by_default() {
    let prog = parse_program("enum Status = Active | Inactive");
    if let TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.visibility, Visibility::Private);
    } else {
        panic!("expected Type");
    }
}

#[test]
fn use_all() {
    let prog = parse_program("use Billing :: *");
    if let TopDecl::Use(UseDecl::All { module, .. }) = &prog.decls[0] {
        assert_eq!(module, "Billing");
    } else {
        panic!("expected Use::All");
    }
}

#[test]
fn use_single() {
    let prog = parse_program("use Commerce::Order");
    if let TopDecl::Use(UseDecl::Single { module, name, .. }) = &prog.decls[0] {
        assert_eq!(module, "Commerce");
        assert_eq!(name, "Order");
    } else {
        panic!("expected Use::Single");
    }
}

#[test]
fn use_alias() {
    let prog = parse_program("use Commerce::Order as CO");
    if let TopDecl::Use(UseDecl::Alias {
        module,
        name,
        alias,
        ..
    }) = &prog.decls[0]
    {
        assert_eq!(module, "Commerce");
        assert_eq!(name, "Order");
        assert_eq!(alias, "CO");
    } else {
        panic!("expected Use::Alias");
    }
}

#[test]
fn use_items() {
    let src = "use Billing::{PaymentIntent as PI, open_intent, capture_payment}";
    let prog = parse_program(src);
    if let TopDecl::Use(UseDecl::Items { module, items, .. }) = &prog.decls[0] {
        assert_eq!(module, "Billing");
        assert_eq!(items.len(), 3);
        // First item is an alias
        assert!(
            matches!(&items[0], UseItem::Alias { name, alias, .. } if name == "PaymentIntent" && alias == "PI")
        );
        // Second and third are plain names
        assert!(matches!(&items[1], UseItem::Name { name, .. } if name == "open_intent"));
        assert!(matches!(&items[2], UseItem::Name { name, .. } if name == "capture_payment"));
    } else {
        panic!("expected Use::Items");
    }
}

#[test]
fn const_decl() {
    let prog = parse_program("const MAX_ORDERS = 500");
    if let TopDecl::Const(c) = &prog.decls[0] {
        assert_eq!(c.name, "MAX_ORDERS");
        assert!(matches!(c.value.kind, ExprKind::Int(500)));
    } else {
        panic!("expected Const");
    }
}

#[test]
fn sum_type() {
    let prog = parse_program("enum OrderStatus = Pending | AwaitingPayment | Paid");
    if let TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "OrderStatus");
        assert_eq!(t.variants.len(), 3);
    } else {
        panic!("expected Type");
    }
}

#[test]
fn record_type() {
    let prog = parse_program("struct Address { street: string, city: string }");
    if let TopDecl::Record(r) = &prog.decls[0] {
        assert_eq!(r.name, "Address");
        assert_eq!(r.fields.len(), 2);
    } else {
        panic!("expected Record");
    }
}

#[test]
fn entity_decl() {
    let src = r"entity Order {
  id: identity
  status: OrderStatus = @Pending

  action submit()
requires status == @Pending {
status' = @AwaitingPayment
  }
}";
    let prog = parse_program(src);
    if let TopDecl::Entity(e) = &prog.decls[0] {
        assert_eq!(e.name, "Order");
        assert_eq!(e.items.len(), 3);
    } else {
        panic!("expected Entity");
    }
}

/// a `derived NAME = EXPR` clause in an entity
/// body parses as a `DerivedDecl` and lives alongside fields and
/// actions in the entity's items list.
#[test]
fn entity_derived_field_single_expression() {
    let src = r"entity Order {
  status: OrderStatus = @Pending
  derived is_done = status == @Shipped
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    assert_eq!(e.items.len(), 2);
    let EntityItem::Derived(d) = &e.items[1] else {
        panic!("expected Derived in items[1], got: {:?}", e.items[1]);
    };
    assert_eq!(d.name, "is_done");
}

/// derived field bodies may be arbitrary
/// expressions including let-in expressions for naming intermediate
/// values. The body parser is the existing expression parser; no
/// special sub-grammar.
#[test]
fn entity_derived_field_let_in_form() {
    let src = r"entity Order {
  total: int = 0
  derived doubled = let t = total in t + t
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    let EntityItem::Derived(d) = &e.items[1] else {
        panic!("expected Derived in items[1]");
    };
    assert_eq!(d.name, "doubled");
}

/// derived fields can also live in system bodies.
#[test]
fn system_derived_field() {
    let src = r"system Shop(orders: Store<Order>) {
  derived order_count = 42
}";
    let prog = parse_program(src);
    let TopDecl::System(s) = &prog.decls[0] else {
        panic!("expected System");
    };
    assert_eq!(s.items.len(), 1);
    let SystemItem::Derived(d) = &s.items[0] else {
        panic!("expected Derived in items[0]");
    };
    assert_eq!(d.name, "order_count");
}

/// `derived` outside an entity or system body
/// is rejected at the top level with `DERIVED_INVALID_SCOPE`.
#[test]
fn derived_at_top_level_rejected() {
    let src = "derived nope = 1";
    let err = parse_program_err(src);
    assert!(
        format!("{err:?}").contains("derived"),
        "expected an error mentioning `derived`, got: {err:?}"
    );
}

/// an `invariant NAME { EXPR }` clause in
/// an entity body parses as an `InvariantDecl` and lives alongside
/// fields, derived fields, and actions.
#[test]
fn entity_invariant_decl() {
    let src = r"entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    assert_eq!(e.items.len(), 2);
    let EntityItem::Invariant(inv) = &e.items[1] else {
        panic!("expected Invariant in items[1], got: {:?}", e.items[1]);
    };
    assert_eq!(inv.name, "non_negative");
}

/// multiple invariants per scope.
#[test]
fn entity_multiple_invariants() {
    let src = r"entity Account {
  balance: int = 0
  is_frozen: bool = false
  invariant non_negative { balance >= 0 }
  invariant frozen_zero { is_frozen implies balance == 0 }
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    let inv_count = e
        .items
        .iter()
        .filter(|i| matches!(i, EntityItem::Invariant(_)))
        .count();
    assert_eq!(inv_count, 2);
}

/// invariants can also live in system bodies.
#[test]
fn system_invariant_decl() {
    let src = r"system Banking(accounts: Store<Account>) {
  invariant solvent { all a: Account | a.balance >= 0 }
}";
    let prog = parse_program(src);
    let TopDecl::System(s) = &prog.decls[0] else {
        panic!("expected System");
    };
    let SystemItem::Invariant(inv) = &s.items[0] else {
        panic!("expected Invariant in items[0]");
    };
    assert_eq!(inv.name, "solvent");
}

/// invariants cannot take parameters.
#[test]
fn entity_invariant_with_params_rejected() {
    let src = r"entity X {
  balance: int = 0
  invariant solvent(min: int) { balance >= min }
}";
    let err = parse_program_err(src);
    let msg = format!("{err:?}");
    assert!(
        msg.contains("invariant") || msg.contains("parameter") || msg.contains('('),
        "expected an error about invariant parameters, got: {err:?}"
    );
}

// ── fsm declarations () ──────────────────────────

/// a basic fsm declaration parses with one
/// non-terminal row plus a terminal row.
#[test]
fn entity_fsm_basic() {
    let src = r"entity Order {
  status: OrderStatus = @cart
  fsm status {
@cart -> @placed
@placed ->
  }
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    let EntityItem::Fsm(fsm) = &e.items[1] else {
        panic!("expected Fsm in items[1], got: {:?}", e.items[1]);
    };
    assert_eq!(fsm.field, "status");
    assert_eq!(fsm.rows.len(), 2);
    assert_eq!(fsm.rows[0].from, "cart");
    assert_eq!(fsm.rows[0].targets, vec!["placed".to_owned()]);
    assert_eq!(fsm.rows[1].from, "placed");
    assert!(fsm.rows[1].targets.is_empty());
}

/// a row with multiple targets via `|`.
#[test]
fn entity_fsm_multiple_targets() {
    let src = r"entity Order {
  status: OrderStatus = @cart
  fsm status {
@cart -> @placed | @cancelled
@placed -> @paid | @cancelled
@paid ->
@cancelled ->
  }
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    let EntityItem::Fsm(fsm) = &e.items[1] else {
        panic!("expected Fsm");
    };
    assert_eq!(fsm.rows.len(), 4);
    assert_eq!(fsm.rows[0].targets, vec!["placed", "cancelled"]);
    assert_eq!(fsm.rows[1].targets, vec!["paid", "cancelled"]);
    assert!(fsm.rows[2].targets.is_empty());
    assert!(fsm.rows[3].targets.is_empty());
}

/// multiple fsms per entity, one per field.
#[test]
fn entity_multiple_fsms() {
    let src = r"entity Document {
  status: DocStatus = @draft
  review: ReviewState = @pending
  fsm status {
@draft -> @published
@published ->
  }
  fsm review {
@pending -> @approved
@approved ->
  }
}";
    let prog = parse_program(src);
    let TopDecl::Entity(e) = &prog.decls[0] else {
        panic!("expected Entity");
    };
    let fsm_count = e
        .items
        .iter()
        .filter(|i| matches!(i, EntityItem::Fsm(_)))
        .count();
    assert_eq!(fsm_count, 2);
}

/// `fsm` declarations may also live on direct system fields.
#[test]
fn fsm_in_system_parses() {
    let src = r"system S(orders: Store<Order>) {
  status: OrderStatus = @cart
  fsm status {
@cart -> @placed
@placed ->
  }
}";
    let prog = parse_program(src);
    let TopDecl::System(s) = &prog.decls[0] else {
        panic!("expected System");
    };
    let SystemItem::Fsm(fsm) = &s.items[1] else {
        panic!("expected Fsm in items[1]");
    };
    assert_eq!(fsm.field, "status");
    assert_eq!(fsm.rows.len(), 2);
}

/// `use Entity` inside system body is rejected with
/// a migration diagnostic.
#[test]
fn use_entity_rejected_in_system() {
    let src = r"system S {
  use Order
}";
    let err = parse_program_err(src);
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Store<T>") || msg.contains("replaced"),
        "expected migration diagnostic for `use Entity`, got: {err:?}"
    );
}

#[test]
fn system_decl() {
    let src = r"system Commerce(orders: Store<Order>) {
  command pay(order_id: identity) {
    choose o: Order where o.id == order_id {
      o.submit()
    }
  }
}";
    let prog = parse_program(src);
    if let TopDecl::System(s) = &prog.decls[0] {
        assert_eq!(s.name, "Commerce");
        assert_eq!(s.params.len(), 1);
        assert_eq!(s.params[0].name, "orders");
        assert_eq!(s.params[0].entity_type, "Order");
        assert_eq!(s.items.len(), 1);
    } else {
        panic!("expected System");
    }
}

#[test]
fn interface_decl() {
    let src = r"interface NotificationBackend {
  command send(recipient: string, body: string) -> string
  query delivery_count() -> int
}";
    let prog = parse_program(src);
    let TopDecl::Interface(i) = &prog.decls[0] else {
        panic!("expected Interface");
    };
    assert_eq!(i.name, "NotificationBackend");
    assert_eq!(i.items.len(), 2);
    assert!(matches!(i.items[0], crate::ast::InterfaceItem::Command(_)));
    assert!(matches!(i.items[1], crate::ast::InterfaceItem::QuerySig(_)));
}

#[test]
fn system_decl_with_implements() {
    let src = r"system SlackAdapter(users: Store<User>) implements NotificationBackend {
  command send(recipient: string, body: string) -> string
  query delivery_count() = 0
}";
    let prog = parse_program(src);
    let TopDecl::System(s) = &prog.decls[0] else {
        panic!("expected System");
    };
    assert_eq!(s.name, "SlackAdapter");
    assert_eq!(s.implements.as_deref(), Some("NotificationBackend"));
}

#[test]
fn pred_decl() {
    let src = "pred non_negative(o: Order) = o.total >= 0";
    let prog = parse_program(src);
    if let TopDecl::Pred(p) = &prog.decls[0] {
        assert_eq!(p.name, "non_negative");
        assert_eq!(p.params.len(), 1);
    } else {
        panic!("expected Pred");
    }
}

#[test]
fn prop_for() {
    let src = "prop safe for Commerce = always true";
    let prog = parse_program(src);
    if let TopDecl::Prop(p) = &prog.decls[0] {
        assert_eq!(p.name, "safe");
        assert_eq!(p.systems.len(), 1);
    } else {
        panic!("expected Prop");
    }
}

#[test]
fn verify_decl() {
    let src = r"verify safety_check {
  assume {
store orders: Order[0..500]
let commerce = Commerce { orders: orders }
  }
  assert always true
}";
    let prog = parse_program(src);
    if let TopDecl::Verify(v) = &prog.decls[0] {
        assert_eq!(v.name, "safety_check");
        assert!(v.assume_block.is_some());
        assert_eq!(v.asserts.len(), 1);
    } else {
        panic!("expected Verify");
    }
}

#[test]
fn verify_decl_depth_is_non_negative() {
    let prog = parse_program("verify bounded [depth: 7] { assert true }");
    if let TopDecl::Verify(v) = &prog.decls[0] {
        assert_eq!(v.depth, Some(7));
    } else {
        panic!("expected Verify");
    }

    let err = parse_program_err("verify bounded [depth: -1] { assert true }");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("non-negative integer"),
        "expected non-negative depth diagnostic, got: {err:?}"
    );
}

/// `for System[0..N]` on verify is rejected.
#[test]
fn verify_for_system_rejected() {
    let src = r"verify safety for Commerce[0..500] { assert true }";
    let err = parse_program_err(src);
    let msg = format!("{err:?}");
    assert!(
        msg.contains("replaced") || msg.contains("store"),
        "expected migration diagnostic, got: {err:?}"
    );
}

#[test]
fn theorem_decl() {
    let src = r"theorem order_safety for Commerce
  invariant all o: Order | o.total >= 0 {
  show always true
}";
    let prog = parse_program(src);
    if let TopDecl::Theorem(t) = &prog.decls[0] {
        assert_eq!(t.name, "order_safety");
        assert_eq!(t.invariants.len(), 1);
        assert_eq!(t.shows.len(), 1);
        assert!(t.by_file.is_none());
    } else {
        panic!("expected Theorem");
    }
}

#[test]
fn theorem_expr_form() {
    let src = r"theorem no_overdraft = always true";
    let prog = parse_program(src);
    if let TopDecl::Theorem(t) = &prog.decls[0] {
        assert_eq!(t.name, "no_overdraft");
        assert_eq!(t.shows.len(), 1);
        assert!(t.by_file.is_none());
    } else {
        panic!("expected Theorem");
    }
}

#[test]
fn theorem_with_by() {
    let src = r#"theorem crypto_safe = always true by "proofs/crypto.agda""#;
    let prog = parse_program(src);
    if let TopDecl::Theorem(t) = &prog.decls[0] {
        assert_eq!(t.name, "crypto_safe");
        assert_eq!(t.by_file, Some("proofs/crypto.agda".to_string()));
    } else {
        panic!("expected Theorem");
    }
}

#[test]
fn axiom_decl() {
    let src = r"axiom max_accounts = true";
    let prog = parse_program(src);
    if let TopDecl::Axiom(a) = &prog.decls[0] {
        assert_eq!(a.name, "max_accounts");
        assert!(a.by_file.is_none());
    } else {
        panic!("expected Axiom");
    }
}

#[test]
fn axiom_with_by() {
    let src = r#"axiom crypto = true by "proofs/crypto.agda""#;
    let prog = parse_program(src);
    if let TopDecl::Axiom(a) = &prog.decls[0] {
        assert_eq!(a.name, "crypto");
        assert_eq!(a.by_file, Some("proofs/crypto.agda".to_string()));
    } else {
        panic!("expected Axiom");
    }
}

#[test]
fn lemma_decl() {
    let src = r"lemma foo {
  a implies a
}";
    let prog = parse_program(src);
    if let TopDecl::Lemma(l) = &prog.decls[0] {
        assert_eq!(l.name, "foo");
        assert_eq!(l.body.len(), 1);
    } else {
        panic!("expected Lemma");
    }
}

// ── assume { } blocks on verify/theorem/lemma ──────────

/// A `verify` block with an `assume { fair X; strong fair Y }` block
/// parses into a `VerifyDecl` with `assume_block: Some(AssumeBlock {... })`.
#[test]
fn verify_decl_with_assume_block_fair() {
    let src = r"verify safety_check {
  assume {
store orders: Order[0..500]
let commerce = Commerce { orders: orders }
fair Commerce::mark_paid
strong fair Commerce::ship_order
  }
  assert always true
}";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    let ab = v
        .assume_block
        .as_ref()
        .expect("verify should have an assume block");
    // store + let + fair + strong fair = 4 items
    assert_eq!(ab.items.len(), 4);
    assert!(matches!(&ab.items[0], AssumeItem::Store(_)));
    assert!(matches!(&ab.items[1], AssumeItem::Let(_)));
    match &ab.items[2] {
        AssumeItem::Fair { path, .. } => {
            assert_eq!(
                path.segments,
                vec!["Commerce".to_owned(), "mark_paid".to_owned()]
            );
        }
        other => panic!("expected Fair, got {other:?}"),
    }
    match &ab.items[3] {
        AssumeItem::StrongFair { path, .. } => {
            assert_eq!(
                path.segments,
                vec!["Commerce".to_owned(), "ship_order".to_owned()]
            );
        }
        other => panic!("expected StrongFair, got {other:?}"),
    }
    assert_eq!(v.asserts.len(), 1);
}

/// `assume { stutter }` parses as a `Stutter` item.
#[test]
fn verify_assume_stutter_item() {
    let src = r"verify s {
  assume {
store es: E[0..3]
let sys = Sys { es: es }
stutter
fair Sys::tick
  }
  assert always true
}";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    let ab = v.assume_block.as_ref().unwrap();
    // store + let + stutter + fair = 4
    assert_eq!(ab.items.len(), 4);
    assert!(matches!(&ab.items[2], AssumeItem::Stutter { .. }));
    assert!(matches!(&ab.items[3], AssumeItem::Fair { .. }));
}

/// `assume { no stutter }` parses as a `NoStutter` item.
#[test]
fn verify_assume_no_stutter_item() {
    let src = r"verify s {
  assume {
store es: E[0..3]
let sys = Sys { es: es }
no stutter
fair Sys::tick
  }
  assert always true
}";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    let ab = v.assume_block.as_ref().unwrap();
    assert!(matches!(&ab.items[2], AssumeItem::NoStutter { .. }));
}

/// `assume {; }` items can be separated by `;` (the new statement
/// separator from ), as well as by newlines.
#[test]
fn verify_assume_semicolon_separator() {
    let src = "verify s { assume { store es: E[0..3]; let sys = Sys { es: es }; fair Sys::a; fair Sys::b; no stutter } assert true }";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    let ab = v.assume_block.as_ref().unwrap();
    // store + let + fair + fair + no stutter = 5
    assert_eq!(ab.items.len(), 5);
}

#[test]
fn verify_assume_proc_bound_item() {
    let src = r"verify s {
  assume {
store es: E[0..3]
let shop = Shop { es: es }
proc shop.fulfill[0..2]
  }
  assert true
}";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    let ab = v.assume_block.as_ref().unwrap();
    assert_eq!(ab.items.len(), 3);
    match &ab.items[2] {
        AssumeItem::Proc(pd) => {
            assert_eq!(
                pd.path.segments,
                vec!["shop".to_owned(), "fulfill".to_owned()]
            );
            assert_eq!(pd.lo, 0);
            assert_eq!(pd.hi, 2);
        }
        other => panic!("expected Proc bound, got {other:?}"),
    }
}

/// `assume { stutter; no stutter }` is rejected with `ASSUME_STUTTER_CONFLICT`.
#[test]
fn verify_assume_stutter_conflict_rejected() {
    let src = r"verify s {
  assume {
stutter
no stutter
  }
  assert true
}";
    let err = parse_program_err(src);
    assert!(
        err.to_string().contains("stutter"),
        "expected stutter conflict diagnostic, got: {err}"
    );
}

/// A bare `verify` block (no `assume`) parses with `assume_block: None`.
#[test]
fn verify_decl_no_assume_block() {
    let src = r"verify s { assert true }";
    let prog = parse_program(src);
    let v = match &prog.decls[0] {
        TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    assert!(v.assume_block.is_none());
}

/// Theorem can also carry an `assume {... }` block.
#[test]
fn theorem_decl_with_assume_block() {
    let src = r"theorem t for Sys {
  assume { fair Sys::tick }
  show always true
}";
    let prog = parse_program(src);
    let t = match &prog.decls[0] {
        TopDecl::Theorem(t) => t,
        other => panic!("expected Theorem, got {other:?}"),
    };
    let ab = t.assume_block.as_ref().unwrap();
    assert_eq!(ab.items.len(), 1);
}

/// Lemma can also carry an `assume {... }` block.
#[test]
fn lemma_decl_with_assume_block() {
    let src = r"lemma l {
  assume { fair Sys::tick }
  always true
}";
    let prog = parse_program(src);
    let l = match &prog.decls[0] {
        TopDecl::Lemma(l) => l,
        other => panic!("expected Lemma, got {other:?}"),
    };
    let ab = l.assume_block.as_ref().unwrap();
    assert_eq!(ab.items.len(), 1);
    assert_eq!(l.body.len(), 1);
}

/// Per REPLACED, `fair event` modifier syntax on system event
/// declarations is rejected with `LEGACY_FAIR_EVENT_REJECTED`.
#[test]
fn legacy_fair_event_modifier_rejected() {
    let src = r"system S(jobs: Store<Job>) {
  fair event tick() {}
}";
    let err = parse_program_err(src);
    assert!(
        err.to_string().contains("fair"),
        "expected legacy fair-event diagnostic, got: {err}"
    );
}

/// Same for `strong fair event`.
#[test]
fn legacy_strong_fair_event_modifier_rejected() {
    let src = r"system S(jobs: Store<Job>) {
  strong fair event tick() {}
}";
    let err = parse_program_err(src);
    assert!(
        err.to_string().contains("strong"),
        "expected legacy strong-fair-event diagnostic, got: {err}"
    );
}

#[test]
fn scene_with_blocks() {
    let src = r"scene payment_test {
  given {
store orders: Order[0..2]
let commerce = Commerce { orders: orders }
let o = one Order in orders where o.total == 100
  }
  when {
commerce.pay(o.id)
  }
  then {
assert o.status == @Paid
  }
}";
    let prog = parse_program(src);
    if let TopDecl::Scene(s) = &prog.decls[0] {
        assert_eq!(s.name, "payment_test");
        assert_eq!(s.items.len(), 3);
    } else {
        panic!("expected Scene");
    }
}

#[test]
fn contract_parsing() {
    let src = r"entity Order {
  action submit()
requires status == @Pending
requires total > 0
ensures status == @AwaitingPayment {
status' = @AwaitingPayment
  }
}";
    let prog = parse_program(src);
    if let TopDecl::Entity(e) = &prog.decls[0] {
        if let EntityItem::Action(a) = &e.items[0] {
            assert_eq!(a.contracts.len(), 3);
        } else {
            panic!("expected Action");
        }
    } else {
        panic!("expected Entity");
    }
}

#[test]
fn create_block() {
    let src = r"system Billing(intents: Store<PaymentIntent>) {
  action open_intent(order_id: identity) {
create PaymentIntent {
  order_id = order_id
  amount = 0
  status = @Opened
}
  }
}";
    let prog = parse_program(src);
    if let TopDecl::System(s) = &prog.decls[0] {
        if let SystemItem::Action(e) = &s.items[0] {
            assert_eq!(e.items.len(), 1);
            assert!(matches!(e.items[0], EventItem::Create(_)));
        } else {
            panic!("expected Action");
        }
    } else {
        panic!("expected System");
    }
}

// ── Match expression tests ──────────────────────────────────────

#[test]
fn match_simple() {
    let e = parse_expr("match s { Pending => 1 Confirmed => 2 }");
    if let ExprKind::Match(scrut, arms) = &e.kind {
        assert!(matches!(scrut.kind, ExprKind::Var(ref s) if s == "s"));
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].pattern, Pattern::Var(ref s, _) if s == "Pending"));
        assert!(matches!(arms[1].pattern, Pattern::Var(ref s, _) if s == "Confirmed"));
        assert!(arms[0].guard.is_none());
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_wildcard() {
    let e = parse_expr("match x { _ => 0 }");
    if let ExprKind::Match(_, arms) = &e.kind {
        assert_eq!(arms.len(), 1);
        assert!(matches!(arms[0].pattern, Pattern::Wild(_)));
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_record_pattern() {
    let e = parse_expr("match s { Circle { radius: r } => r }");
    if let ExprKind::Match(_, arms) = &e.kind {
        assert_eq!(arms.len(), 1);
        if let Pattern::Ctor(name, fields, has_rest, _) = &arms[0].pattern {
            assert_eq!(name, "Circle");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].name, "radius");
            assert!(!has_rest);
        } else {
            panic!("expected Ctor pattern");
        }
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_guard() {
    let e = parse_expr("match s { Circle { radius: r } if r > 100 => 1 _ => 0 }");
    if let ExprKind::Match(_, arms) = &e.kind {
        assert_eq!(arms.len(), 2);
        assert!(arms[0].guard.is_some());
        assert!(arms[1].guard.is_none());
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_guard_without_pattern_uses_wildcard() {
    let e = parse_expr("match x { if x < 0 => 0 - x _ => x }");
    if let ExprKind::Match(_, arms) = &e.kind {
        assert_eq!(arms.len(), 2);
        assert!(arms[0].guard.is_some());
        assert!(matches!(arms[0].pattern, Pattern::Wild(_)));
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_or_pattern() {
    let e = parse_expr("match s { Pending | Confirmed => 1 _ => 0 }");
    if let ExprKind::Match(_, arms) = &e.kind {
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].pattern, Pattern::Or(_, _, _)));
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_rest_pattern() {
    let e = parse_expr("match s { Circle { radius: r, .. } => r }");
    if let ExprKind::Match(_, arms) = &e.kind {
        if let Pattern::Ctor(_, _, has_rest, _) = &arms[0].pattern {
            assert!(has_rest);
        } else {
            panic!("expected Ctor pattern");
        }
    } else {
        panic!("expected Match");
    }
}

#[test]
fn match_field_access_scrutinee() {
    let e = parse_expr("match o.status { Pending => 1 }");
    if let ExprKind::Match(scrut, _) = &e.kind {
        assert!(matches!(scrut.kind, ExprKind::Field(_, ref f) if f == "status"));
    } else {
        panic!("expected Match");
    }
}

// ── Generic type reference tests () ─────────────────────────

#[test]
fn type_ref_generic_set() {
    let src = "fn ids(s: Set<int>): bool = true";
    let prog = parse_program(src);
    if let TopDecl::Fn(f) = &prog.decls[0] {
        match &f.params[0].ty.kind {
            TypeRefKind::Param(name, args) => {
                assert_eq!(name, "Set");
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0].kind, TypeRefKind::Simple(ref s) if s == "int"));
            }
            other => panic!("expected Param, got {other:?}"),
        }
    } else {
        panic!("expected Fn");
    }
}

#[test]
fn type_ref_generic_map() {
    let src = "fn lookup(m: Map<string, bool>): bool = true";
    let prog = parse_program(src);
    if let TopDecl::Fn(f) = &prog.decls[0] {
        match &f.params[0].ty.kind {
            TypeRefKind::Param(name, args) => {
                assert_eq!(name, "Map");
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0].kind, TypeRefKind::Simple(ref s) if s == "string"));
                assert!(matches!(args[1].kind, TypeRefKind::Simple(ref s) if s == "bool"));
            }
            other => panic!("expected Param, got {other:?}"),
        }
    } else {
        panic!("expected Fn");
    }
}

#[test]
fn type_ref_nested_generics() {
    let src = "fn nested(s: Set<Set<int>>): bool = true";
    let prog = parse_program(src);
    if let TopDecl::Fn(f) = &prog.decls[0] {
        match &f.params[0].ty.kind {
            TypeRefKind::Param(name, args) => {
                assert_eq!(name, "Set");
                assert_eq!(args.len(), 1);
                match &args[0].kind {
                    TypeRefKind::Param(inner_name, inner_args) => {
                        assert_eq!(inner_name, "Set");
                        assert_eq!(inner_args.len(), 1);
                        assert!(
                            matches!(inner_args[0].kind, TypeRefKind::Simple(ref s) if s == "int")
                        );
                    }
                    other => panic!("expected nested Param, got {other:?}"),
                }
            }
            other => panic!("expected Param, got {other:?}"),
        }
    } else {
        panic!("expected Fn");
    }
}

// ── Mut ref param tests () ───────────────────────────────────

#[test]
fn action_mut_ref_param() {
    let src = r"entity Account {
  balance: int

  action transfer[mut to: Account](amount: int)
requires balance >= amount {
balance' = balance - amount
  }
}";
    let prog = parse_program(src);
    if let TopDecl::Entity(e) = &prog.decls[0] {
        if let EntityItem::Action(a) = &e.items[1] {
            assert_eq!(a.name, "transfer");
            assert_eq!(a.ref_params.len(), 1);
            assert_eq!(a.ref_params[0].name, "to");
            assert!(matches!(&a.ref_params[0].ty.kind, TypeRefKind::Simple(n) if n == "Account"));
            assert!(a.ref_params[0].mutable);
            assert_eq!(a.params.len(), 1);
            assert_eq!(a.params[0].name, "amount");
            assert!(!a.params[0].mutable);
        } else {
            panic!("expected Action");
        }
    } else {
        panic!("expected Entity");
    }
}

#[test]
fn action_non_mut_ref_param() {
    let src = r"entity Account {
  balance: int

  action check[other: Account]() requires true {
balance' = balance
  }
}";
    let prog = parse_program(src);
    if let TopDecl::Entity(e) = &prog.decls[0] {
        if let EntityItem::Action(a) = &e.items[1] {
            assert_eq!(a.ref_params.len(), 1);
            assert!(!a.ref_params[0].mutable);
        } else {
            panic!("expected Action");
        }
    } else {
        panic!("expected Entity");
    }
}

#[test]
fn field_type_generic_collection() {
    let src = r"entity Warehouse {
  items: Set<identity>
  prices: Map<identity, int>
}";
    let prog = parse_program(src);
    if let TopDecl::Entity(e) = &prog.decls[0] {
        if let EntityItem::Field(f) = &e.items[0] {
            assert_eq!(f.name, "items");
            match &f.ty.kind {
                TypeRefKind::Param(name, args) => {
                    assert_eq!(name, "Set");
                    assert_eq!(args.len(), 1);
                }
                other => panic!("expected Param, got {other:?}"),
            }
        } else {
            panic!("expected Field");
        }
        if let EntityItem::Field(f) = &e.items[1] {
            assert_eq!(f.name, "prices");
            match &f.ty.kind {
                TypeRefKind::Param(name, args) => {
                    assert_eq!(name, "Map");
                    assert_eq!(args.len(), 2);
                }
                other => panic!("expected Param, got {other:?}"),
            }
        } else {
            panic!("expected Field");
        }
    } else {
        panic!("expected Entity");
    }
}

// ── Map update and index tests () ────────────────────────────

#[test]
fn map_update() {
    let e = parse_expr("m[k := v]");
    match &e.kind {
        ExprKind::MapUpdate(m, k, v) => {
            assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
            assert!(matches!(k.kind, ExprKind::Var(ref s) if s == "k"));
            assert!(matches!(v.kind, ExprKind::Var(ref s) if s == "v"));
        }
        other => panic!("expected MapUpdate, got {other:?}"),
    }
}

#[test]
fn map_index() {
    let e = parse_expr("m[k]");
    match &e.kind {
        ExprKind::Index(m, k) => {
            assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
            assert!(matches!(k.kind, ExprKind::Var(ref s) if s == "k"));
        }
        other => panic!("expected Index, got {other:?}"),
    }
}

#[test]
fn map_update_chained() {
    let e = parse_expr("m[a := x][b := y]");
    match &e.kind {
        ExprKind::MapUpdate(inner, b, y) => {
            assert!(matches!(b.kind, ExprKind::Var(ref s) if s == "b"));
            assert!(matches!(y.kind, ExprKind::Var(ref s) if s == "y"));
            match &inner.kind {
                ExprKind::MapUpdate(m, a, x) => {
                    assert!(matches!(m.kind, ExprKind::Var(ref s) if s == "m"));
                    assert!(matches!(a.kind, ExprKind::Var(ref s) if s == "a"));
                    assert!(matches!(x.kind, ExprKind::Var(ref s) if s == "x"));
                }
                other => panic!("expected inner MapUpdate, got {other:?}"),
            }
        }
        other => panic!("expected MapUpdate, got {other:?}"),
    }
}

// ── Set comprehension tests () ───────────────────────────────

#[test]
fn set_comp_simple() {
    let e = parse_expr("{ a: Account where a.status == @Frozen }");
    match &e.kind {
        ExprKind::SetComp {
            projection,
            var,
            domain,
            filter,
        } => {
            assert!(projection.is_none());
            assert_eq!(var, "a");
            assert!(matches!(&domain.kind, TypeRefKind::Simple(ref n) if n == "Account"));
            assert!(matches!(filter.kind, ExprKind::Eq(_, _)));
        }
        other => panic!("expected SetComp, got {other:?}"),
    }
}

#[test]
fn set_comp_projection() {
    let e = parse_expr("{ a.balance | a: Account where a.balance > 0 }");
    match &e.kind {
        ExprKind::SetComp {
            projection,
            var,
            domain,
            filter,
        } => {
            assert!(projection.is_some());
            let proj = projection.as_ref().unwrap();
            assert!(matches!(&proj.kind, ExprKind::Field(_, ref f) if f == "balance"));
            assert_eq!(var, "a");
            assert!(matches!(&domain.kind, TypeRefKind::Simple(ref n) if n == "Account"));
            assert!(matches!(filter.kind, ExprKind::Gt(_, _)));
        }
        other => panic!("expected SetComp, got {other:?}"),
    }
}

#[test]
fn set_comp_cardinality() {
    let e = parse_expr("#{ a: Account where a.balance > 0 }");
    match &e.kind {
        ExprKind::Card(inner) => {
            assert!(matches!(
                &inner.kind,
                ExprKind::SetComp {
                    projection: None,
                    ..
                }
            ));
        }
        other => panic!("expected Card(SetComp), got {other:?}"),
    }
}

// ── Collection literal recognition () ────────────────────────

#[test]
fn collection_literal_set() {
    let e = parse_expr("Set(1, 2, 3)");
    match &e.kind {
        ExprKind::Call(callee, args) => {
            assert!(matches!(&callee.kind, ExprKind::Var(ref s) if s == "Set"));
            assert_eq!(args.len(), 3);
            assert!(matches!(args[0].kind, ExprKind::Int(1)));
            assert!(matches!(args[1].kind, ExprKind::Int(2)));
            assert!(matches!(args[2].kind, ExprKind::Int(3)));
        }
        other => panic!("expected Call(Var(Set), [1,2,3]), got {other:?}"),
    }
}

// ── Removed keyword detection tests ──────────────────────────

fn try_parse(src: &str) -> Result<Program, ParseError> {
    let tokens = lex::lex(src).expect("lex error");
    let mut parser = Parser::new(tokens);
    parser.parse_program()
}

#[test]
fn removed_field_keyword_in_entity() {
    let err = try_parse("entity Order { field status: int }").unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("field"), "should mention 'field': {msg}");
}

#[test]
fn removed_import_keyword() {
    let err = try_parse(r#"import "billing.ab" as Billing"#).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("import"), "should mention 'import': {msg}");
}

#[test]
fn removed_proof_keyword() {
    let err = try_parse("proof safety for S { show always true }").unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("proof"), "should mention 'proof': {msg}");
}

#[test]
fn removed_uses_keyword() {
    let err = try_parse("system S { uses Order }").unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("uses"), "should mention 'uses': {msg}");
}

// ── Recovery and multi-error tests ──────────────────────────

fn try_parse_recovering(src: &str) -> (Program, Vec<ParseError>) {
    let tokens = lex::lex(src).expect("lex error");
    let mut parser = Parser::new(tokens);
    parser.parse_program_recovering()
}

#[test]
fn recovery_reports_multiple_errors() {
    let src = "import x\ntype Status = A | B\nimport y\nentity Order { id: identity }";
    let (program, errors) = try_parse_recovering(src);
    // Two import errors, but type and entity should parse successfully
    assert_eq!(errors.len(), 2, "should have 2 errors: {errors:?}");
    let valid_decl_count = program
        .decls
        .iter()
        .filter(|decl| !matches!(decl, TopDecl::Error(_)))
        .count();
    let error_decl_count = program
        .decls
        .iter()
        .filter(|decl| matches!(decl, TopDecl::Error(_)))
        .count();
    assert_eq!(valid_decl_count, 2, "should have 2 valid decls");
    assert_eq!(error_decl_count, 2, "should retain 2 error nodes");
}

#[test]
fn recovery_does_not_skip_valid_starter() {
    let src = "import x\nenum Status = A | B";
    let (program, errors) = try_parse_recovering(src);
    assert_eq!(errors.len(), 1, "one import error");
    let valid_decl_count = program
        .decls
        .iter()
        .filter(|decl| !matches!(decl, TopDecl::Error(_)))
        .count();
    assert_eq!(valid_decl_count, 1, "enum should be recovered");
    assert!(
        matches!(program.decls.first(), Some(TopDecl::Error(_))),
        "broken declaration should be retained as an error node"
    );
}

#[test]
fn recovery_retains_error_node_inside_system_body() {
    let src = r#"
system S {
  command ping()
  uses Order
  query ready() = true
}
"#;
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let (prog, errors) = parser.parse_program_recovering();
    assert!(
        !errors.is_empty(),
        "broken system body should report an error"
    );
    let TopDecl::System(sys) = &prog.decls[0] else {
        panic!("expected system decl");
    };
    assert!(
        sys.items
            .iter()
            .any(|item| matches!(item, SystemItem::Error(_))),
        "system body should retain an explicit error item"
    );
    assert!(
        sys.items
            .iter()
            .any(|item| matches!(item, SystemItem::Query(_))),
        "parser should recover and keep later valid system items"
    );
}

#[test]
fn recovery_retains_error_expr_inside_block() {
    let src = r#"
fn f(x: int): int {
  var y = ;
  y
}
"#;
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let (prog, errors) = parser.parse_program_recovering();
    assert!(
        !errors.is_empty(),
        "broken block item should report an error"
    );
    let TopDecl::Fn(f) = &prog.decls[0] else {
        panic!("expected fn decl");
    };
    let ExprKind::Block(items) = &f.body.kind else {
        panic!("expected block body");
    };
    assert!(
        items
            .iter()
            .any(|item| matches!(item.kind, ExprKind::Error(_))),
        "block should retain an explicit error expression"
    );
}

#[test]
fn parse_string_recovering_returns_partial_program_and_errors() {
    let src = "import x\nenum Status = A | B";
    let output = parse_string_recovering(src).expect("lex");
    assert_eq!(
        output.errors.len(),
        1,
        "should retain the import parse error"
    );
    assert!(
        output
            .program
            .decls
            .iter()
            .any(|decl| matches!(decl, TopDecl::Type(ty) if ty.name == "Status")),
        "recovering parse should keep later valid declarations"
    );
}

/// Extract the help text from a `ParseError`, if present.
fn extract_help(err: &ParseError) -> Option<&str> {
    match err {
        ParseError::Expected { help, .. } => help.as_deref(),
        ParseError::General { help, .. } => help.as_deref(),
        ParseError::UnexpectedEof { .. } => None,
    }
}

#[test]
fn import_help_text_content() {
    let err = try_parse(r#"import "billing.ab" as Billing"#).unwrap_err();
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("module"),
        "help should mention 'module': {help}"
    );
    assert!(
        help.contains("include"),
        "help should mention 'include': {help}"
    );
}

#[test]
fn field_help_text_content() {
    let err = try_parse("entity Order { field status: int }").unwrap_err();
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("name: Type"),
        "help should show bare field syntax: {help}"
    );
}

#[test]
fn verify_body_contextual_help() {
    let err = try_parse("verify test { show always true }").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("assert"),
        "should expect 'assert' in verify body: {msg}"
    );
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("assert"),
        "help should mention assert statements: {help}"
    );
}

#[test]
fn theorem_assert_instead_of_show() {
    let err = try_parse("theorem t for S { assert always true }").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("show"),
        "should suggest 'show' instead of 'assert': {msg}"
    );
    let help = extract_help(&err).expect("should have help");
    assert!(help.contains("show"), "help should mention 'show': {help}");
}

#[test]
fn scene_body_contextual_help() {
    let err = try_parse("scene s { verify true }").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("given") || msg.contains("when") || msg.contains("then"),
        "should mention scene sections: {msg}"
    );
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("given"),
        "help should mention 'given': {help}"
    );
}

#[test]
fn action_body_assert_instead_of_requires() {
    let err = try_parse("system S { action e() { assert true } }").unwrap_err();
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("requires"),
        "help should suggest 'requires': {help}"
    );
}

#[test]
fn source_step_syntax_is_rejected() {
    let err = try_parse("system S { step e() { } }").unwrap_err();
    let help = extract_help(&err).expect("should have help");
    assert!(
        help.contains("Use `action`"),
        "help should point to action syntax: {help}"
    );
}

// ──: enum / struct / type alias tests ───────────────────

#[test]
fn enum_simple() {
    let prog = parse_program("enum Status = Active | Inactive | Suspended");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "Status");
        assert_eq!(t.variants.len(), 3);
        assert!(matches!(&t.variants[0], TypeVariant::Simple { name, .. } if name == "Active"));
        assert!(matches!(&t.variants[1], TypeVariant::Simple { name, .. } if name == "Inactive"));
        assert!(matches!(&t.variants[2], TypeVariant::Simple { name, .. } if name == "Suspended"));
    } else {
        panic!("expected Type from enum");
    }
}

#[test]
fn enum_adt_with_record_variants() {
    let src = "enum Shape = Circle { radius: real } | Rectangle { width: real, height: real }";
    let prog = parse_program(src);
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "Shape");
        assert_eq!(t.variants.len(), 2);
        assert!(
            matches!(&t.variants[0], TypeVariant::Record { name, fields, .. } if name == "Circle" && fields.len() == 1)
        );
        assert!(
            matches!(&t.variants[1], TypeVariant::Record { name, fields, .. } if name == "Rectangle" && fields.len() == 2)
        );
    } else {
        panic!("expected Type from enum");
    }
}

#[test]
fn struct_decl_test() {
    let src = "struct Address { street: string, city: string, zip: string }";
    let prog = parse_program(src);
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Record(r) = &prog.decls[0] {
        assert_eq!(r.name, "Address");
        assert_eq!(r.fields.len(), 3);
        assert_eq!(r.fields[0].name, "street");
        assert_eq!(r.fields[1].name, "city");
        assert_eq!(r.fields[2].name, "zip");
    } else {
        panic!("expected Record from struct");
    }
}

#[test]
fn type_alias_to_tuple() {
    let prog = parse_program("type Coord = (real, real)");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "Coord");
        assert!(matches!(&a.target.kind, TypeRefKind::Tuple(ts) if ts.len() == 2));
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn type_alias_to_collection() {
    let prog = parse_program("type Ids = Set<identity>");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "Ids");
        assert!(
            matches!(&a.target.kind, TypeRefKind::Param(name, ts) if name == "Set" && ts.len() == 1)
        );
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn type_alias_to_builtin() {
    let prog = parse_program("type Amount = real");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "Amount");
        assert!(matches!(&a.target.kind, TypeRefKind::Simple(name) if name == "real"));
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn enum_struct_type_default_private() {
    let src = r"enum Color = Red | Green | Blue
struct Point { x: real, y: real }
type Distance = real";
    let prog = parse_program(src);
    assert_eq!(prog.decls.len(), 3);
    if let TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "Color");
        assert_eq!(t.visibility, Visibility::Private);
        assert_eq!(t.variants.len(), 3);
    } else {
        panic!("expected Type from enum");
    }
    if let TopDecl::Record(r) = &prog.decls[1] {
        assert_eq!(r.name, "Point");
        assert_eq!(r.visibility, Visibility::Private);
        assert_eq!(r.fields.len(), 2);
    } else {
        panic!("expected Record from struct");
    }
    if let TopDecl::Alias(a) = &prog.decls[2] {
        assert_eq!(a.name, "Distance");
        assert_eq!(a.visibility, Visibility::Private);
    } else {
        panic!("expected Alias from type");
    }
}

#[test]
fn type_does_not_produce_enum() {
    // `type` with pipe-separated variants: type_ref() parses `Pending`
    // as a simple alias, leaving `| Paid` as trailing junk.
    let tokens = lex::lex("type OrderStatus = Pending | Paid").expect("lex");
    let mut parser = Parser::new(tokens);
    let (prog, errors) = parser.parse_program_recovering();
    // Should either error or produce an alias (not a multi-variant enum)
    let has_multi_variant = prog
        .decls
        .iter()
        .any(|d| matches!(d, TopDecl::Type(t) if t.variants.len() > 1));
    assert!(
        !has_multi_variant,
        "type with | should not produce multi-variant enum — use enum"
    );
    // The trailing `| Paid` should produce a parse error
    assert!(
        !errors.is_empty() || prog.decls.len() != 1,
        "type with | should produce errors or unexpected decls"
    );
}

#[test]
fn type_does_not_produce_record() {
    // `type Name { fields }` is not valid — use `struct`
    let tokens = lex::lex("type Address { street: string }").expect("lex");
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(
        result.is_err(),
        "type with {{ fields }} should be rejected — use struct"
    );
}

#[test]
fn type_alias_to_map() {
    let prog = parse_program("type Ledger = Map<identity, real>");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "Ledger");
        if let TypeRefKind::Param(name, ts) = &a.target.kind {
            assert_eq!(name, "Map");
            assert_eq!(ts.len(), 2);
        } else {
            panic!("expected Param type ref");
        }
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn type_alias_triple_tuple() {
    let prog = parse_program("type RGB = (int, int, int)");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "RGB");
        if let TypeRefKind::Tuple(ts) = &a.target.kind {
            assert_eq!(ts.len(), 3);
        } else {
            panic!("expected Tuple type ref");
        }
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn type_alias_function_type() {
    let prog = parse_program("type Handler = int -> bool");
    assert_eq!(prog.decls.len(), 1);
    if let TopDecl::Alias(a) = &prog.decls[0] {
        assert_eq!(a.name, "Handler");
        assert!(
            matches!(a.target.kind, TypeRefKind::Fn(_, _)),
            "expected function type, got {:?}",
            a.target.kind
        );
    } else {
        panic!("expected Alias, got {:?}", prog.decls[0]);
    }
}

#[test]
fn type_single_name_is_alias() {
    // type Status = Pending → alias (no backward compat for enums)
    // Use `enum Status = Pending` for single-variant enums.
    let prog = parse_program("type Status = Pending");
    match &prog.decls[0] {
        TopDecl::Alias(a) => {
            assert_eq!(a.name, "Status");
            assert!(
                matches!(a.target.kind, TypeRefKind::Simple(ref n) if n == "Pending"),
                "expected alias to Pending, got {:?}",
                a.target.kind
            );
        }
        other => panic!("expected Alias, got {other:?}"),
    }
}

#[test]
fn enum_rejects_brace_syntax() {
    let tokens = lex::lex("enum Point { x: int }").expect("lex");
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(result.is_err(), "enum with {{ fields }} should be rejected");
}

#[test]
fn struct_rejects_eq_syntax() {
    let tokens = lex::lex("struct Status = A | B").expect("lex");
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(result.is_err(), "struct with = should be rejected");
}

#[test]
fn type_alias_uppercase_function_type() {
    // type Predicate = User -> bool — User is uppercase non-builtin
    // but -> makes it a function type, so it must be an alias, not enum.
    let prog = parse_program("type Predicate = User -> bool");
    match &prog.decls[0] {
        TopDecl::Alias(a) => {
            assert_eq!(a.name, "Predicate");
            assert!(
                matches!(a.target.kind, TypeRefKind::Fn(_, _)),
                "expected function type, got {:?}",
                a.target.kind
            );
        }
        other => panic!("expected Alias, got {other:?}"),
    }
}

// ── fn contract tests ─────────────────────────────────────────────

#[test]
fn fn_no_contracts() {
    let prog = parse_program("fn double(x: int): int = x + x");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.name, "double");
            assert!(f.contracts.is_empty());
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_requires() {
    let prog = parse_program("fn gcd(a: int, b: int): int requires a > 0 requires b >= 0 { a }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.name, "gcd");
            assert_eq!(f.contracts.len(), 2);
            assert!(matches!(f.contracts[0], Contract::Requires { .. }));
            assert!(matches!(f.contracts[1], Contract::Requires { .. }));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_ensures() {
    let prog = parse_program("fn abs(x: int): int ensures result >= 0 { x }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.name, "abs");
            assert_eq!(f.contracts.len(), 1);
            assert!(matches!(f.contracts[0], Contract::Ensures { .. }));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_decreases_single() {
    let prog = parse_program("fn countdown(n: int): int decreases n { n }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.contracts.len(), 1);
            match &f.contracts[0] {
                Contract::Decreases { measures, star, .. } => {
                    assert_eq!(measures.len(), 1);
                    assert!(!star);
                }
                other => panic!("expected Decreases, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_decreases_lexicographic() {
    let prog = parse_program("fn ack(m: int, n: int): int decreases m, n { m }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.contracts.len(), 1);
            match &f.contracts[0] {
                Contract::Decreases { measures, star, .. } => {
                    assert_eq!(measures.len(), 2);
                    assert!(!star);
                }
                other => panic!("expected Decreases, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_decreases_star() {
    let prog = parse_program("fn f(n: int): int decreases * { n }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.contracts.len(), 1);
            match &f.contracts[0] {
                Contract::Decreases { measures, star, .. } => {
                    assert!(measures.is_empty());
                    assert!(star);
                }
                other => panic!("expected Decreases, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_all_contracts() {
    let prog = parse_program(
        "fn gcd(a: int, b: int): int requires a > 0 ensures result > 0 decreases b { a }",
    );
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.contracts.len(), 3);
            assert!(matches!(f.contracts[0], Contract::Requires { .. }));
            assert!(matches!(f.contracts[1], Contract::Ensures { .. }));
            assert!(matches!(f.contracts[2], Contract::Decreases { .. }));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_pure_form_no_contracts() {
    // Pure form with = body should still work
    let prog = parse_program("fn id(x: int): int = x");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.name, "id");
            assert!(f.contracts.is_empty());
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

// ── Imperative fn body tests ────────────────────────────────────

#[test]
fn fn_with_var_decl() {
    let prog = parse_program("fn f(x: int): int { var y = x + 1\ny }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.name, "f");
            match &f.body.kind {
                ExprKind::Block(items) => {
                    assert_eq!(items.len(), 2);
                    assert!(matches!(items[0].kind, ExprKind::VarDecl { .. }));
                    assert!(matches!(items[1].kind, ExprKind::Var(_)));
                }
                other => panic!("expected Block, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_while_loop() {
    let prog = parse_program("fn f(x: int): int { while x > 0 { x } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            // Single-item block with a while unwraps directly
            match &f.body.kind {
                ExprKind::While { cond, body, .. } => {
                    assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                    assert!(matches!(body.kind, ExprKind::Var(_)));
                }
                other => panic!("expected While, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_while_invariant_decreases() {
    let prog =
        parse_program("fn f(x: int): int { while x > 0 invariant x >= 0 decreases x { x } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => match &f.body.kind {
            ExprKind::While {
                contracts, cond, ..
            } => {
                assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                assert_eq!(contracts.len(), 2);
                assert!(matches!(contracts[0], Contract::Invariant { .. }));
                assert!(matches!(contracts[1], Contract::Decreases { .. }));
            }
            other => panic!("expected While, got {other:?}"),
        },
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_if_else() {
    let prog = parse_program("fn f(x: int): int { if x > 0 { x } else { 0 } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => match &f.body.kind {
            ExprKind::IfElse {
                cond,
                then_body,
                else_body,
            } => {
                assert!(matches!(cond.kind, ExprKind::Gt(_, _)));
                assert!(matches!(then_body.kind, ExprKind::Var(_)));
                assert!(else_body.is_some());
                assert!(matches!(else_body.as_ref().unwrap().kind, ExprKind::Int(0)));
            }
            other => panic!("expected IfElse, got {other:?}"),
        },
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_if_no_else() {
    let prog = parse_program("fn f(x: int): int { if x > 0 { x } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => match &f.body.kind {
            ExprKind::IfElse { else_body, .. } => {
                assert!(else_body.is_none());
            }
            other => panic!("expected IfElse, got {other:?}"),
        },
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_multiple_statements() {
    let prog = parse_program("fn f(x: int): int {\n  var a = 1\n  var b = 2\n  a + b\n}");
    match &prog.decls[0] {
        TopDecl::Fn(f) => match &f.body.kind {
            ExprKind::Block(items) => {
                assert_eq!(items.len(), 3);
                assert!(matches!(items[0].kind, ExprKind::VarDecl { .. }));
                assert!(matches!(items[1].kind, ExprKind::VarDecl { .. }));
                assert!(matches!(items[2].kind, ExprKind::Add(_, _)));
            }
            other => panic!("expected Block, got {other:?}"),
        },
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_var_typed() {
    let prog = parse_program("fn f(x: int): int { var y: int = 0\ny }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => match &f.body.kind {
            ExprKind::Block(items) => {
                assert_eq!(items.len(), 2);
                match &items[0].kind {
                    ExprKind::VarDecl { name, ty, .. } => {
                        assert_eq!(name, "y");
                        assert!(ty.is_some());
                    }
                    other => panic!("expected VarDecl, got {other:?}"),
                }
            }
            other => panic!("expected Block, got {other:?}"),
        },
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_with_else_if_chain() {
    let prog =
        parse_program("fn f(x: int): int { if x > 0 { 1 } else if x == 0 { 0 } else { 2 } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            match &f.body.kind {
                ExprKind::IfElse { else_body, .. } => {
                    // The else branch is another IfElse
                    let eb = else_body.as_ref().unwrap();
                    assert!(matches!(eb.kind, ExprKind::IfElse { .. }));
                }
                other => panic!("expected IfElse, got {other:?}"),
            }
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn fn_single_expr_body_unwraps() {
    // A block with a single non-VarDecl expression should unwrap
    let prog = parse_program("fn f(x: int): int { x + 1 }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert!(
                matches!(f.body.kind, ExprKind::Add(_, _)),
                "single-expr block should unwrap, got {:?}",
                f.body.kind
            );
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

// ── Refinement type tests ───────────────────────────────────────

#[test]
fn refinement_type_alias() {
    let prog = parse_program("type Positive = int { $ > 0 }");
    match &prog.decls[0] {
        TopDecl::Alias(a) => match &a.target.kind {
            TypeRefKind::Refine(base, pred) => {
                assert!(matches!(base.kind, TypeRefKind::Simple(ref n) if n == "int"));
                assert!(matches!(pred.kind, ExprKind::Gt(_, _)));
            }
            other => panic!("expected Refine, got {other:?}"),
        },
        other => panic!("expected Alias, got {other:?}"),
    }
}

#[test]
fn refinement_param_type() {
    let prog = parse_program("fn f(x: int{ $ > 0 }): int = x");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert!(matches!(f.params[0].ty.kind, TypeRefKind::Refine(_, _)));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn refinement_left_to_right() {
    let prog = parse_program("fn clamp(lo: int, hi: int{ $ > lo }): int = hi");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.params.len(), 2);
            assert!(matches!(f.params[0].ty.kind, TypeRefKind::Simple(_)));
            assert!(matches!(f.params[1].ty.kind, TypeRefKind::Refine(_, _)));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn refinement_dollar_in_expr() {
    let prog = parse_program("type Byte = int { $ >= 0 and $ <= 255 }");
    match &prog.decls[0] {
        TopDecl::Alias(a) => {
            assert!(matches!(a.target.kind, TypeRefKind::Refine(_, _)));
        }
        other => panic!("expected Alias, got {other:?}"),
    }
}

#[test]
fn fn_body_not_confused_with_refinement() {
    // fn without contracts + { body } must parse as fn body, not refinement
    let prog = parse_program("fn sign(x: int): int { if x > 0 { 1 } else { 0 } }");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert!(matches!(f.ret_type.kind, TypeRefKind::Simple(ref n) if n == "int"));
            assert!(matches!(f.body.kind, ExprKind::IfElse { .. }));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn refinement_param_name() {
    let prog = parse_program("fn g(x: int{ x > 0 }, y: int{ y > x }): int = y");
    match &prog.decls[0] {
        TopDecl::Fn(f) => {
            assert_eq!(f.params.len(), 2);
            assert!(matches!(f.params[0].ty.kind, TypeRefKind::Refine(_, _)));
            assert!(matches!(f.params[1].ty.kind, TypeRefKind::Refine(_, _)));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

// ── Composition operator precedence tests () ─────────

#[test]
fn seq_tighter_than_same_step() {
    // a -> b & c should parse as (a -> b) & c
    let prog = parse_program("pred p(a: int, b: int, c: int) = a -> b & c");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            assert!(matches!(p.body.kind, ExprKind::SameStep(_, _)));
            if let ExprKind::SameStep(lhs, _) = &p.body.kind {
                assert!(matches!(lhs.kind, ExprKind::Seq(_, _)));
            }
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn same_step_tighter_than_concurrent() {
    // a & b || c should parse as (a & b) || c
    let prog = parse_program("pred p(a: int, b: int, c: int) = a & b || c");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            assert!(matches!(p.body.kind, ExprKind::Conc(_, _)));
            if let ExprKind::Conc(lhs, _) = &p.body.kind {
                assert!(matches!(lhs.kind, ExprKind::SameStep(_, _)));
            }
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn concurrent_tighter_than_unordered() {
    // a || b | c should parse as (a || b) | c
    let prog = parse_program("pred p(a: int, b: int, c: int) = a || b | c");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            assert!(matches!(p.body.kind, ExprKind::Unord(_, _)));
            if let ExprKind::Unord(lhs, _) = &p.body.kind {
                assert!(matches!(lhs.kind, ExprKind::Conc(_, _)));
            }
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn full_composition_precedence() {
    // a -> b & c | d should parse as ((a -> b) & c) | d
    let prog = parse_program("pred p(a: int, b: int, c: int, d: int) = a -> b & c | d");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            // outermost: | (unordered)
            assert!(matches!(p.body.kind, ExprKind::Unord(_, _)));
            if let ExprKind::Unord(lhs, _) = &p.body.kind {
                // middle: & (same-step)
                assert!(matches!(lhs.kind, ExprKind::SameStep(_, _)));
                if let ExprKind::SameStep(inner, _) = &lhs.kind {
                    // innermost: -> (seq)
                    assert!(matches!(inner.kind, ExprKind::Seq(_, _)));
                }
            }
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn seq_right_assoc() {
    // a -> b -> c should parse as a -> (b -> c)
    let prog = parse_program("pred p(a: int, b: int, c: int) = a -> b -> c");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            assert!(matches!(p.body.kind, ExprKind::Seq(_, _)));
            if let ExprKind::Seq(_, rhs) = &p.body.kind {
                assert!(matches!(rhs.kind, ExprKind::Seq(_, _)));
            }
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

// ── system flat state fields ──────────────────────────

#[test]
fn system_flat_field() {
    let prog = parse_program(
        "system S { screen: int = 0 command handle(i: int) requires screen == 0 { screen' = 1 } }",
    );
    match &prog.decls[0] {
        TopDecl::System(s) => {
            assert_eq!(s.name, "S");
            assert!(matches!(&s.items[0], SystemItem::Field(f) if f.name == "screen"));
        }
        other => panic!("expected System, got {other:?}"),
    }
}

#[test]
fn struct_ctor_expr() {
    let prog = parse_program("pred p() = UiState { screen: 0, mode: 1, dirty: false }");
    match &prog.decls[0] {
        TopDecl::Pred(p) => {
            assert!(matches!(&p.body.kind, ExprKind::StructCtor(name, fields)
                    if name == "UiState" && fields.len() == 3));
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn system_struct_typed_field() {
    let src = r"
        struct UiState { screen: int, mode: int }
        system S {
            ui: UiState = UiState { screen: 0, mode: 1 }
            command handle(i: int) requires ui.screen == 0 { ui.screen' = 1 }
        }
    ";
    let prog = parse_program(src);
    // struct + system = 2 decls
    assert!(prog.decls.len() >= 2);
    match &prog.decls[1] {
        TopDecl::System(s) => {
            assert!(matches!(&s.items[0], SystemItem::Field(f) if f.name == "ui"));
            if let SystemItem::Field(f) = &s.items[0] {
                assert!(matches!(&f.default, Some(FieldDefault::Value(e))
                    if matches!(&e.kind, ExprKind::StructCtor(n, _) if n == "UiState")));
            }
        }
        other => panic!("expected System, got {other:?}"),
    }
}
#[test]
fn pub_keyword_is_not_a_declaration_modifier() {
    let err = parse_program_err("pub enum OrderStatus = Pending | Paid");
    assert!(
        err.to_string().contains("top-level declaration"),
        "expected top-level declaration error, got {err:?}"
    );
}

#[test]
fn parse_top_level_proc() {
    let prog = parse_program(
        r"
proc submit(billing: Billing, orders: Orders, order: Order) {
  charge = billing.charge(order)
  confirm = orders.confirm(order)
  confirm needs charge.ok
}
",
    );

    let TopDecl::Proc(proc_decl) = &prog.decls[0] else {
        panic!("expected top-level proc decl");
    };
    assert_eq!(proc_decl.name, "submit");
    assert_eq!(proc_decl.params.len(), 3);
    assert!(proc_decl.requires.is_none());
    assert_eq!(proc_decl.params[0].name, "billing");
    assert!(matches!(
        &proc_decl.params[0].ty.kind,
        crate::ast::TypeRefKind::Simple(name) if name == "Billing"
    ));
}

#[test]
fn parse_top_level_proc_with_requires() {
    let prog = parse_program(
        r"
proc submit(order: Order) requires order.status == @Pending {
  charge = billing.charge(order)
}
",
    );

    let TopDecl::Proc(proc_decl) = &prog.decls[0] else {
        panic!("expected top-level proc decl");
    };
    assert!(proc_decl.requires.is_some());
}

#[test]
fn parse_program_proc_use() {
    let prog = parse_program(
        r"
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let orders_sys = Orders { orders: orders }
  use submit(billing, orders_sys)
}
",
    );

    let TopDecl::Program(program) = &prog.decls[0] else {
        panic!("expected program decl");
    };
    assert_eq!(program.items.len(), 3);
    let crate::ast::ProgramItem::UseProc(use_decl) = &program.items[2] else {
        panic!("expected proc use");
    };
    assert_eq!(use_decl.proc_name, "submit");
    assert_eq!(use_decl.args, vec!["billing", "orders_sys"]);
}

#[test]
fn parse_proc_use_composition_item() {
    let prog = parse_program(
        r"
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }

  proc checkout(order: Order) {
    use submit(billing, order) as charge_flow
    done needs charge_flow::charge.ok
  }
}
",
    );

    let TopDecl::Program(program) = &prog.decls[0] else {
        panic!("expected program decl");
    };
    let crate::ast::ProgramItem::Proc(proc_decl) = &program.items[1] else {
        panic!("expected proc decl");
    };
    match &proc_decl.items[0] {
        crate::ast::ProcItem::UseProc(use_decl) => {
            assert_eq!(use_decl.proc_name, "submit");
            assert_eq!(use_decl.alias.as_deref(), Some("charge_flow"));
        }
        other => panic!("expected proc use item, got {other:?}"),
    }
}

#[test]
fn parse_proc_match_branch_sugar_desugars_to_edges() {
    let prog = parse_program(
        r"
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship = shipping.ship(order)
    retry = billing.retry(order)

    match charge {
      @ok => ship
      @err => retry, ship
    }
  }
}
",
    );

    let TopDecl::Program(program) = &prog.decls[0] else {
        panic!("expected program decl");
    };
    let crate::ast::ProgramItem::Proc(proc_decl) = &program.items[2] else {
        panic!("expected proc item");
    };
    let edge_count = proc_decl
        .items
        .iter()
        .filter(|item| matches!(item, crate::ast::ProcItem::NeedsEdge { .. }))
        .count();
    assert_eq!(edge_count, 3);
}

#[test]
fn parse_proc_dependency_condition_precedence_and_parentheses() {
    let prog = parse_program(
        r"
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    pack = shipping.pack(order)
    ship = shipping.ship(order)

    ship needs charge.ok or not (pack.done and charge.err)
  }
}
",
    );

    let TopDecl::Program(program) = &prog.decls[0] else {
        panic!("expected program decl");
    };
    let crate::ast::ProgramItem::Proc(proc_decl) = &program.items[2] else {
        panic!("expected proc item");
    };
    let edge = proc_decl
        .items
        .iter()
        .find_map(|item| match item {
            crate::ast::ProcItem::NeedsEdge { condition, .. } => Some(condition),
            _ => None,
        })
        .expect("expected needs edge");

    match edge {
        crate::ast::ProcDepCond::Or(left, right) => {
            assert!(matches!(
                left.as_ref(),
                crate::ast::ProcDepCond::Fact { node, qualifier }
                    if node == "charge" && qualifier.as_deref() == Some("ok")
            ));
            match right.as_ref() {
                crate::ast::ProcDepCond::Not(inner) => match inner.as_ref() {
                    crate::ast::ProcDepCond::And(and_left, and_right) => {
                        assert!(matches!(
                            and_left.as_ref(),
                            crate::ast::ProcDepCond::Fact { node, qualifier }
                                if node == "pack" && qualifier.as_deref() == Some("done")
                        ));
                        assert!(matches!(
                            and_right.as_ref(),
                            crate::ast::ProcDepCond::Fact { node, qualifier }
                                if node == "charge" && qualifier.as_deref() == Some("err")
                        ));
                    }
                    other => panic!("expected inner And, got {other:?}"),
                },
                other => panic!("expected right side Not, got {other:?}"),
            }
        }
        other => panic!("expected top-level Or, got {other:?}"),
    }
}
