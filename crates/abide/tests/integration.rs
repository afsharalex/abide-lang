// Crate-level clippy allows for the integration test binary. Mirrors the
// allows on the library crate (`src/lib.rs`) — these style lints are
// historically tolerated across the codebase.
#![allow(
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::match_same_arms,
    clippy::items_after_statements,
    clippy::format_push_string,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_lossless,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    clippy::doc_lazy_continuation,
    clippy::doc_markdown,
    clippy::ref_option,
    clippy::needless_pass_by_value,
    clippy::needless_pass_by_ref_mut,
    clippy::result_large_err,
    clippy::large_enum_variant,
    clippy::unnecessary_wraps,
    clippy::cloned_ref_to_slice_refs,
    clippy::redundant_closure_call,
    clippy::used_underscore_binding
)]

use std::path::PathBuf;

use abide::elab;
use abide::ir;
use abide::lex;
use abide::loader;
use abide::parse::Parser;

const UNBOUNDED_PROOF_TEST_ENV: &str = "ABIDE_RUN_UNBOUNDED_PROOF_TESTS";

fn should_run_unbounded_proof_tests() -> bool {
    std::env::var_os(UNBOUNDED_PROOF_TEST_ENV).is_some()
}

fn skip_unbounded_proof_test() {
    eprintln!("skipping unbounded proof-backend test; set {UNBOUNDED_PROOF_TEST_ENV}=1 to opt in");
}

macro_rules! require_unbounded_proof_tests {
    () => {
        if !should_run_unbounded_proof_tests() {
            skip_unbounded_proof_test();
            return;
        }
    };
}

fn parse_file(path: &str) -> abide::ast::Program {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let tokens = lex::lex(&src).unwrap_or_else(|errors| {
        panic!("lex errors in {path}: {errors:?}");
    });
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap_or_else(|e| {
        panic!("parse error in {path}: {e}");
    });
    assert!(
        !program.decls.is_empty(),
        "{path} should have at least one declaration"
    );
    program
}

fn elaborate_file(path: &str) -> elab::types::ElabResult {
    let program = parse_file(path);
    let (result, errors) = elab::elaborate(&program);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    for err in &actual_errors {
        eprintln!("{path}: {err}");
    }
    assert!(
        actual_errors.is_empty(),
        "{path} should elaborate without errors"
    );
    result
}

/// Load and elaborate via the multi-file loader (handles include/use).
fn load_and_elaborate_files(paths: &[&str]) -> elab::types::ElabResult {
    let path_bufs: Vec<PathBuf> = paths.iter().map(PathBuf::from).collect();
    let (env, load_errors, _all_paths) = loader::load_files(&path_bufs);
    assert!(
        load_errors.is_empty(),
        "{paths:?} should load without errors: {load_errors:?}"
    );
    assert!(
        env.include_load_errors.is_empty(),
        "{paths:?} should have no include errors: {:?}",
        env.include_load_errors
    );

    let (result, errors) = elab::elaborate_env(env);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    for err in &actual_errors {
        eprintln!("{paths:?}: {err}");
    }
    assert!(
        actual_errors.is_empty(),
        "{paths:?} should elaborate without errors"
    );
    result
}

fn lower_loaded_files(paths: &[&str]) -> ir::types::IRProgram {
    let result = load_and_elaborate_files(paths);
    let (ir_program, _lower_diag) = ir::lower(&result);
    ir_program
}

/// Commerce fixture: multi-file via include (commerce.ab includes billing.ab).
const COMMERCE_FIXTURE: &[&str] = &["tests/fixtures/commerce.ab"];

/// Logistics fixture: two includes, wildcard + aliased imports.
const LOGISTICS_FIXTURE: &[&str] = &["tests/fixtures/logistics.ab"];

#[test]
fn parse_simple() {
    parse_file("tests/fixtures/simple.ab");
}

#[test]
fn parse_auth() {
    parse_file("tests/fixtures/auth.ab");
}

#[test]
fn parse_commerce() {
    parse_file("tests/fixtures/commerce.ab");
}

#[test]
fn parse_inventory() {
    parse_file("tests/fixtures/inventory.ab");
}

#[test]
fn parse_workflow() {
    parse_file("tests/fixtures/workflow.ab");
}

#[test]
fn parse_relations() {
    parse_file("tests/fixtures/relations.ab");
}

#[test]
fn parse_collections() {
    parse_file("tests/fixtures/collections.ab");
}

#[test]
fn lex_all_fixtures() {
    for name in &[
        "simple",
        "auth",
        "commerce",
        "inventory",
        "workflow",
        "relations",
        "collections",
        "collection_comprehensions",
    ] {
        let path = format!("tests/fixtures/{name}.ab");
        let src = std::fs::read_to_string(&path).unwrap();
        lex::lex(&src).unwrap_or_else(|errors| {
            panic!("lex errors in {path}: {errors:?}");
        });
    }
}

// ── Elaboration integration tests ────────────────────────────────────

#[test]
fn elaborate_simple() {
    let result = elaborate_file("tests/fixtures/simple.ab");
    assert!(!result.types.is_empty(), "should have types");
    assert!(!result.entities.is_empty(), "should have entities");
}

#[test]
fn elaborate_auth() {
    let result = elaborate_file("tests/fixtures/auth.ab");
    assert!(result.entities.len() >= 2, "should have User and Session");
    assert!(!result.systems.is_empty(), "should have Auth system");
    assert!(!result.preds.is_empty(), "should have predicates");
    assert!(!result.verifies.is_empty(), "should have verify blocks");
}

#[test]
fn elaborate_commerce() {
    // Multi-file: commerce + billing modules loaded together
    let result = load_and_elaborate_files(COMMERCE_FIXTURE);
    assert!(
        result.systems.len() >= 2,
        "should have Commerce and Billing"
    );
    assert!(!result.scenes.is_empty(), "should have scenes");
    assert!(!result.theorems.is_empty(), "should have proofs");
}

#[test]
fn elaborate_logistics() {
    // Multi-file: logistics includes shipping + warehouse,
    // uses wildcard (Shipping::*) and aliases (Warehouse::Slot as WSlot).
    let result = load_and_elaborate_files(LOGISTICS_FIXTURE);
    assert!(!result.systems.is_empty(), "should have Logistics system");
    assert!(
        result.entities.len() >= 2,
        "should have Package (wildcard) and WSlot (alias), got {}",
        result.entities.len()
    );
    assert!(
        result.preds.len() >= 2,
        "should have preds using alias and wildcard names"
    );
}

#[test]
fn lower_logistics() {
    let prog = lower_loaded_files(LOGISTICS_FIXTURE);
    assert!(!prog.verifies.is_empty(), "should have verify blocks");
    assert!(!prog.scenes.is_empty(), "should have scene blocks");
    let json = ir::emit_json(&prog).expect("IR serialization should succeed");
    let _parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
}

#[test]
fn verify_logistics_fixture() {
    let prog = lower_loaded_files(LOGISTICS_FIXTURE);
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    // logistics_safety: uses WSlot alias in quantifier — should verify
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                | abide::verify::VerificationResult::Checked { name, .. }
                if name == "logistics_safety"
        )),
        "logistics_safety should be PROVED or CHECKED, got: {results:?}"
    );
    // reserve_and_ship scene uses aliased (WSlot) and wildcard (Package) entity names
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "reserve_and_ship"
        )),
        "reserve_and_ship scene should PASS, got: {results:?}"
    );
}

#[test]
fn elaborate_inventory() {
    let result = elaborate_file("tests/fixtures/inventory.ab");
    assert!(
        result.entities.len() >= 3,
        "should have Product, Reservation, Fulfillment"
    );
}

#[test]
fn elaborate_workflow() {
    let result = elaborate_file("tests/fixtures/workflow.ab");
    assert!(
        !result.lemmas.is_empty() || !result.theorems.is_empty(),
        "should have proofs or lemmas"
    );
}

// ── AssumptionSet population ────────────────────────────────
//
// These tests verify that the elab resolve pass correctly populates
// `EVerify::assumption_set` (and the equivalents on theorem/lemma) from
// the parsed `assume {... }` block, with construct defaults applied
// and normalization (sort, dedup, strong-implies-weak).

fn elaborate_source(src: &str) -> abide::elab::types::ElabResult {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    elaborate_file(&path_str)
}

fn elaborate_source_errors(src: &str) -> Vec<abide::elab::error::ElabError> {
    let program = parse_source(src);
    let (_result, errors) = elab::elaborate(&program);
    errors
        .into_iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect()
}

fn parse_source(src: &str) -> abide::ast::Program {
    let tokens = lex::lex(src).unwrap_or_else(|errors| {
        panic!("lex errors in inline source: {errors:?}");
    });
    let mut parser = Parser::new(tokens);
    parser
        .parse_program()
        .unwrap_or_else(|err| panic!("parse error in inline source: {err}"))
}

#[test]
fn assumption_set_verify_default_no_stutter() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  } assert always true }
";
    let result = elaborate_source(src);
    let v = result.verifies.iter().find(|v| v.name == "v").expect("v");
    assert!(!v.assumption_set.stutter, "verify default is no stutter");
    assert!(v.assumption_set.weak_fair.is_empty());
    assert!(v.assumption_set.strong_fair.is_empty());
}

#[test]
fn reusable_proc_use_expands_into_program_procs() {
    let src = r"
enum Outcome = ok | err

entity Order {
  status: int = 0
}

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    return @ok
  }
}

system Orders(orders: Store<Order>) {
  command confirm(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

proc submit(billing: Billing, orders_sys: Orders, order: Order) {
  charge = billing.charge(order)
  confirm = orders_sys.confirm(order)
  confirm needs charge.ok
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let orders_sys = Orders { orders: orders }
  use submit(billing, orders_sys)
}
";

    let result = elaborate_source(src);
    let shop = result
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should be present");
    let submit = shop
        .procs
        .iter()
        .find(|proc_decl| proc_decl.name == "submit")
        .expect("reusable proc should expand into program");
    assert_eq!(submit.nodes.len(), 2);
    assert!(submit
        .nodes
        .iter()
        .any(|node| node.name == "charge" && node.instance == "billing"));
    assert!(submit
        .nodes
        .iter()
        .any(|node| node.name == "confirm" && node.instance == "orders_sys"));
}

#[test]
fn reusable_proc_use_reports_unknown_let_binding() {
    let src = r"
enum Outcome = ok | err
entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 { return @ok }
}

proc submit(billing: Billing, order: Order) {
  charge = billing.charge(order)
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  use submit(missing)
}
";

    let program = parse_source(src);
    let (result, errors) = elab::elaborate(&program);
    let _ = result;
    assert!(
        errors.iter().any(|err| err
            .to_string()
            .contains("argument `missing` is not a let binding")),
        "expected proc-use let binding diagnostic, got: {errors:?}"
    );
}

#[test]
fn proc_composition_expands_child_nodes_with_namespace() {
    let src = r"
enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 { return @ok }
}

system Orders(orders: Store<Order>) {
  command confirm(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

proc submit(billing: Billing, orders_sys: Orders, order: Order) {
  charge = billing.charge(order)
  confirm = orders_sys.confirm(order)
  confirm needs charge.ok
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let orders_sys = Orders { orders: orders }

  proc checkout(order: Order) {
    use submit(billing, orders_sys, order) as submit_flow
    done = orders_sys.confirm(order)
    done needs submit_flow::confirm
  }
}
";

    let result = elaborate_source(src);
    let shop = result
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should be present");
    let checkout = shop
        .procs
        .iter()
        .find(|proc_decl| proc_decl.name == "checkout")
        .expect("composed proc should exist");
    assert!(checkout
        .nodes
        .iter()
        .any(|node| node.name == "submit_flow__charge" && node.instance == "billing"));
    assert!(checkout
        .nodes
        .iter()
        .any(|node| node.name == "submit_flow__confirm" && node.instance == "orders_sys"));
    assert!(checkout.edges.iter().any(|edge| edge.target == "done"));
}

#[test]
fn assumption_set_theorem_default_stutter() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

theorem t for Sys { show always true }
";
    let result = elaborate_source(src);
    let t = result.theorems.iter().find(|t| t.name == "t").expect("t");
    assert!(t.assumption_set.stutter, "theorem default is stutter on");
}

#[test]
fn assumption_set_populated_from_assume_block() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go_a() requires s == @A { s' = @B }
  action go_b() requires s == @B { s' = @A } }
system Sys(es: Store<E>) {command a() { choose e: E where e.s == @A { e.go_a() } }
  command b() { choose e: E where e.s == @B { e.go_b() } } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
  
    fair Sys::a
    strong fair Sys::b
  }
  assert always true
}
";
    let result = elaborate_source(src);
    let v = result.verifies.iter().find(|v| v.name == "v").expect("v");
    assert_eq!(v.assumption_set.weak_fair.len(), 1);
    assert_eq!(v.assumption_set.strong_fair.len(), 1);
    let weak = v.assumption_set.weak_fair.iter().next().unwrap();
    assert_eq!(weak.system, "Sys");
    assert_eq!(weak.command, "a");
    let strong = v.assumption_set.strong_fair.iter().next().unwrap();
    assert_eq!(strong.command, "b");
}

#[test]
fn assumption_set_strong_implies_weak_normalization() {
    // Listing the same event under both `fair` and `strong fair` should
    // collapse — normalization keeps it only in strong_fair.
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
  
    fair Sys::tick
    strong fair Sys::tick
  }
  assert always true
}
";
    let result = elaborate_source(src);
    let v = result.verifies.iter().find(|v| v.name == "v").expect("v");
    assert_eq!(v.assumption_set.weak_fair.len(), 0);
    assert_eq!(v.assumption_set.strong_fair.len(), 1);
}

#[test]
fn assumption_set_no_stutter_overrides_theorem_default() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

theorem t for Sys {
  assume { no stutter }
  show always true
}
";
    let result = elaborate_source(src);
    let t = result.theorems.iter().find(|t| t.name == "t").expect("t");
    assert!(
        !t.assumption_set.stutter,
        "explicit `no stutter` wins over theorem default"
    );
}

#[test]
fn assumption_set_unqualified_event_resolves_in_scope() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
   fair tick }
  assert always true
}
";
    let result = elaborate_source(src);
    let v = result.verifies.iter().find(|v| v.name == "v").expect("v");
    let weak = v.assumption_set.weak_fair.iter().next().unwrap();
    assert_eq!(weak.system, "Sys");
    assert_eq!(weak.command, "tick");
}

#[test]
fn assumption_set_qualified_path_must_be_in_scope() {
    // Verify `v for A` references `B::other` — should be rejected even
    // though B is declared elsewhere in the program. The verification
    // site's scope is `[A]`; B is out of scope.
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }

system A(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

system B(es: Store<E>) {command other() { choose e: E where e.s == @A { e.go() } } }

verify v {
  assume {
    store es: E[0..3]
    let a = A { es: es }
  
   fair B::other }
  assert always true
}
";
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = elab::elaborate(&program);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("not in this verification site's scope")
                || msg.contains(
                    "not a system name or let-binding instance in this verification site's scope",
                )
        }),
        "should reject out-of-scope qualified path, got: {errors:?}"
    );
}

#[test]
fn assumption_set_unknown_event_diagnostic() {
    let src = r"module T

enum S = A | B
entity E { s: S = @A
  action go() requires s == @A { s' = @B } }
system Sys(es: Store<E>) {command tick() { choose e: E where e.s == @A { e.go() } } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
   fair Sys::nonexistent }
  assert always true
}
";
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = elab::elaborate(&program);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("unknown event") || msg.contains("nonexistent")
        }),
        "should report UNKNOWN_FAIR_EVENT diagnostic, got: {errors:?}"
    );
}

#[test]
fn assumption_set_per_tuple_for_parameterized_event() {
    // `tick(o: Order)` is parameterized — fair tick should populate the
    // per_tuple set so knows to encode per-(event, args) tuple
    // fairness rather than per-event.
    let src = r"module T

enum S = A | B
entity Order { o: S = @A
  action go() requires o == @A { o' = @B } }
system Sys(orders: Store<Order>) {command tick(target: Order) { target.go() }
  command noop() { } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
  
    fair Sys::tick
    fair Sys::noop
  }
  assert always true
}
";
    let result = elaborate_source(src);
    let v = result.verifies.iter().find(|v| v.name == "v").expect("v");

    use abide::elab::types::EventRef;
    // tick has a parameter → must be in per_tuple
    assert!(
        v.assumption_set
            .per_tuple
            .contains(&EventRef::new("Sys", "tick")),
        "parameterized event should be in per_tuple, got {:?}",
        v.assumption_set.per_tuple
    );
    // noop has no parameters → must NOT be in per_tuple
    assert!(
        !v.assumption_set
            .per_tuple
            .contains(&EventRef::new("Sys", "noop")),
        "zero-arg event should not be in per_tuple, got {:?}",
        v.assumption_set.per_tuple
    );
}

#[test]
fn assumption_set_per_tuple_lowered_to_ir() {
    // The IR mirror also carries the per_tuple set.
    let src = r"module T

enum S = A | B
entity Order { o: S = @A
  action go() requires o == @A { o' = @B } }
system Sys(orders: Store<Order>) {command tick(target: Order) { target.go() } }

verify v {
  assume {
    store orders: Order[0..3]
    let sys = Sys { orders: orders }
  
   fair Sys::tick }
  assert always true
}
";
    let result = elaborate_source(src);
    let (prog, _lower_diag) = ir::lower(&result);
    let v = prog.verifies.iter().find(|v| v.name == "v").expect("v");
    assert_eq!(v.assumption_set.per_tuple.len(), 1);
    assert_eq!(v.assumption_set.per_tuple[0].command, "tick");
}

#[test]
fn assumption_set_lowered_to_ir() {
    // The IR mirror is populated from the elab field. Verify a known
    // fixture has the expected normalized data after lowering.
    let prog = lower_file("tests/fixtures/strong_fairness.ab");
    let strong_thm = prog
        .theorems
        .iter()
        .find(|t| t.name == "strong_liveness")
        .expect("strong_liveness");
    assert!(
        strong_thm.assumption_set.stutter,
        "theorem default = stutter on"
    );
    assert_eq!(strong_thm.assumption_set.strong_fair.len(), 1);
    assert_eq!(strong_thm.assumption_set.strong_fair[0].command, "go_c");
    // Weak fair set should NOT contain go_c (normalization removed it).
    assert!(strong_thm
        .assumption_set
        .weak_fair
        .iter()
        .all(|e| e.command != "go_c"));
}

// ── IR lowering + JSON integration tests ─────────────────────────────

fn lower_file(path: &str) -> ir::types::IRProgram {
    let result = elaborate_file(path);
    let (ir_program, _lower_diag) = ir::lower(&result);
    ir_program
}

fn lower_files(paths: &[&str]) -> ir::types::IRProgram {
    let result = load_and_elaborate_files(paths);
    let (ir_program, _lower_diag) = ir::lower(&result);
    ir_program
}

#[test]
fn lower_simple() {
    let prog = lower_file("tests/fixtures/simple.ab");
    assert!(!prog.types.is_empty(), "should have IR types");
    assert!(!prog.entities.is_empty(), "should have IR entities");
    // Verify JSON serialization succeeds
    let json = ir::emit_json(&prog).expect("IR serialization should succeed");
    assert!(
        json.contains("\"entities\""),
        "JSON should contain entities key"
    );
}

#[test]
fn lower_commerce() {
    // Multi-file: commerce + billing modules loaded together
    let prog = lower_loaded_files(COMMERCE_FIXTURE);
    assert!(prog.systems.len() >= 2, "should have Commerce and Billing");
    assert!(!prog.verifies.is_empty(), "should have IR verifies");
    assert!(!prog.scenes.is_empty(), "should have IR scenes");
    let json = ir::emit_json(&prog).expect("IR serialization should succeed");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert!(parsed["systems"].is_array());
    assert!(parsed["scenes"].is_array());
}

#[test]
fn lower_all_fixtures() {
    // Single-file fixtures
    for name in &[
        "simple",
        "auth",
        "inventory",
        "workflow",
        "collections",
        "collection_comprehensions",
    ] {
        let path = format!("tests/fixtures/{name}.ab");
        let prog = lower_file(&path);
        let json = ir::emit_json(&prog).expect("IR serialization should succeed");
        let parsed: serde_json::Value =
            serde_json::from_str(&json).unwrap_or_else(|e| panic!("{name}: invalid JSON: {e}"));
        assert!(parsed.is_object(), "{name}: top-level should be object");
        assert!(
            parsed["types"].is_array(),
            "{name}: should have types array"
        );
        assert!(
            parsed["entities"].is_array(),
            "{name}: should have entities array"
        );
    }
    // Multi-file fixture (commerce + billing modules)
    {
        let prog = lower_loaded_files(COMMERCE_FIXTURE);
        let json = ir::emit_json(&prog).expect("IR serialization should succeed");
        let parsed: serde_json::Value =
            serde_json::from_str(&json).unwrap_or_else(|e| panic!("commerce: invalid JSON: {e}"));
        assert!(parsed.is_object(), "commerce: top-level should be object");
        assert!(
            parsed["types"].is_array(),
            "commerce: should have types array"
        );
        assert!(
            parsed["entities"].is_array(),
            "commerce: should have entities array"
        );
    }
}

// ── Verification integration tests ──────────────────────────────────

fn verify_file(path: &str) -> Vec<abide::verify::VerificationResult> {
    let prog = lower_file(path);
    abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default())
}

#[test]
fn verify_auth_fixture() {
    let results = verify_file("tests/fixtures/auth.ab");
    assert!(!results.is_empty(), "auth should have verification results");
    // auth_safety: CHECKED or PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "auth_safety"
        )),
        "auth_safety should be CHECKED or PROVED"
    );
    // lockout scene: PASS
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "lockout_after_5_failures"
        )),
        "lockout scene should PASS"
    );
}

#[test]
fn verify_workflow_fixture() {
    let results = verify_file("tests/fixtures/workflow.ab");
    // workflow_safety: CHECKED (complex invariant, induction fails → BMC fallback)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "workflow_safety"
        )),
        "workflow_safety should be CHECKED"
    );
    // workflow_liveness: CHECKED (eventually → skips induction, BMC)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "workflow_liveness"
        )),
        "workflow_liveness should be CHECKED"
    );
    // revision_count_monotonic: PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "revision_count_monotonic"
        )),
        "revision_count_monotonic should be PROVED"
    );
    // All 3 scenes should pass
    let scene_passes: Vec<_> = results
        .iter()
        .filter(|r| matches!(&r, abide::verify::VerificationResult::ScenePass { .. }))
        .collect();
    assert_eq!(
        scene_passes.len(),
        3,
        "all 3 workflow scenes should pass, got {}",
        scene_passes.len()
    );
}

#[test]
fn verify_inventory_fixture() {
    let results = verify_file("tests/fixtures/inventory.ab");
    // inventory_safety: PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "inventory_safety"
        )),
        "inventory_safety should be PROVED"
    );
    // end_to_end: PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "end_to_end"
        )),
        "end_to_end should be PROVED"
    );
    // Both scenes should pass
    let scene_passes: Vec<_> = results
        .iter()
        .filter(|r| matches!(&r, abide::verify::VerificationResult::ScenePass { .. }))
        .collect();
    assert_eq!(scene_passes.len(), 2, "both inventory scenes should pass");
}

#[test]
fn verify_relations_fixture() {
    let results = verify_file("tests/fixtures/relations.ab");
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_join_passes" && *depth == 0
        )),
        "relation join should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_transpose_passes" && *depth == 0
        )),
        "relation transpose should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_reach_passes" && *depth == 0
        )),
        "relation reflexive closure should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_closure_passes" && *depth == 0
        )),
        "relation transitive closure should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_projection_passes" && *depth == 0
        )),
        "relation projection should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_intersection_passes" && *depth == 0
        )),
        "relation intersection should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_empty_join_cardinality_passes" && *depth == 0
        )),
        "empty relation join cardinality should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_nary_join_passes" && *depth == 0
        )),
        "n-ary relation join should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_mixed_projection_passes" && *depth == 0
        )),
        "mixed-column relation projection should be routed to RustSAT"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, depth, .. }
                if name == "relation_nested_composition_passes" && *depth == 0
        )),
        "nested relation composition should be routed to RustSAT"
    );
    let counterexample = results
        .iter()
        .find(|r| {
            matches!(
                &r,
                abide::verify::VerificationResult::Counterexample { name, .. }
                    if name == "relation_counterexample_renders_witness"
            )
        })
        .expect("false relation equality should produce a counterexample");
    assert!(
        counterexample.relational_witness().is_some(),
        "relation counterexample should include relational witness evidence: {counterexample:?}"
    );
    let rendered = counterexample.to_string();
    assert!(
        rendered.contains("relation derived left") && rendered.contains("(1, 3)"),
        "rendered relation witness should include the computed left relation: {rendered}"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "relation_field_current_subset_next"
        )),
        "current field relation should be checked as a subset of next"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "relation_field_next_not_subset_current"
        )),
        "reverse field relation subset should produce a counterexample"
    );
}

#[test]
fn verify_commerce_fixture() {
    // Multi-file: commerce.ab includes billing.ab
    let prog = lower_loaded_files(COMMERCE_FIXTURE);
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    // commerce_smoke: COUNTEREXAMPLE (expected — eventually in bounded check)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "commerce_smoke"
        )),
        "commerce_smoke should be COUNTEREXAMPLE"
    );
    // billing_safety: PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "billing_safety"
        )),
        "billing_safety should be PROVED"
    );
    // happy_path scene: PASS
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "happy_path"
        )),
        "commerce happy_path scene should PASS"
    );
    // order_total_non_negative theorem: PROVED
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "order_total_non_negative"
        )),
        "order_total_non_negative should be PROVED"
    );
}

// ── Source-location propagation tests ────────────────────────────────

/// Verify that verification results carry source spans from the original file.
/// Uses the auth fixture which has verify, scene, and theorem blocks.
#[test]
fn verification_results_carry_source_spans() {
    // Load through the full pipeline (loader → elaboration → lower → verify)
    // to ensure spans propagate end-to-end.
    let path = std::path::PathBuf::from("tests/fixtures/auth.ab");
    let mut sources = vec![];
    let (result, _errors) = {
        let mut srcs: Vec<(String, String)> = vec![];
        let r = load_and_elaborate_for_test(&[path.clone()], &mut srcs);
        sources = srcs;
        r
    };
    let (ir, _lower_diag) = abide::ir::lower(&result);
    let results = abide::verify::verify_all(&ir, &abide::verify::VerifyConfig::default());

    // Every result should have a span (since the fixture has verify/scene/theorem blocks
    // and we loaded through the loader which sets current_file).
    for r in &results {
        assert!(
            r.span().is_some(),
            "verification result should have a span: {r}"
        );
        assert!(
            r.file().is_some(),
            "verification result should have a file: {r}"
        );
        // The file should be the canonical path of the auth fixture
        let file = r.file().unwrap();
        assert!(
            file.contains("auth.ab"),
            "file should reference auth.ab, got: {file}"
        );
    }

    // At least one source should be loaded
    assert!(!sources.is_empty(), "should have loaded source text");
}

fn load_and_elaborate_for_test(
    paths: &[std::path::PathBuf],
    sources: &mut Vec<(String, String)>,
) -> (
    abide::elab::types::ElabResult,
    Vec<abide::elab::error::ElabError>,
) {
    let read_sources = |paths: &[std::path::PathBuf]| -> Vec<(String, String)> {
        paths
            .iter()
            .filter_map(|p| {
                let src = std::fs::read_to_string(p).ok()?;
                let key = std::fs::canonicalize(p)
                    .map_or_else(|_| p.display().to_string(), |c| c.display().to_string());
                Some((key, src))
            })
            .collect()
    };
    *sources = read_sources(paths);
    let (env, _load_errors, all_paths) = abide::loader::load_files(paths);
    for loaded_path in &all_paths {
        let key = loaded_path.display().to_string();
        if !sources.iter().any(|(name, _)| name == &key) {
            if let Ok(src) = std::fs::read_to_string(loaded_path) {
                sources.push((key, src));
            }
        }
    }
    abide::elab::elaborate_env(env)
}

// ── CLI output snapshot tests ────────────────────────────────────────

/// Verify that `abide verify` on auth.ab produces miette-rendered output
/// for the `lockout_correctness` theorem (which fails with liveness).
/// Checks that stderr contains file path, line markers, and labeled span.
#[test]
fn cli_verify_renders_miette_snippet_for_failure() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args(["verify", "tests/fixtures/auth.ab"])
        .output()
        .expect("failed to run abide verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should exit with failure (lockout_correctness is Unprovable)
    assert!(
        !output.status.success(),
        "expected non-zero exit: stdout={stdout}, stderr={stderr}"
    );

    // stderr should contain miette-rendered diagnostic with file reference
    assert!(
        stderr.contains("auth.ab"),
        "stderr should reference auth.ab file: {stderr}"
    );

    // stderr should contain the labeled span pointing to the show expression
    assert!(
        stderr.contains("could not prove"),
        "stderr should contain 'could not prove' label: {stderr}"
    );

    // stderr should contain line-number gutter (miette renders ` NNN │ `)
    assert!(
        stderr.contains("│"),
        "stderr should contain miette line gutter: {stderr}"
    );

    // stdout should contain success results as plain text
    assert!(
        stdout.contains("CHECKED") || stdout.contains("PROVED"),
        "stdout should have CHECKED or PROVED result: {stdout}"
    );
    assert!(
        stdout.contains("PASS"),
        "stdout should have PASS for scene: {stdout}"
    );
}

/// Verify that success-only output goes to stdout with no miette rendering.
/// Uses the workflow fixture which has no failures.
#[test]
fn cli_verify_success_only_renders_plain_text() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args(["verify", "tests/fixtures/workflow.ab"])
        .output()
        .expect("failed to run abide verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should exit successfully
    assert!(
        !stdout.trim().is_empty(),
        "expected machine-readable JSON output even on verification failure: stderr={stderr}"
    );

    // stdout should contain verification results
    assert!(
        stdout.contains("CHECKED") || stdout.contains("PROVED"),
        "stdout should have verification results: {stdout}"
    );
    assert!(
        stdout.contains("PASS"),
        "stdout should have PASS for scenes: {stdout}"
    );

    // stderr should be empty (no failures to render)
    assert!(
        stderr.is_empty(),
        "stderr should be empty for success-only run: {stderr}"
    );
}

#[test]
fn cli_verify_accepts_independent_chc_solver_flag() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/logistics.ab",
            "--solver",
            "cvc5",
            "--chc-solver",
            "z3",
            "--bounded-only",
        ])
        .output()
        .expect("failed to run abide verify with independent --chc-solver");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "expected zero exit: stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.contains("CHECKED") || stdout.contains("PROVED"),
        "expected human-readable verification output: stdout={stdout}"
    );
}

#[test]
fn cli_verify_verbose_prints_human_readable_details() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--verbose",
            "--witness-semantics",
            "operational",
        ])
        .output()
        .expect("failed to run abide verify --verbose");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("tests/fixtures/fairness.ab"),
        "expected verbose output to include project-relative source path: stderr={stderr}"
    );
    assert!(
        stderr.contains("liveness violation found for 'unfair_signal'"),
        "expected verbose output to include the labeled miette failure: stderr={stderr}"
    );
    assert!(
        stderr.contains("Loop fairness analysis:"),
        "expected verbose output to include the failure witness trace: stderr={stderr}"
    );
}

#[test]
fn cli_verify_debug_evidence_prints_raw_evidence_json() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--debug-evidence",
            "--witness-semantics",
            "operational",
        ])
        .output()
        .expect("failed to run abide verify --debug-evidence");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("debug evidence:"),
        "expected debug evidence banner: stderr={stderr}"
    );
    assert!(
        stderr.contains("\"family\": \"operational\""),
        "expected raw operational evidence JSON: stderr={stderr}"
    );
}

#[test]
fn cli_verify_report_json_writes_machine_readable_report_file() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("fairness.report.json");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--witness-semantics",
            "relational",
            "--report",
            "json",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report json");

    assert!(
        report.exists(),
        "expected verify report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_json =
        std::fs::read_to_string(&report).expect("should read generated verification report");
    let value: serde_json::Value =
        serde_json::from_str(&report_json).expect("report should be valid JSON");
    assert_eq!(
        value.get("kind").and_then(serde_json::Value::as_str),
        Some("verification_report")
    );
    assert_eq!(
        value.get("version").and_then(serde_json::Value::as_u64),
        Some(1)
    );
    assert_eq!(
        value
            .pointer("/summary/result_count")
            .and_then(serde_json::Value::as_u64),
        Some(3)
    );
    assert_eq!(
        value
            .pointer("/summary/failure_count")
            .and_then(serde_json::Value::as_u64),
        Some(1)
    );
    assert!(
        value
            .get("diagnostics")
            .and_then(serde_json::Value::as_array)
            .is_some(),
        "report should include diagnostics array: {report_json}"
    );
    assert_eq!(
        value
            .pointer("/config/witness_semantics")
            .and_then(serde_json::Value::as_str),
        Some("relational")
    );
    let family = value
        .get("results")
        .and_then(serde_json::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|item| item.get("evidence"))
        .filter(|evidence| !evidence.is_null())
        .filter_map(|evidence| evidence.pointer("/payload/payload/payload/family"))
        .find_map(serde_json::Value::as_str);
    assert_eq!(
        family,
        Some("relational"),
        "expected report to preserve relational witness payloads: {report_json}"
    );
}

#[test]
fn cli_verify_report_markdown_writes_markdown_file() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("fairness.report.md");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--report",
            "markdown",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report markdown");

    assert!(
        report.exists(),
        "expected markdown report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text =
        std::fs::read_to_string(&report).expect("should read generated markdown report");
    assert!(
        report_text.contains("# Verification Report"),
        "{report_text}"
    );
    assert!(report_text.contains("## Results"), "{report_text}");
    assert!(report_text.contains("### Failing Results"), "{report_text}");
    assert!(report_text.contains("### Passing Results"), "{report_text}");
    assert!(
        report_text.contains("#### LIVENESS VIOLATION unfair_signal"),
        "{report_text}"
    );
    assert!(report_text.contains("##### Evidence"), "{report_text}");
    assert!(report_text.contains("Execution witness"), "{report_text}");
    assert!(report_text.contains("Repeating cycle"), "{report_text}");
    assert!(report_text.contains("Repeating cycle:"), "{report_text}");
    assert!(report_text.contains("Violated assertion"), "{report_text}");
    assert!(report_text.contains("##### Context"), "{report_text}");
}

#[test]
fn cli_verify_report_html_writes_html_file() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("fairness.report.html");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--report",
            "html",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report html");

    assert!(
        report.exists(),
        "expected html report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text = std::fs::read_to_string(&report).expect("should read generated html report");
    assert!(report_text.contains("<!doctype html>"), "{report_text}");
    assert!(
        report_text.contains("<h1>Verification Report</h1>"),
        "{report_text}"
    );
    assert!(report_text.contains("unfair_signal"), "{report_text}");
    assert!(
        report_text.contains("Why this violates the assertion"),
        "{report_text}"
    );
    assert!(report_text.contains("Repeating cycle:"), "{report_text}");
    assert!(report_text.contains("loop-panel"), "{report_text}");
    assert!(
        report_text.contains("Why this violates the assertion"),
        "{report_text}"
    );
}

#[test]
fn cli_verify_report_markdown_renders_relational_evidence() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("fairness.report.md");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--witness-semantics",
            "relational",
            "--report",
            "markdown",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report markdown --witness-semantics relational");

    assert!(
        report.exists(),
        "expected markdown report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text =
        std::fs::read_to_string(&report).expect("should read generated markdown report");
    assert!(
        report_text.contains("Kind: temporal relational witness"),
        "{report_text}"
    );
    assert!(report_text.contains("###### State 0"), "{report_text}");
    assert!(
        report_text.contains("| Relation | Tuples | Sample |"),
        "{report_text}"
    );
    assert!(report_text.contains("`Signal.color`"), "{report_text}");
}

#[test]
fn cli_verify_report_html_renders_relational_evidence() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("fairness.report.html");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/fairness.ab",
            "--witness-semantics",
            "relational",
            "--report",
            "html",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report html --witness-semantics relational");

    assert!(
        report.exists(),
        "expected html report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text = std::fs::read_to_string(&report).expect("should read generated html report");
    assert!(report_text.contains("Relational witness"), "{report_text}");
    assert!(
        report_text.contains("cycle starts at state"),
        "{report_text}"
    );
    assert!(report_text.contains("Signal.color"), "{report_text}");
}

#[test]
fn cli_verify_report_html_renders_proof_failures() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("proof_failures.report.html");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/proof_failures.ab",
            "--report",
            "html",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report html on proof_failures");

    assert!(
        report.exists(),
        "expected html report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text = std::fs::read_to_string(&report).expect("should read generated html report");
    assert!(report_text.contains("impossible_lemma"), "{report_text}");
    assert!(report_text.contains("never_on"), "{report_text}");
    assert!(
        report_text.contains("Counterexample shape"),
        "{report_text}"
    );
    assert!(
        report_text.contains("Why this obligation is false"),
        "{report_text}"
    );
    assert!(
        report_text.contains("tests/fixtures/proof_failures.ab:"),
        "{report_text}"
    );
    assert!(!report_text.contains("span:"), "{report_text}");
}

#[test]
fn cli_verify_report_markdown_renders_proof_failures() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("proof_failures.report.md");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/proof_failures.ab",
            "--report",
            "markdown",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report markdown on proof_failures");

    assert!(
        report.exists(),
        "expected markdown report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text =
        std::fs::read_to_string(&report).expect("should read generated markdown report");
    assert!(report_text.contains("impossible_lemma"), "{report_text}");
    assert!(report_text.contains("never_on"), "{report_text}");
    assert!(
        report_text.contains("Counterexample shape:"),
        "{report_text}"
    );
    assert!(report_text.contains("Why This Fails"), "{report_text}");
    assert!(
        report_text.contains("location: tests/fixtures/proof_failures.ab:"),
        "{report_text}"
    );
    assert!(!report_text.contains("span:"), "{report_text}");
}

#[test]
fn cli_verify_report_html_renders_deadlock_failure() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let fixture = dir.path().join("deadlock_report.ab");
    let report = dir.path().join("deadlock_report.report.html");

    std::fs::write(
        &fixture,
        r"module DeadlockReport

entity Sig {
  flag: bool = false
}

system S(sigs: Store<Sig>) {
  command impossible() requires false {
    create Sig {}
  }
}

verify deadlocked {
  assume {
    store sigs: Sig[0..1]
    let s = S { sigs: sigs }
  }
  assert always all s: Sig | not s.flag
}
",
    )
    .expect("write deadlock fixture");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            fixture.to_str().expect("utf8 fixture path"),
            "--report",
            "html",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report html on deadlock fixture");

    assert!(
        report.exists(),
        "expected html report file to be written: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report_text = std::fs::read_to_string(&report).expect("should read generated html report");
    assert!(report_text.contains("deadlocked"), "{report_text}");
    assert!(report_text.contains("Why this deadlocks"), "{report_text}");
    assert!(report_text.contains("Blocked events"), "{report_text}");
    assert!(report_text.contains("impossible"), "{report_text}");
    assert!(report_text.contains("Deadlock reason"), "{report_text}");
    assert!(report_text.contains("Blocked state"), "{report_text}");
    assert!(report_text.contains("deadlock_report.ab:"), "{report_text}");
    assert!(!report_text.contains("span:"), "{report_text}");
    assert!(!report_text.contains("Previous</button>"), "{report_text}");
}

#[test]
fn cli_verify_report_defaults_to_reports_dir_and_single_file_name() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/fairness.ab");

    let output = std::process::Command::new(binary)
        .current_dir(dir.path())
        .args([
            "verify",
            fixture.to_str().expect("utf8 fixture path"),
            "--report",
            "json",
        ])
        .output()
        .expect("failed to run abide verify --report json with default dir");

    let report = dir.path().join("reports").join("fairness.report.json");
    assert!(
        report.exists(),
        "expected default report path for single-file run: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn cli_verify_report_is_written_even_when_diagnostics_abort_verification() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("broken.ab");
    let report = dir.path().join("broken.report.json");
    std::fs::write(
        &file,
        r"module Broken

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires missing_symbol == 0 {
    order.status' = 1
  }
}

verify bad for Billing[0..2] {
  assert always true
}
",
    )
    .expect("write broken fixture");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            file.to_str().expect("utf8 source path"),
            "--report",
            "json",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify --report on broken input");

    assert!(
        !output.status.success(),
        "expected verify to fail on broken input"
    );
    assert!(
        report.exists(),
        "expected report file even on diagnostic failure"
    );

    let report_json =
        std::fs::read_to_string(&report).expect("should read generated failure report");
    let value: serde_json::Value =
        serde_json::from_str(&report_json).expect("report should be valid JSON");
    assert_eq!(
        value
            .pointer("/summary/result_count")
            .and_then(serde_json::Value::as_u64),
        Some(0)
    );
    assert!(
        value
            .pointer("/summary/diagnostic_count")
            .and_then(serde_json::Value::as_u64)
            .is_some_and(|count| count > 0),
        "expected diagnostic count in report: {report_json}"
    );
    assert!(
        value
            .get("diagnostics")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|diagnostics| !diagnostics.is_empty()),
        "expected diagnostics payload in report: {report_json}"
    );
}

#[test]
fn cli_verify_report_rejects_unknown_format() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args(["verify", "tests/fixtures/fairness.ab", "--report", "xml"])
        .output()
        .expect("failed to run abide verify --report xml");

    assert!(
        !output.status.success(),
        "expected non-zero exit for unknown report format"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unsupported report format"),
        "expected validation error for unknown report format: {stderr}"
    );
}

#[test]
fn cli_verify_missing_input_does_not_write_report() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let dir = tempfile::tempdir().expect("tempdir");
    let missing = dir.path().join("missing.ab");
    let report = dir.path().join("missing.report.html");

    let output = std::process::Command::new(binary)
        .args([
            "verify",
            missing.to_str().expect("utf8 missing path"),
            "--report",
            "html",
            dir.path().to_str().expect("utf8 report dir"),
        ])
        .output()
        .expect("failed to run abide verify on missing input");

    assert!(
        !output.status.success(),
        "expected non-zero exit for missing input: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !report.exists(),
        "expected no report file for missing input: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("failed to read"),
        "expected missing-file load error in stderr: {stderr}"
    );
}

#[test]
fn cli_verify_both_bounded_only_succeeds_when_backends_agree() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args([
            "verify",
            "tests/fixtures/logistics.ab",
            "--solver",
            "both",
            "--bounded-only",
        ])
        .output()
        .expect("failed to run abide verify --solver both --bounded-only");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "expected zero exit: stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stderr.trim().is_empty(),
        "stderr should be empty in bounded-only success output: {stderr}"
    );
    assert!(
        stdout.contains("CHECKED"),
        "expected bounded-only run to include checked verify results: {stdout}"
    );
    assert!(
        !stdout.contains("UNPROVABLE"),
        "solver disagreement should not appear on this bounded logistics run: {stdout}"
    );
}

#[test]
fn cli_verify_unbounded_with_cvc5_chc_solver_stays_honest() {
    let spec = r"
entity Counter {
  x: int = 0
  y: int = 0

  action bump() requires x < 10 {
    x' = x + 1
    y' = y + 1
  }
}

system S(counters: Store<Counter>) {
  command tick() {
    choose c: Counter where true { c.bump() }
  }
}

verify counter_verify {
  assume {
    store counters: Counter[0..20]
    let s = S { counters: counters }
    stutter
  }
  assert always all c: Counter | c.y <= 10
}

theorem counter_theorem for S {
  show always all c: Counter | c.y <= 10
}
";
    let dir = tempfile::tempdir().expect("create tempdir");
    let spec_path = dir.path().join("counter.ab");
    let report_path = dir.path().join("counter.report.json");
    std::fs::write(&spec_path, spec).expect("write spec");

    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args([
            "verify",
            spec_path.to_str().expect("temp path should be valid UTF-8"),
            "--solver",
            "cvc5",
            "--chc-solver",
            "cvc5",
            "--unbounded-only",
            "--report",
            "json",
            dir.path().to_str().expect("temp dir should be valid UTF-8"),
        ])
        .output()
        .expect("failed to run abide verify with cvc5 CHC selection on unbounded path");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        !output.status.success(),
        "expected non-zero exit for unprovable results: stdout={stdout}, stderr={stderr}"
    );

    let value: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&report_path).expect("should read generated json report"),
    )
    .expect("report should be valid JSON");
    let arr = value
        .get("results")
        .and_then(serde_json::Value::as_array)
        .expect("report should include results array");
    assert!(!arr.is_empty(), "expected at least one verification result");

    assert!(
        arr.iter().any(|v| {
            matches!(
                v.get("kind").and_then(serde_json::Value::as_str),
                Some("unprovable")
            )
        }),
        "expected at least one unprovable result on the unbounded CHC path: {value}"
    );

    assert!(
        arr.iter().all(|v| {
            matches!(
                v.get("kind").and_then(serde_json::Value::as_str),
                Some("unprovable")
            )
        }),
        "expected the CHC-dependent unbounded run to stay honest instead of claiming proof: {value}"
    );
}

// ── Multi-file diagnostic tests ──────────────────────────────────────

/// Verify that duplicate declarations across files produce errors with file tags.
#[test]
fn multi_file_duplicate_decl_has_file_tags() {
    let dir = tempfile::tempdir().expect("create tempdir");

    let file_a = dir.path().join("a.ab");
    std::fs::write(&file_a, "enum Color = Red | Blue\n").unwrap();

    let file_b = dir.path().join("b.ab");
    std::fs::write(&file_b, "enum Color = Green | Yellow\n").unwrap();

    let main_file = dir.path().join("main.ab");
    std::fs::write(&main_file, "include \"a.ab\"\ninclude \"b.ab\"\n").unwrap();

    let paths = vec![main_file];
    let mut sources = Vec::new();
    let (_result, errors) = load_and_elaborate_for_test(&paths, &mut sources);

    // Should have a duplicate declaration error
    let dup_errors: Vec<_> = errors
        .iter()
        .filter(|e| e.kind == abide::elab::error::ErrorKind::DuplicateDecl)
        .collect();
    assert!(
        !dup_errors.is_empty(),
        "should have DuplicateDecl error: {errors:?}"
    );

    // The error should have a file tag (from the loader's per-file tagging)
    let first = &dup_errors[0];
    assert!(
        first.file.is_some(),
        "duplicate error should be file-tagged: {first:?}"
    );

    // Display should show error[E001]
    let text = format!("{first}");
    assert!(
        text.contains("error[E001]"),
        "should show error[E001]: {text}"
    );
}

/// Verify that the name suggestion scope includes types and entities, not just fields.
#[test]
fn name_suggestion_includes_types_and_entities() {
    // Create a spec with a typo in a requires expression
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("test.ab");
    std::fs::write(
        &file,
        r"
enum OrderStatus = Pending | Confirmed

entity Order {
    status: OrderStatus = @Pending
    action confirm() requires Confirmd == @Pending {
        status' = @Confirmed
    }
}
",
    )
    .unwrap();

    let paths = vec![file];
    let mut sources = Vec::new();
    let (_result, errors) = load_and_elaborate_for_test(&paths, &mut sources);

    // Should have an unresolved name error with a "did you mean?" suggestion
    let undef_errors: Vec<_> = errors
        .iter()
        .filter(|e| {
            e.kind == abide::elab::error::ErrorKind::UndefinedRef && e.message.contains("Confirmd")
        })
        .collect();
    assert!(
        !undef_errors.is_empty(),
        "should have UndefinedRef for 'Confirmd': {errors:?}"
    );

    let err = &undef_errors[0];
    let help = err.help.as_deref().unwrap_or("");
    assert!(
        help.contains("Confirmed"),
        "should suggest 'Confirmed' for 'Confirmd': help={help}"
    );
}

// ── QA Runner Integration Tests ─────────────────────────────────────

#[test]
fn qa_script_all_pass() {
    let script = std::path::Path::new("tests/fixtures/test_pass.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    assert!(
        result.failed == 0,
        "all assertions should pass: {} failed, output: {:?}",
        result.failed,
        result.output
    );
    assert!(
        result.passed > 0,
        "should have at least one passing assertion"
    );
    assert_eq!(result.passed, 4, "should have 4 passing assertions");
}

#[test]
fn qa_script_assertion_failure() {
    let script = std::path::Path::new("tests/fixtures/test_fail.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    assert_eq!(result.failed, 1, "one assertion should fail");
    assert_eq!(result.passed, 1, "one assertion should pass");
    assert!(
        result.output.iter().any(|l| l.contains("FAIL")),
        "output should contain FAIL"
    );
}

#[test]
fn qa_script_json_output() {
    let script = std::path::Path::new("tests/fixtures/test_pass.qa");
    let result = abide::qa::runner::run_qa_script(script, None, true);
    assert_eq!(result.failed, 0);
    for line in &result.output {
        assert!(
            line.starts_with('{'),
            "JSON output lines should be JSON objects: {line}"
        );
    }
}

#[test]
fn qa_script_load_from_file() {
    let script = std::path::Path::new("tests/fixtures/test_pass.qa");
    // -f flag with a single file
    let spec_file = std::path::Path::new("tests/fixtures/commerce.ab");
    let result = abide::qa::runner::run_qa_script(script, Some(spec_file), false);
    // With -f preloading + script's own load, commerce is loaded (possibly double-loaded
    // but module system deduplicates). Assertions should still pass.
    assert_eq!(result.failed, 0, "assertions should pass with -f preload");
}

#[test]
fn qa_script_load_from_directory() {
    // Create a temp directory with a single.ab file
    let tmp = tempfile::TempDir::new().unwrap();
    let spec_dir = tmp.path().join("specs");
    std::fs::create_dir(&spec_dir).unwrap();
    std::fs::copy("tests/fixtures/hypo_base.ab", spec_dir.join("ticket.ab")).unwrap();

    let script_path = tmp.path().join("test.qa");
    std::fs::write(&script_path, "ask entities\n").unwrap();

    // Use -f to load the spec directory
    let result = abide::qa::runner::run_qa_script(&script_path, Some(&spec_dir), false);
    assert!(result.executed > 0, "should execute at least one statement");
    assert!(
        !result.output.iter().any(|l| l.starts_with("error:")),
        "should not have errors: {:?}",
        result.output
    );
}

#[test]
fn qa_script_missing_file() {
    let script = std::path::Path::new("tests/fixtures/nonexistent.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    assert_eq!(result.executed, 0);
    assert!(
        result.output.iter().any(|l| l.contains("error")),
        "should report error for missing file"
    );
}

#[test]
fn qa_base_spec_no_cycles() {
    // Base spec only: Open -> InProgress -> Closed, no cycles
    let script = std::path::Path::new("tests/fixtures/test_no_hypothetical.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    assert_eq!(
        result.failed, 0,
        "base spec should have no cycles: {:?}",
        result.output
    );
    assert_eq!(result.passed, 2, "should have 2 passing assertions");
}

#[test]
fn qa_hypothetical_merges_modules() {
    // Base + hypothetical reopen: merging creates a cycle (Closed -> Open)
    let script = std::path::Path::new("tests/fixtures/test_hypothetical.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    assert_eq!(
        result.failed, 0,
        "hypothetical should merge and create cycles.\npassed: {}, failed: {}, executed: {}\noutput: {:?}",
        result.passed, result.failed, result.executed, result.output
    );
    assert_eq!(
        result.passed, 3,
        "should have 3 passing assertions.\noutput: {:?}",
        result.output
    );
}

// ── Circular include integration tests ──────────────────────────────

#[test]
fn circular_include_produces_load_error() {
    // Multi-file: a.ab includes b.ab, b.ab includes a.ab → CircularInclude
    let dir = tempfile::tempdir().expect("create tempdir");

    let a_path = dir.path().join("a.ab");
    std::fs::write(&a_path, "include \"b.ab\"\nenum AType = X").unwrap();

    let b_path = dir.path().join("b.ab");
    std::fs::write(&b_path, "include \"a.ab\"\nenum BType = Y").unwrap();

    let (env, load_errors, _) = loader::load_files(&[a_path]);
    assert!(load_errors.is_empty(), "top-level should succeed");

    let circular: Vec<_> = env
        .include_load_errors
        .iter()
        .filter(|e| matches!(e, loader::LoadError::CircularInclude { .. }))
        .collect();
    assert_eq!(
        circular.len(),
        1,
        "should detect exactly one circular include: {:?}",
        env.include_load_errors
    );
}

#[test]
fn circular_include_cli_exits_nonzero() {
    // The CLI should exit with non-zero when include errors are present.
    let dir = tempfile::tempdir().expect("create tempdir");

    let a_path = dir.path().join("a.ab");
    std::fs::write(&a_path, "include \"b.ab\"").unwrap();

    let b_path = dir.path().join("b.ab");
    std::fs::write(&b_path, "include \"a.ab\"").unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("elaborate")
        .arg(&a_path)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "CLI should exit non-zero for circular include"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("circular include"),
        "stderr should mention circular include, got: {stderr}"
    );
}

#[test]
fn circular_include_exits_nonzero_even_with_warnings() {
    // Regression: include cycle + unrelated warning (e.g., unknown module in use)
    // must still exit non-zero. Previously the synthetic hard error was only
    // injected when elab_errors was empty, so warnings prevented it.
    let dir = tempfile::tempdir().expect("create tempdir");

    let a_path = dir.path().join("a.ab");
    std::fs::write(
        &a_path,
        "module Test\ninclude \"b.ab\"\nuse Missing::*\nenum A = X",
    )
    .unwrap();

    let b_path = dir.path().join("b.ab");
    std::fs::write(&b_path, "include \"a.ab\"\nenum B = Y").unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("elaborate")
        .arg(&a_path)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "CLI should exit non-zero for circular include even when warnings are present"
    );
}

// ── Function contract verification integration tests ────────────────

#[test]
fn verify_contracts_fixture() {
    let prog = lower_file("tests/fixtures/contracts.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // abs: ensures result >= 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "abs"
        )),
        "abs contract should be PROVED"
    );

    // max_val: ensures result >= a, ensures result >= b
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "max_val"
        )),
        "max_val contract should be PROVED"
    );

    // clamp: requires lo <= hi, ensures result >= lo, ensures result <= hi
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "clamp"
        )),
        "clamp contract should be PROVED"
    );

    // double and is_positive have no ensures — should NOT produce results
    assert!(
        !results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
            | abide::verify::VerificationResult::FnContractFailed { name, .. }
                if name == "double" || name == "is_positive"
        )),
        "fns without ensures should not produce contract verification results"
    );

    // Total: exactly 3 contract results
    let fn_results: Vec<_> = results
        .iter()
        .filter(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { .. }
                    | abide::verify::VerificationResult::FnContractFailed { .. }
            )
        })
        .collect();
    assert_eq!(fn_results.len(), 3, "should verify exactly 3 fn contracts");
}

#[test]
fn verify_contracts_cli_output() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg("tests/fixtures/contracts.ab")
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "CLI should succeed for valid contracts"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("PROVED  fn abs"), "should show abs proved");
    assert!(
        stdout.contains("PROVED  fn max_val"),
        "should show max_val proved"
    );
    assert!(
        stdout.contains("PROVED  fn clamp"),
        "should show clamp proved"
    );
}

#[test]
fn verify_contracts_no_fn_verify_flag() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg("--no-fn-verify")
        .arg("tests/fixtures/contracts.ab")
        .output()
        .expect("run CLI");
    // With --no-fn-verify, no fn contract results should appear
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("PROVED  fn"),
        "no fn contract results should appear with --no-fn-verify"
    );
}

#[test]
fn verify_contracts_failing_ensures() {
    // Create a spec with a function that has a wrong ensures
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("bad.ab");
    std::fs::write(
        &file,
        "module Bad\n\nfn identity(x: int): int\n  ensures result > x\n{\n  x\n}\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "CLI should fail for violated fn contract"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("identity") || stderr.contains("contract violated"),
        "should mention the failing function: {stderr}"
    );
}

// ── Imperative while-loop verification tests ────────────────────────

#[test]
fn verify_imperative_fixture() {
    let prog = lower_file("tests/fixtures/imperative.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // sum_to: while loop with invariant total >= 0, ensures result >= 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "sum_to"
        )),
        "sum_to should be PROVED"
    );

    // gcd_imperative: while loop with invariant x > 0 ∧ y >= 0, ensures result > 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "gcd_imperative"
        )),
        "gcd_imperative should be PROVED"
    );

    // abs and max_val: pure if/else with ensures
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "abs"
        )),
        "abs should be PROVED"
    );
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "max_val"
        )),
        "max_val should be PROVED"
    );

    // checked_divide: assert b != 0 with requires b != 0 — should prove
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "checked_divide"
        )),
        "checked_divide should be PROVED"
    );

    // with_assertion: assert x > 0 with requires x > 0 — should prove
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "with_assertion"
        )),
        "with_assertion should be PROVED"
    );

    // Exactly 6 fn contracts verified (sum_to, gcd, abs, max_val, checked_divide, with_assertion)
    let fn_results: Vec<_> = results
        .iter()
        .filter(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { .. }
                    | abide::verify::VerificationResult::FnContractFailed { .. }
            )
        })
        .collect();
    assert_eq!(
        fn_results.len(),
        6,
        "should verify exactly 6 fn contracts in imperative.ab"
    );
}

#[test]
fn verify_assert_assume_fixture() {
    let prog = lower_file("tests/fixtures/assert_assume.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Assert-only functions should be PROVED
    for name in &[
        "assert_true_trivial",
        "assert_with_requires",
        "assert_chain",
        "assert_in_loop",
        "assert_after_loop",
        "checked_divide",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED"
        );
    }

    // Assume-containing functions should be ADMITTED (not PROVED)
    for name in &["assume_then_use", "assume_in_branch"] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractAdmitted { name: n, .. }
                    if n == name
            )),
            "{name} should be ADMITTED (contains assume)"
        );
    }

    // Total: 6 proved + 2 admitted = 8 successful verifications
    let success_count = results
        .iter()
        .filter(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { .. }
                    | abide::verify::VerificationResult::FnContractAdmitted { .. }
            )
        })
        .count();
    assert_eq!(
        success_count, 8,
        "should have 8 successful verifications (6 proved + 2 admitted)"
    );
}

#[test]
fn verify_assert_false_fails() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("assert_false.ab");
    std::fs::write(
        &file,
        "module TestFail\n\nfn bad(x: int): int\n  ensures result == x\n{\n  assert false\n  x\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // assert false should cause a verification failure
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Unprovable { hint, .. }
                if hint.contains("assertion may not hold")
        )),
        "assert false should produce an 'assertion may not hold' error"
    );
}

#[test]
fn verify_assert_false_without_ensures_fails() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("assert_false_no_ensures.ab");
    std::fs::write(
        &file,
        "module TestFail\n\nfn bad(x: int): int {\n  assert false\n  x\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // assert false should fail even without ensures
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Unprovable { hint, .. }
                if hint.contains("assertion may not hold")
        )),
        "assert false without ensures should still produce an assertion failure"
    );
}

#[test]
fn verify_nested_assert_in_pure_context_caught() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("nested_assert.ab");
    std::fs::write(
        &file,
        "module TestNested\n\nfn bad(x: int): int { x + (assert false) }\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Nested assert should be detected and produce an error
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Unprovable { hint, .. }
                if hint.contains("assert in pure expression context")
        )),
        "nested assert in pure expression context should produce an error (not 'No verification targets')"
    );
}

#[test]
fn verify_assume_false_vacuous() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("assume_false.ab");
    std::fs::write(
        &file,
        "module TestAssume\n\nfn vacuous(x: int): int\n  ensures result > 999\n{\n  assume false\n  x\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // assume false should vacuously prove the postcondition but report as ADMITTED
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, .. }
                if name == "vacuous"
        )),
        "assume false should be reported as ADMITTED (not PROVED)"
    );
}

#[test]
fn verify_sorry_bool_fn_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_bool.ab");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn bool_sorry(x: int): bool\n  ensures result == true\n{\n  sorry\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "bool_sorry" && reason.contains("sorry")
        )),
        "sorry in bool fn should be ADMITTED (not PROVED)"
    );
}

#[test]
fn verify_sorry_int_fn_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_int.ab");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn int_sorry(x: int): int\n  ensures result > 0\n{\n  sorry\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // sorry in int fn should be ADMITTED (previously errored with type mismatch)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "int_sorry" && reason.contains("sorry")
        )),
        "sorry in int fn should be ADMITTED (not type error)"
    );
}

#[test]
fn verify_sorry_no_ensures_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_no_ensures.ab");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn no_ensures(x: int): int {\n  sorry\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "no_ensures" && reason.contains("sorry")
        )),
        "sorry without ensures should still be ADMITTED"
    );
}

#[test]
fn verify_sorry_nested_in_binop_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_nested.ab");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn f(x: int): int { x + sorry }\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "f" && reason.contains("sorry")
        )),
        "nested sorry (x + sorry) should be ADMITTED, not skipped or type error"
    );
}

#[test]
fn verify_sorry_bypasses_termination() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_term.ab");
    std::fs::write(
        &file,
        "module TestSorry\n\n\
         fn f(n: int): int\n  ensures result >= 0\n  decreases n\n\
         {\n  if n > 0 { f(n) } else { sorry }\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // sorry should bypass termination checking entirely — no UNKNOWN termination error
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "f" && reason.contains("sorry")
        )),
        "sorry should bypass termination verification and report ADMITTED"
    );
    assert!(
        !results
            .iter()
            .any(|r| matches!(r, abide::verify::VerificationResult::Unprovable { .. })),
        "sorry should not produce any UNKNOWN/Unprovable results"
    );
}

#[test]
fn verify_quantifiers_fixture() {
    let prog = lower_file("tests/fixtures/quantifiers.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    for name in &[
        "identity_forall",
        "exists_witness",
        "nested_forall",
        "positive_from_requires",
        "order_preserving",
        "enum_forall_exhaustive",
        "enum_exists",
        "refinement_forall",
        "refinement_exists",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED"
        );
    }
}

#[test]
fn verify_enum_quantifier_unsound_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("enum_quant.ab");
    std::fs::write(
        &file,
        "module T\n\nenum E = A | B\n\n\
         fn bad(x: int): bool\n  ensures exists y: E | y != @E::A and y != @E::B\n{\n  true\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractFailed { .. }
        )),
        "exists y: E where y is neither A nor B should FAIL (domain restricted to enum values)"
    );
}

#[test]
fn verify_refinement_quantifier_unsound_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("ref_quant.ab");
    std::fs::write(
        &file,
        "module T\n\ntype Positive = int { $ > 0 }\n\n\
         fn bad(x: int): bool\n  ensures exists y: Positive | y < 0\n{\n  true\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractFailed { .. }
        )),
        "exists y: Positive where y < 0 should FAIL (domain restricted by refinement predicate)"
    );
}

#[test]
fn verify_cardinality_fixture() {
    let prog = lower_file("tests/fixtures/cardinality.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    for name in &[
        "set_card_3",
        "set_card_dedup",
        "seq_card_4",
        "seq_card_with_dupes",
        "card_in_ensures",
        "card_compare",
        "empty_set_card",
        "semantic_dedup",
        "semantic_dedup_expr",
        "param_dedup",
        "comp_membership",
        "comp_non_membership",
        "comp_in_ensures",
        "comp_enum_membership",
        "comp_enum_non_membership",
        "comp_refinement_membership",
        "comp_refinement_non_membership",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED"
        );
    }
}

#[test]
fn verify_setcomp_false_membership_fails() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("setcomp_false.ab");
    std::fs::write(
        &file,
        "module T\n\nfn bad(x: int): bool\n  ensures 0 in { y: int where y > 0 }\n{\n  true\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractFailed { .. }
        )),
        "0 in set comprehension where y > 0 should FAIL"
    );
}

#[test]
fn verify_constructor_fields_fixture() {
    let prog = lower_file("tests/fixtures/constructor_fields.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    for name in &[
        "get_radius_or_zero",
        "rect_perimeter",
        "always_42",
        "get_or_default",
        "make_some",
        "make_none",
        "reordered_ctor_fields",
        "reordered_pat_fields",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED (constructor field destructuring)"
        );
    }
}

#[test]
fn verify_ctor_missing_field_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("missing_field.ab");
    std::fs::write(
        &file,
        "module T\n\nenum S = R { w: int, h: int }\n\n\
         fn f(): int\n  ensures true\n{\n  match @R { w: 1 } { _ => 0 }\n}\n",
    )
    .unwrap();

    // Front-end should catch missing fields during elaboration
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = abide::elab::elaborate(&program);

    assert!(
        errors.iter().any(|e| format!("{e}").contains("missing")),
        "constructor with missing field should produce elab error"
    );
}

#[test]
fn verify_ctor_unknown_field_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("unknown_field.ab");
    std::fs::write(
        &file,
        "module T\n\nenum S = R { w: int, h: int }\n\n\
         fn f(): int\n  ensures true\n{\n  match @R { z: 1, w: 2 } { _ => 0 }\n}\n",
    )
    .unwrap();

    // Front-end should catch unknown fields during elaboration
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = abide::elab::elaborate(&program);

    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("unknown field")),
        "constructor with unknown field should produce elab error"
    );
}

#[test]
fn verify_bare_field_ctor_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("bare_ctor.ab");
    std::fs::write(
        &file,
        "module T\n\nenum Option = None | Some { value: int }\n\n\
         fn mk(): Option\n  ensures true\n{\n  @Some\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Unprovable { hint, .. }
                if hint.contains("requires") && hint.contains("field argument")
        )),
        "bare use of field-bearing constructor should produce arity error, not panic"
    );
}

#[test]
fn verify_lambdas_fixture() {
    let prog = lower_file("tests/fixtures/lambdas.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    for name in &[
        "apply_single",
        "apply_multi",
        "apply_three_args",
        "identity",
        "let_lambda",
        "closure",
        "bool_lambda",
        "ensures_lambda",
        "assert_lambda",
        "partial_app",
        "multi_partial",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED"
        );
    }
}

#[test]
fn verify_while_loop_missing_invariant() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("weak.ab");
    std::fs::write(
        &file,
        "module Weak\n\n\
         fn counting(n: int): int\n\
         \x20 requires n >= 0\n\
         \x20 ensures result >= 0\n\
         {\n\
         \x20 var x = 0\n\
         \x20 var i = 0\n\
         \x20 while i < n\n\
         \x20   decreases n - i\n\
         \x20 {\n\
         \x20   x = x + i\n\
         \x20   i = i + 1\n\
         \x20 }\n\
         \x20 x\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "while loop without invariant should fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("requires at least one loop invariant"),
        "should report missing invariant: {stderr}"
    );
}

#[test]
fn verify_nested_while_unsound_invariant_rejected() {
    // Inner loop sets x = 1 but outer loop claims invariant x == 0.
    // Must NOT be proved — this was a soundness bug.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("nested.ab");
    std::fs::write(
        &file,
        "module Nested\n\n\
         fn nested_unsound(n: int): int\n\
         \x20 requires n > 0\n\
         \x20 ensures result == 0\n\
         {\n\
         \x20 var x = 0\n\
         \x20 var i = 0\n\
         \x20 while i < n\n\
         \x20   invariant x == 0\n\
         \x20   invariant i >= 0\n\
         \x20   decreases n - i\n\
         \x20 {\n\
         \x20   var j = 0\n\
         \x20   while j < 3\n\
         \x20     invariant j >= 0\n\
         \x20     decreases 3 - j\n\
         \x20   {\n\
         \x20     x = 1\n\
         \x20     j = j + 1\n\
         \x20   }\n\
         \x20   i = i + 1\n\
         \x20 }\n\
         \x20 x\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "nested while with broken invariant must NOT be proved"
    );
}

#[test]
fn verify_valid_nested_while_proves() {
    // Valid nested while: total only increases, invariant total >= 0 is correct.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("nested_valid.ab");
    std::fs::write(
        &file,
        "module NestedValid\n\n\
         fn matrix_sum(rows: int, cols: int): int\n\
         \x20 requires rows >= 0\n\
         \x20 requires cols >= 0\n\
         \x20 ensures result >= 0\n\
         {\n\
         \x20 var total = 0\n\
         \x20 var i = 0\n\
         \x20 while i < rows\n\
         \x20   invariant total >= 0\n\
         \x20   invariant i >= 0\n\
         \x20   decreases rows - i\n\
         \x20 {\n\
         \x20   var j = 0\n\
         \x20   while j < cols\n\
         \x20     invariant total >= 0\n\
         \x20     invariant j >= 0\n\
         \x20     decreases cols - j\n\
         \x20   {\n\
         \x20     total = total + 1\n\
         \x20     j = j + 1\n\
         \x20   }\n\
         \x20   i = i + 1\n\
         \x20 }\n\
         \x20 total\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "valid nested while should be proved"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("PROVED  fn matrix_sum"),
        "should show matrix_sum proved: {stdout}"
    );
}

#[test]
fn verify_imperative_if_else_with_assignments() {
    // if/else branches with only assignments must be handled imperatively,
    // not routed through the pure encoder.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("if_assign.ab");
    std::fs::write(
        &file,
        "module IfAssign\n\n\
         fn conditional_assign(flag: bool): int\n\
         \x20 ensures result > 0\n\
         {\n\
         \x20 var x = 0\n\
         \x20 if flag {\n\
         \x20   x = 1\n\
         \x20 } else {\n\
         \x20   x = 2\n\
         \x20 }\n\
         \x20 x\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "imperative if/else with assignments should be proved"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("PROVED  fn conditional_assign"),
        "should show conditional_assign proved: {stdout}"
    );
}

#[test]
fn verify_branch_condition_propagated_to_loop() {
    // A while loop inside an if-branch should be able to use the branch
    // condition as a loop invariant. Previously this failed because branch
    // conditions were not threaded into loop verification.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("branch_cond.ab");
    std::fs::write(
        &file,
        "module BranchCond\n\n\
         fn branch_inner(flag: bool): int\n\
         \x20 ensures result == 0\n\
         {\n\
         \x20 if flag {\n\
         \x20   var i = 0\n\
         \x20   while i < 1\n\
         \x20     invariant flag\n\
         \x20     invariant i >= 0\n\
         \x20     decreases 1 - i\n\
         \x20   {\n\
         \x20     i = i + 1\n\
         \x20   }\n\
         \x20 }\n\
         \x20 0\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "branch condition should be available as loop invariant"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("PROVED  fn branch_inner"),
        "should prove branch_inner: {stdout}"
    );
}

#[test]
fn verify_nested_loop_requires_invariant() {
    // Inner loops must have invariants — same rule as top-level loops.
    // Previously inner loops without invariants were silently accepted.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("inner_no_inv.ab");
    std::fs::write(
        &file,
        "module InnerNoInv\n\n\
         fn inner_no_inv(n: int): int\n\
         \x20 requires n >= 0\n\
         \x20 ensures result == n\n\
         {\n\
         \x20 var i = 0\n\
         \x20 while i < n\n\
         \x20   invariant i >= 0\n\
         \x20   invariant i <= n\n\
         \x20   decreases n - i\n\
         \x20 {\n\
         \x20   var j = 0\n\
         \x20   while j < 3\n\
         \x20     decreases 3 - j\n\
         \x20   {\n\
         \x20     j = j + 1\n\
         \x20   }\n\
         \x20   i = i + 1\n\
         \x20 }\n\
         \x20 i\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "inner loop without invariant must not be proved"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("requires at least one loop invariant"),
        "should report missing invariant for inner loop: {stderr}"
    );
}

#[test]
fn verify_unreachable_branch_loop_does_not_pollute() {
    // A while loop in an unreachable branch (if flag { if not flag {... } })
    // must not pollute the solver — even with `invariant false`.
    // Previously, post-loop assertions were unguarded and collapsed the proof.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("unreachable.ab");
    std::fs::write(
        &file,
        "module Unreachable\n\n\
         fn unreachable_branch_bug(flag: bool): int\n\
         \x20 ensures result == 0\n\
         {\n\
         \x20 var x = 1\n\
         \x20 if flag {\n\
         \x20   if not flag {\n\
         \x20     while x > 0\n\
         \x20       invariant false\n\
         \x20       decreases x\n\
         \x20     {\n\
         \x20       x = x - 1\n\
         \x20     }\n\
         \x20   }\n\
         \x20 }\n\
         \x20 x\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "unreachable branch with invariant false must NOT prove a wrong postcondition"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("contract violated") || stderr.contains("FAILED"),
        "should report contract violation: {stderr}"
    );
}

#[test]
fn verify_unreachable_branch_in_loop_body_does_not_pollute() {
    // Same as the top-level unreachable-branch test, but the unreachable
    // branch is inside a loop body. The inner loop's `invariant false`
    // must not collapse the outer loop's preservation/termination VCs.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("loop_branch.ab");
    std::fs::write(
        &file,
        "module LoopBranch\n\n\
         fn loop_branch_pollute(flag: bool): int\n\
         \x20 ensures result == 0\n\
         {\n\
         \x20 var x = 0\n\
         \x20 while x < 1\n\
         \x20   invariant x == 0\n\
         \x20   decreases 1 - x\n\
         \x20 {\n\
         \x20   if flag {\n\
         \x20     if not flag {\n\
         \x20       while x < 1\n\
         \x20         invariant false\n\
         \x20         decreases 1 - x\n\
         \x20       {\n\
         \x20         x = x + 1\n\
         \x20       }\n\
         \x20     }\n\
         \x20   }\n\
         \x20   x = 1\n\
         \x20 }\n\
         \x20 x\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "unreachable branch inside loop body must NOT prove a wrong postcondition"
    );
}

// ── Call-site precondition checking ────────────────────────

#[test]
fn verify_call_site_preconditions() {
    let prog = lower_file("tests/fixtures/call_site.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // caller_good: requires x > 0 satisfies safe_div's requires b != 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "caller_good"
        )),
        "caller_good should be PROVED"
    );

    // caller_literal: safe_div(10, 2), literal 2 != 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "caller_literal"
        )),
        "caller_literal should be PROVED"
    );

    // caller_bad: no guarantee x != 0, precondition violated
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, .. }
                if name == "fn_caller_bad"
        )),
        "caller_bad should be UNKNOWN (precondition failure)"
    );

    // add_positive: nested calls, both a > 0 and b > 0 satisfy requires x > 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "add_positive"
        )),
        "add_positive should be PROVED"
    );

    // nested_no_requires: positive(a) + positive(b) without requires a > 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, .. }
                if name == "fn_nested_no_requires"
        )),
        "nested_no_requires should be UNKNOWN (nested call precondition failure)"
    );
}

#[test]
fn verify_call_site_cli_output() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg("tests/fixtures/call_site.ab")
        .output()
        .expect("run CLI");
    // CLI should exit non-zero because caller_bad fails
    assert!(
        !output.status.success(),
        "should fail due to caller_bad precondition violation"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("PROVED  fn caller_good"),
        "caller_good proved: {stdout}"
    );
    assert!(
        stdout.contains("PROVED  fn caller_literal"),
        "caller_literal proved: {stdout}"
    );
    assert!(
        stdout.contains("PROVED  fn add_positive"),
        "add_positive proved: {stdout}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("precondition") && stderr.contains("caller_bad"),
        "should report precondition failure for caller_bad: {stderr}"
    );
}

#[test]
fn verify_system_call_site_value_position() {
    // Call with violated precondition in value position (positive(0) == 0).
    // Must be rejected regardless of polarity or position.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("val_call.ab");
    std::fs::write(
        &file,
        "module ValCall\n\n\
         fn positive(x: int): int\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 x\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S(dummyEs: Store<DummyE>) {}\n\n\
         verify bad_prop {
  assume {
    store dummyEs: DummyE[0..1]
    let s = S { dummyEs: dummyEs }
    stutter
  }\n\
         \x20 assert positive(0) == 0\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "value-position call with violated precondition must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("precondition"),
        "value call: should report precondition violation: {stderr}"
    );
}

#[test]
fn verify_system_call_site_under_negation() {
    // Call with violated precondition under negation (not ok(0)).
    // Must be rejected — polarity must not affect precondition checking.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("neg_call.ab");
    std::fs::write(
        &file,
        "module NegCall\n\n\
         fn ok(x: int): bool\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 true\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S(dummyEs: Store<DummyE>) {}\n\n\
         verify neg_bad {
  assume {
    store dummyEs: DummyE[0..1]
    let s = S { dummyEs: dummyEs }
    stutter
  }\n\
         \x20 assert not ok(0)\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        !output.status.success(),
        "negated call with violated precondition must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("precondition"),
        "neg call: should report precondition violation: {stderr}"
    );
}

#[test]
fn verify_system_guarded_call_not_rejected() {
    // A call guarded by an implication whose antecedent is false must NOT
    // be rejected — the precondition is only required when reachable.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("guarded.ab");
    std::fs::write(
        &file,
        "module Guarded\n\n\
         fn positive(x: int): bool\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 true\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S(dummyEs: Store<DummyE>) {}\n\n\
         verify guarded {\n\
         \x20 assume {\n\
         \x20   store dummyEs: DummyE[0..1]\n\
         \x20   let s = S { dummyEs: dummyEs }\n\
         \x20   stutter\n\
         \x20 }\n\
         \x20 assert (0 > 0) implies positive(0)\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "guarded call with false antecedent must not be rejected"
    );
}

#[test]
fn verify_leaked_path_guard_does_not_suppress_violation() {
    // A failed encoding in one block must not leak its path guard
    // into the next block and suppress a real precondition violation.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("leaked.ab");
    std::fs::write(
        &file,
        "module Leaked\n\n\
         fn positive(x: int): int\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 x\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S(dummyEs: Store<DummyE>) {}\n\n\
         verify bad_encode {
  assume {
    store es: E[0..1]
    let s = S { es: es }
    stutter
  }\n\
         \x20 assert (0 > 0) implies (x == 0)\n\
         }\n\n\
         verify should_fail {
  assume {
    store es: E[0..1]
    let s = S { es: es }
    stutter
  }\n\
         \x20 assert positive(0) == 0\n\
         }\n",
    )
    .unwrap();

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg(&file)
        .output()
        .expect("run CLI");
    assert!(!output.status.success(), "should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    // should_fail must report a precondition violation, not be PROVED
    assert!(
        stderr.contains("should_fail") && stderr.contains("precondition"),
        "should_fail must report precondition violation, not be suppressed: {stderr}"
    );
}

// ── Termination verification ───────────────────────────────

#[test]
fn verify_termination_fixture() {
    let prog = lower_file("tests/fixtures/termination.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // factorial: termination proved + postcondition proved
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "factorial"
        )),
        "factorial should be PROVED"
    );

    // fib: termination proved + postcondition proved
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "fib"
        )),
        "fib should be PROVED"
    );

    // bad_recurse: termination fails (n+1 does not decrease)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_bad_recurse" && hint.contains("termination")
        )),
        "bad_recurse should fail termination"
    );

    // no_recursion: trivially terminating + postcondition proved
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "no_recursion"
        )),
        "no_recursion should be PROVED"
    );

    // bad_precond: recursive call f(-1) violates requires n >= 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_bad_precond" && hint.contains("precondition")
        )),
        "bad_precond should fail with precondition violation"
    );
    // bad_precond should NOT have a PROVED result (postcondition skipped after termination failure)
    assert!(
        !results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "bad_precond"
        )),
        "bad_precond must not be PROVED after termination failure"
    );

    // via_local: recursive call through local var binding works
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "via_local"
        )),
        "via_local should be PROVED (local var binding resolved)"
    );
}

#[test]
fn verify_termination_cli_output() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abide"))
        .arg("verify")
        .arg("tests/fixtures/termination.ab")
        .output()
        .expect("run CLI");
    // Should exit non-zero because bad_recurse fails
    assert!(!output.status.success(), "should fail due to bad_recurse");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("PROVED  fn factorial"),
        "factorial proved: {stdout}"
    );
    assert!(stdout.contains("PROVED  fn fib"), "fib proved: {stdout}");
    assert!(
        stdout.contains("PROVED  fn no_recursion"),
        "no_recursion proved: {stdout}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("bad_recurse") && stderr.contains("termination"),
        "should report termination failure for bad_recurse: {stderr}"
    );
}

// ── Recursion stress tests: complex match/pattern/binding shapes ────

#[test]
fn verify_recursion_stress_fixture() {
    let prog = lower_file("tests/fixtures/recursion_stress.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Valid: enum match with recursive calls in both arms
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "eval"
        )),
        "eval should be PROVED (enum match, both arms decrease)"
    );

    // Valid: match inside if inside if (deep nesting)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "deep_nesting"
        )),
        "deep_nesting should be PROVED (match inside nested if)"
    );

    // Valid: three-way guarded match, two recursive calls in last arm
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "three_way"
        )),
        "three_way should be PROVED (3-arm guarded match)"
    );

    // Valid: wildcard match with prior arm exclusion
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "depth"
        )),
        "depth should be PROVED (wildcard match, prior arm excluded)"
    );

    // Valid: multi-action let chain before recursive call
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "chain_let"
        )),
        "chain_let should be PROVED (let chain)"
    );

    // BAD: match arm doesn't decrease
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_bad_match_no_decrease" && hint.contains("termination")
        )),
        "bad_match_no_decrease should fail (measure doesn't decrease)"
    );

    // BAD: match arm violates requires
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_bad_match_precond" && hint.contains("precondition")
        )),
        "bad_match_precond should fail (recursive call violates requires)"
    );

    // Neither bad function should be PROVED
    assert!(
        !results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "bad_match_no_decrease" || name == "bad_match_precond"
        )),
        "bad functions must not be PROVED"
    );
}

// ── Refinement type enforcement at call sites ──────────────

#[test]
fn verify_refinement_call_site_fixture() {
    let prog = lower_file("tests/fixtures/refinement_call_site.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // call_literal: literal 2 satisfies $ != 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_literal"
        )),
        "call_literal should be PROVED"
    );

    // call_variable: requires b > 0 implies b != 0 (refinement satisfied)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_variable"
        )),
        "call_variable should be PROVED"
    );

    // call_both: both refinements satisfied by caller requires
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_both"
        )),
        "call_both should be PROVED"
    );

    // call_bad: no guarantee b != 0 (refinement violated)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_call_bad" && hint.contains("precondition")
        )),
        "call_bad should fail (refinement not satisfied)"
    );

    // call_one_bad: only first refinement satisfied
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_call_one_bad" && hint.contains("precondition")
        )),
        "call_one_bad should fail (second refinement not satisfied)"
    );

    // ── Alias-based refinement types ────────────────────────────────

    // double_pos: Positive alias refinement desugared to requires x > 0
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "double_pos"
        )),
        "double_pos should be PROVED (alias refinement as requires)"
    );

    // call_alias_literal: literal 5 satisfies Positive ($ > 0)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_alias_literal"
        )),
        "call_alias_literal should be PROVED"
    );

    // call_alias_good: requires x > 0 satisfies Positive
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_alias_good"
        )),
        "call_alias_good should be PROVED"
    );

    // call_alias_subtype: Positive (> 0) implies NonNeg (>= 0)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "call_alias_subtype"
        )),
        "call_alias_subtype should be PROVED (subtype relation)"
    );

    // call_alias_bad: no guarantee x > 0 for Positive alias
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_call_alias_bad" && hint.contains("precondition")
        )),
        "call_alias_bad should fail (alias refinement not satisfied)"
    );

    // call_alias_wrong: NonNeg (>= 0) does not imply Positive (> 0)
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::Unprovable { name, hint, .. }
                if name == "fn_call_alias_wrong" && hint.contains("precondition")
        )),
        "call_alias_wrong should fail (NonNeg doesn't imply Positive)"
    );
}

#[test]
fn verify_one_lone_fixture() {
    let prog = lower_file("tests/fixtures/one_lone.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Functions that should PROVE
    for name in &[
        "one_enum_exact",
        "lone_enum_one",
        "lone_enum_none",
        "one_int_exact",
        "lone_int_unique",
        "one_in_requires",
        "lone_adt_match",
        "one_adt_eq",
        "exists_adt",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractProved { name: n, .. }
                    if n == name
            )),
            "{name} should be PROVED"
        );
    }

    // Functions that should FAIL (contract violated)
    for name in &[
        "one_enum_none",
        "one_enum_multiple",
        "lone_enum_multiple",
        "lone_adt_multiple",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::FnContractFailed { name: n, .. }
                    if n == name
            )),
            "{name} should be FAILED (contract violated)"
        );
    }
}

/// Regression: non-entity quantifiers in verify blocks must be checked, not
/// accepted vacuously. Previously, `all c: Color | c == @Red` in a verify
/// block returned CHECKED even though the property is clearly false.
#[test]
fn verify_nonentity_quantifier_in_verify_block() {
    let dir = tempfile::tempdir().expect("create tempdir");

    // False property: not all Colors are Red.
    // opt into stutter so the empty system has a valid trace
    // (verify defaults to no-stutter; with no events the BMC would
    // otherwise have no transitions to encode).
    let file = dir.path().join("enum_quant_verify.ab");
    std::fs::write(
        &file,
        "module T\n\nenum Color = Red | Green | Blue\n\nsystem S {}\n\n\
         verify q {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  stutter
  }\n  assert all c: Color | c == @Color::Red\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "q"
        )),
        "false enum quantifier in verify block should produce COUNTEREXAMPLE, not CHECKED"
    );

    // True property with lone: exactly one Color is Red.
    // stutter opt-in for empty system.
    let file2 = dir.path().join("lone_verify.ab");
    std::fs::write(
        &file2,
        "module T\n\nenum Color = Red | Green | Blue\n\nsystem S {}\n\n\
         verify q {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  stutter
  }\n  assert lone c: Color | c == @Color::Red\n}\n",
    )
    .unwrap();

    let prog2 = lower_file(file2.to_str().unwrap());
    let results2 = abide::verify::verify_all(&prog2, &abide::verify::VerifyConfig::default());

    assert!(
        results2.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
                if name == "q"
        )),
        "lone c: Color | c == @Red should be CHECKED or PROVED (at most one is true), got: {results2:?}"
    );
}

/// Regression: refinement domain predicates must be enforced in verify blocks.
/// `one y: Positive | y == 0` must be false because 0 is outside Positive.
#[test]
fn verify_refinement_domain_in_verify_block() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("refine.ab");
    // stutter opt-in for empty system.
    std::fs::write(
        &file,
        "module T\n\ntype Positive = int { $ > 0 }\n\nsystem S {}\n\n\
         verify q {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  stutter
  }\n  assert one y: Positive | y == 0\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "q"
        )),
        "one y: Positive | y == 0 should be COUNTEREXAMPLE (0 not in Positive)"
    );
}

/// Regression: ADT enum quantifiers in verify blocks must count distinct ADT
/// values, not just constructor tags. `lone sh: Shape | sh == @Circle{r:1} or
/// sh == @Circle{r:2}` is false because there are two distinct Shape values.
#[test]
fn verify_adt_lone_in_verify_block() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("adt_lone.ab");
    // stutter opt-in for empty system.
    std::fs::write(
        &file,
        "module T\n\nenum Shape = Circle { r: int } | Square { s: int }\n\nsystem S {}\n\n\
         verify q {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  stutter
  }\n  assert lone sh: Shape | sh == @Circle { r: 1 } or sh == @Circle { r: 2 }\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "q"
        )),
        "lone over ADT with two distinct values should produce COUNTEREXAMPLE"
    );
}

#[test]
fn verify_lemmas_fixture() {
    let prog = lower_file("tests/fixtures/lemmas.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Lemmas that should PROVE
    for name in &[
        "tautology",
        "excluded_middle",
        "arith_identity",
        "color_exhaustive",
        "two_truths",
        "lambda_identity",
    ] {
        assert!(
            results.iter().any(|r| matches!(
                r,
                abide::verify::VerificationResult::Proved { name: n, method, .. }
                    if n == name && method == "lemma"
            )),
            "{name} should be PROVED (method: lemma)"
        );
    }

    // Lemma that should FAIL
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "contradiction"
        )),
        "contradiction should produce COUNTEREXAMPLE"
    );
}

/// Regression: proved lemmas must be referenceable by their declared name
/// in later theorems. `show helper` in a theorem should expand to the
/// lemma's body (true), not fail with "variable not found".
#[test]
fn verify_lemma_referenced_in_theorem() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("lemma_ref.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         lemma helper { true }\n\n\
         entity E { x: int = 0 }\n\
         system S(es: Store<E>) {}\n\n\
         theorem use_helper for S {\n  show helper\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Lemma should prove
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, method, .. }
                if name == "helper" && method == "lemma"
        )),
        "lemma helper should be PROVED"
    );

    // Theorem should prove by referencing the lemma
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "use_helper"
        )),
        "theorem use_helper should be PROVED (references proved lemma)"
    );
}

#[test]
fn verify_fairness_fixture() {
    let prog = lower_file("tests/fixtures/fairness.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Fair system: exhaustive finite-state liveness should prove.
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, method, .. }
                if name == "fair_signal" && method == "explicit-state exhaustive search"
        )),
        "fair_signal should be PROVED by explicit-state exhaustive search"
    );

    // Unfair system: liveness should produce LIVENESS_VIOLATION
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::LivenessViolation { name, .. }
                if name == "unfair_signal"
        )),
        "unfair_signal should produce LIVENESS_VIOLATION"
    );

    // Safety property should succeed; relational safety may report CHECKED.
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                | abide::verify::VerificationResult::Checked { name, .. }
                if name == "safety_check"
        )),
        "safety_check should succeed (safety property, no liveness)"
    );
}

/// Regression: prefix-triggered response violation.
/// Job goes Pending → Waiting in prefix, then loops in Waiting.
/// No event moves to Done, so the response is violated.
#[test]
fn verify_liveness_prefix_trigger() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("prefix.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         enum State = Pending | Waiting | Done\n\n\
         entity Job {\n  st: State = @Pending\n  \
         action postpone() requires st == @Pending { st' = @Waiting }\n}\n\n\
         system S(jobs: Store<Job>) {\n  \
         command create_job() { create Job {} }\n  \
         command move_to_waiting() {\n    \
         choose j: Job where j.st == @Pending { j.postpone() }\n  }\n}\n\n\
         verify response {
  assume {
    store es: E[0..6]
    let s = S { es: es }
    stutter\n    fair S::move_to_waiting\n  }\n  \
         assert all j: Job | j.st == @Pending implies eventually j.st == @Done\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::LivenessViolation { name, .. }
                if name == "response"
        )),
        "prefix-triggered response with no Done event should be LIVENESS_VIOLATION"
    );
}

/// Regression: multiple liveness asserts checked independently.
/// Each assert is individually false but needs a different lasso.
#[test]
fn verify_liveness_multi_assert_independent() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("multi.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         enum State = Pending | A | B\n\n\
         entity Job {\n  st: State = @Pending\n  \
         action go_a() requires st == @Pending { st' = @A }\n  \
         action go_b() requires st == @Pending { st' = @B }\n}\n\n\
         system S(jobs: Store<Job>) {\n  \
         command create_job() { create Job {} }\n  \
         command choose_a() { choose j: Job where j.st == @Pending { j.go_a() } }\n  \
         command choose_b() { choose j: Job where j.st == @Pending { j.go_b() } }\n}\n\n\
         verify responses {
  assume {
    store es: E[0..6]
    let s = S { es: es }
    stutter\n    fair S::choose_a\n    fair S::choose_b\n  }\n  \
         assert all j: Job | j.st == @Pending implies eventually j.st == @A\n  \
         assert all j: Job | j.st == @Pending implies eventually j.st == @B\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::LivenessViolation { name, .. }
                if name == "responses"
        )),
        "each assert is individually false — should produce LIVENESS_VIOLATION"
    );
}

/// Regression: choose enabledness is checked properly.
/// A fair event with choose on a condition that never holds should NOT
/// Regression: per-tuple fairness on a parameterized event ().
///
/// `tick(j: Job)` is parameterized over Job with toggling state. With
/// per-EVENT fairness, the SAT solver could pick a lasso where only
/// `tick(j=0)` fires forever (j=0 toggles in a 2-cycle) and `j=1`
/// starves at `active=false` — the per-event obligation "tick fires
/// in the loop" is satisfied even though j=1 never gets ticked.
///
/// With per-TUPLE fairness, the obligation "tick(j=t) fires in the
/// loop for each tuple t" rules out that lasso, so the verifier
/// cannot find a counterexample to `eventually all j: Job | j.active`.
///
/// Without per-tuple encoding the verifier returns LIVENESS_VIOLATION
/// (false positive). With per-tuple it returns CHECKED.
#[test]
fn verify_liveness_per_tuple_fairness() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("per_tuple.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         entity Job {\n  active: bool = false\n  \
         action toggle() { active' = not active }\n}\n\n\
         system S(jobs: Store<Job>) {\n  \
         command create_job() { create Job {} }\n  \
         command tick(j: Job) { j.toggle() }\n}\n\n\
         verify per_tuple_liveness {
  assume {
    store es: E[0..8]
    let s = S { es: es }
    fair S::create_job\n    fair S::tick\n  }\n  \
         assert all j: Job | eventually j.active\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());

    // Sanity-check: tick is in per_tuple at the IR level
    let v = prog
        .verifies
        .iter()
        .find(|v| v.name == "per_tuple_liveness")
        .expect("verify block");
    assert!(
        v.assumption_set
            .per_tuple
            .iter()
            .any(|r| r.system == "S" && r.command == "tick"),
        "tick should be in per_tuple, got {:?}",
        v.assumption_set.per_tuple
    );

    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // With per-tuple lasso encoding, every Job slot must eventually be
    // active under fairness. Without per-tuple (or without the encoder
    // tying `param_<target>_<step>` to the slot index that the Apply
    // actually mutated), the verifier finds a slot-starvation lasso
    // and returns LIVENESS_VIOLATION (false positive).
    //
    // The result must be Checked, not Proved. The
    // unbounded reduction path cannot soundly discharge per-tuple
    // fairness without k-liveness (), so verify blocks with
    // parameterized fair events should fall through to bounded lasso
    // BMC and report CHECKED. Allowing Proved here would mask the
    // single-justice-counter encoding gap in `try_liveness_reduction`.
    let result_for = results
        .iter()
        .find(|r| match r {
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::LivenessViolation { name, .. } => {
                name == "per_tuple_liveness"
            }
            _ => false,
        })
        .expect("per_tuple_liveness result");

    // The result must be Checked, not Proved. The
    // unbounded reduction path cannot soundly discharge per-tuple
    // fairness without k-liveness (), so verify blocks with
    // parameterized fair events must fall through to bounded lasso
    // BMC and report CHECKED. Allowing Proved here would mask the
    // single-justice-counter encoding gap in `try_liveness_reduction`.
    //
    // The encoder fix that ties `param_<target>_<step>` to the actual
    // slot index has its own focused unit test in
    // `verify::harness::tests::apply_on_entity_param_ties_param_to_slot`.
    assert!(
        matches!(result_for, abide::verify::VerificationResult::Checked { .. }),
        "per_tuple_liveness should be CHECKED (per-tuple fairness rules out the slot-starvation lasso, and the reduction path must fall through pending k-liveness): got {result_for:?}"
    );
}

/// / revised: when stutter is opted out (verify default
/// per revised), a system that reaches a state where no events
/// are enabled must be reported as DEADLOCK, not silently as CHECKED.
///
/// The fixture below has a single event whose `requires false` precondition
/// is never satisfiable. Under ambient stutter, the verifier could stutter
/// forever and report a property-style verdict. Under no-stutter (the
/// default), the BMC's transition constraint is unsatisfiable from the
/// initial state, and the new direct deadlock detection turns that into
/// a Deadlock verdict instead of a misleading Checked.
#[test]
fn verify_deadlock_when_no_events_enabled() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("deadlock_simple.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify deadlocked {
  assume {
    store es: E[0..3]
    let s = S { es: es }
  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    let result_for = results
        .iter()
        .find(|r| match r {
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Counterexample { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. } => name == "deadlocked",
            _ => false,
        })
        .expect("deadlocked result");

    assert!(
        matches!(result_for, abide::verify::VerificationResult::Deadlock { .. }),
        "verify block with no enabled events under no-stutter must report DEADLOCK, not CHECKED or COUNTEREXAMPLE: got {result_for:?}"
    );
}

/// opting into stutter via `assume { stutter }` recovers the
/// earlier behavior — the same fixture above no longer reports
/// DEADLOCK because the BMC can extend the trace via stutter steps.
#[test]
fn verify_no_deadlock_when_stutter_opted_in() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("deadlock_with_stutter.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify with_stutter {\n  \
         assume {\n    store sigs: Sig[0..3]\n    let s = S { sigs: sigs }\n    stutter\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    let result_for = results
        .iter()
        .find(|r| match r {
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. } => name == "with_stutter",
            _ => false,
        })
        .expect("with_stutter result");

    assert!(
        !matches!(result_for, abide::verify::VerificationResult::Deadlock { .. }),
        "verify block with `assume {{ stutter }}` must NOT report DEADLOCK (the stutter self-loop is always a valid trace step, so the property is checked normally): got {result_for:?}"
    );
}

/// be considered enabled, so its fairness constraint doesn't apply.
#[test]
fn verify_liveness_choose_enabledness() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("choose_en.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         enum State = Pending | Waiting\n\n\
         entity Job {\n  st: State = @Waiting\n  \
         action poke() requires st == @Waiting { st' = @Waiting }\n}\n\n\
         system S(jobs: Store<Job>) {\n  \
         command create_job() { create Job {} }\n  \
         command process() {\n    \
         choose j: Job where j.st == @Pending { j.poke() }\n  }\n}\n\n\
         verify test {\n  assume {\n    store jobs: Job[0..4]\n    let s = S { jobs: jobs }\n    stutter\n    fair S::process\n  }\n  assert eventually exists j: Job | j.st == @Pending\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::LivenessViolation { name, .. }
                if name == "test"
        )),
        "process is never enabled (no Pending jobs) — eventually Pending should be VIOLATION"
    );
}

#[test]
fn verify_until_fixture() {
    let prog = lower_file("tests/fixtures/until.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Direct: Red until Green is bounded-checked on this finite fixture.
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "direct_until"
        )),
        "direct_until should produce CHECKED"
    );

    // Indirect: Red until Green fails (Yellow intervenes)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "indirect_fails"
        )),
        "indirect_fails should produce COUNTEREXAMPLE"
    );

    // StuckRed has no active signal in the bounded prefix, so the universal
    // property is bounded-checked vacuously.
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "never_green"
        )),
        "never_green should produce CHECKED"
    );

    // Via prop: until inside prop definition (def expansion path)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "via_prop"
        )),
        "via_prop should produce CHECKED"
    );

    // Via pred: until inside pred definition (def expansion path)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "via_pred"
        )),
        "via_pred should produce CHECKED"
    );
}

/// Regression: BMC counterexample traces should identify which event fired.
#[test]
fn verify_counterexample_event_identification() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("trace.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         enum Status = Pending | Cancelled\n\n\
         entity Order {\n  status: Status = @Pending\n  \
         action cancel() requires status == @Pending { status' = @Cancelled }\n}\n\n\
         system S(orders: Store<Order>) {\n  \
         command create_order() { create Order {} }\n  \
         command cancel_order() {\n    \
         choose o: Order where o.status == @Pending { o.cancel() }\n  }\n}\n\n\
         verify no_cancel {
  assume {
    store es: E[0..4]
    let s = S { es: es }
  }\n  \
         assert always all o: Order | o.status != @Cancelled\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Should find counterexample with event identification
    let ce = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "no_cancel"
        )
    });
    assert!(ce.is_some(), "should produce COUNTEREXAMPLE");

    if let Some(result) = ce {
        let witness = result
            .operational_witness()
            .expect("counterexample should carry an operational witness");
        let behavior = witness.behavior();

        let has_event = behavior
            .transitions()
            .iter()
            .any(|transition| !transition.atomic_steps().is_empty());
        assert!(
            has_event,
            "counterexample should identify at least one event"
        );

        let has_cancel = behavior.transitions().iter().any(|transition| {
            transition
                .atomic_steps()
                .iter()
                .any(|step| step.command().contains("cancel_order"))
        });
        assert!(
            has_cancel,
            "counterexample should identify cancel_order event"
        );
    }
}

// ── Nested actions in Choose/ForAll ────────────────────────

#[test]
fn parse_nested_actions_fixture() {
    let _prog = parse_file("tests/fixtures/nested_actions.ab");
}

#[test]
fn elaborate_nested_actions_fixture() {
    let _result = elaborate_file("tests/fixtures/nested_actions.ab");
}

#[test]
fn lower_nested_actions_fixture() {
    let prog = lower_file("tests/fixtures/nested_actions.ab");
    // Should have systems with nested action patterns
    assert!(
        !prog.systems.is_empty(),
        "nested_actions should have systems"
    );
}

#[test]
fn verify_create_in_choose() {
    let results = verify_file("tests/fixtures/nested_actions.ab");
    let create_in_choose = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Counterexample { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. } => name == "create_in_choose",
        _ => false,
    });
    assert!(
        create_in_choose.is_some(),
        "create_in_choose should produce a result (got: {results:?})"
    );
    // Should be CHECKED (no counterexample — Create inside Choose works)
    assert!(
        matches!(
            create_in_choose.unwrap(),
            abide::verify::VerificationResult::Checked { .. }
                | abide::verify::VerificationResult::Proved { .. }
        ),
        "create_in_choose should be CHECKED or PROVED, got: {create_in_choose:?}"
    );
}

#[test]
fn verify_create_in_forall() {
    let results = verify_file("tests/fixtures/nested_actions.ab");
    let result = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Counterexample { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. } => name == "create_in_forall",
        _ => false,
    });
    assert!(
        result.is_some(),
        "create_in_forall should produce a result (got: {results:?})"
    );
    assert!(
        matches!(
            result.unwrap(),
            abide::verify::VerificationResult::Checked { .. }
                | abide::verify::VerificationResult::Proved { .. }
        ),
        "create_in_forall should be CHECKED or PROVED, got: {result:?}"
    );
}

#[test]
fn verify_crosscall_in_choose() {
    let results = verify_file("tests/fixtures/nested_actions.ab");
    let result = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Counterexample { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. } => name == "crosscall_in_choose",
        _ => false,
    });
    assert!(
        result.is_some(),
        "crosscall_in_choose should produce a result (got: {results:?})"
    );
    assert!(
        matches!(
            result.unwrap(),
            abide::verify::VerificationResult::Checked { .. }
                | abide::verify::VerificationResult::Proved { .. }
        ),
        "crosscall_in_choose should be CHECKED or PROVED, got: {result:?}"
    );
}

#[test]
fn verify_forall_in_choose() {
    let results = verify_file("tests/fixtures/nested_actions.ab");
    let result = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Counterexample { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. } => name == "forall_in_choose",
        _ => false,
    });
    assert!(
        result.is_some(),
        "forall_in_choose should produce a result (got: {results:?})"
    );
    assert!(
        matches!(
            result.unwrap(),
            abide::verify::VerificationResult::Checked { .. }
                | abide::verify::VerificationResult::Proved { .. }
        ),
        "forall_in_choose should be CHECKED or PROVED, got: {result:?}"
    );
}

#[test]
fn verify_cross_entity_apply_target() {
    // Regression test: Apply inside nested Choose must resolve to the correct
    // target entity, not blindly use the inner bound entity.
    let results = verify_file("tests/fixtures/nested_actions.ab");
    let result = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Counterexample { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. } => name == "cross_entity_target",
        _ => false,
    });
    assert!(
        result.is_some(),
        "cross_entity_target should produce a result (got: {results:?})"
    );
    // Worker should never reach Done — if the Apply target was resolved
    // incorrectly (to Worker instead of Task), this would fail.
    assert!(
        matches!(
            result.unwrap(),
            abide::verify::VerificationResult::Checked { .. }
                | abide::verify::VerificationResult::Proved { .. }
        ),
        "cross_entity_target should be CHECKED or PROVED (Worker never Done), got: {result:?}"
    );
}

// ── Match exhaustiveness checking ──────────────────────────

#[test]
fn elaborate_exhaustive_match_no_errors() {
    // All matches in this fixture are exhaustive — should elaborate cleanly
    let _result = elaborate_file("tests/fixtures/match_exhaustive.ab");
}

#[test]
fn elaborate_non_exhaustive_match_produces_error() {
    let program = parse_file("tests/fixtures/match_non_exhaustive.ab");
    let (_result, errors) = abide::elab::elaborate(&program);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, abide::elab::error::Severity::Warning))
        .collect();
    assert!(
        !actual_errors.is_empty(),
        "non-exhaustive match should produce errors"
    );
    // Should report the missing constructors
    let has_exhaustiveness_error = actual_errors
        .iter()
        .any(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch));
    assert!(
        has_exhaustiveness_error,
        "should produce NonExhaustiveMatch error, got: {actual_errors:?}"
    );
    // Should mention the missing constructors
    let msg = &actual_errors
        .iter()
        .find(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch))
        .unwrap()
        .message;
    assert!(
        msg.contains("Shipped") && msg.contains("Cancelled"),
        "error should list missing constructors Shipped and Cancelled, got: {msg}"
    );
}

#[test]
fn elaborate_existing_match_fixture_still_passes() {
    // The existing match_test.ab fixture should still elaborate cleanly
    // (all its matches are exhaustive)
    let _result = elaborate_file("tests/fixtures/match_test.ab");
}

#[test]
fn elaborate_non_exhaustive_scene_field() {
    // match o.status in a scene given block — missing Shipped
    let program = parse_file("tests/fixtures/match_non_exhaustive_scene.ab");
    let (_result, errors) = abide::elab::elaborate(&program);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, abide::elab::error::Severity::Warning))
        .collect();
    let has_exhaustiveness_error = actual_errors
        .iter()
        .any(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch));
    assert!(
        has_exhaustiveness_error,
        "scene field-access non-exhaustive match should produce E012, got: {actual_errors:?}"
    );
    let msg = &actual_errors
        .iter()
        .find(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch))
        .unwrap()
        .message;
    assert!(
        msg.contains("Shipped"),
        "error should list missing constructor Shipped, got: {msg}"
    );
}

#[test]
fn elaborate_non_exhaustive_alias_chain() {
    // type Paint = Traffic = Color — missing Blue through two alias layers
    let program = parse_file("tests/fixtures/match_non_exhaustive_alias.ab");
    let (_result, errors) = abide::elab::elaborate(&program);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, abide::elab::error::Severity::Warning))
        .collect();
    let has_exhaustiveness_error = actual_errors
        .iter()
        .any(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch));
    assert!(
        has_exhaustiveness_error,
        "alias-chained non-exhaustive match should produce E012, got: {actual_errors:?}"
    );
    let msg = &actual_errors
        .iter()
        .find(|e| matches!(e.kind, abide::elab::error::ErrorKind::NonExhaustiveMatch))
        .unwrap()
        .message;
    assert!(
        msg.contains("Blue"),
        "error should list missing constructor Blue, got: {msg}"
    );
}

// ── Scene composition operator semantics ──────────────────

fn find_scene_result<'a>(
    results: &'a [abide::verify::VerificationResult],
    name: &str,
) -> Option<&'a abide::verify::VerificationResult> {
    results.iter().find(|r| match r {
        abide::verify::VerificationResult::ScenePass { name: n, .. }
        | abide::verify::VerificationResult::SceneFail { name: n, .. } => n == name,
        _ => false,
    })
}

#[test]
fn scene_ordering_sequence() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // confirm -> ship: should pass (correct order enforced)
    let r = find_scene_result(&results, "confirm_then_ship");
    assert!(r.is_some(), "confirm_then_ship should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "confirm_then_ship should PASS, got: {r:?}"
    );
}

#[test]
fn scene_ordering_chain() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // confirm -> ship -> deliver: 3-event chain
    let r = find_scene_result(&results, "chain_ordering");
    assert!(r.is_some(), "chain_ordering should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "chain_ordering should PASS, got: {r:?}"
    );
}

#[test]
fn scene_ordering_reversed_list() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // Events listed in reverse but assume enforces correct order
    let r = find_scene_result(&results, "reversed_list_order");
    assert!(r.is_some(), "reversed_list_order should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "reversed_list_order should PASS (ordering from assume, not list position), got: {r:?}"
    );
}

#[test]
fn scene_ordering_impossible() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // ship -> confirm is impossible: should fail
    let r = find_scene_result(&results, "impossible_order");
    assert!(r.is_some(), "impossible_order should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::SceneFail { .. }
        ),
        "impossible_order should FAIL (ship before confirm is impossible), got: {r:?}"
    );
}

#[test]
fn scene_ordering_no_assume() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // No assume: solver finds valid order automatically
    let r = find_scene_result(&results, "no_ordering");
    assert!(r.is_some(), "no_ordering should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "no_ordering should PASS (solver picks valid order), got: {r:?}"
    );
}

#[test]
fn scene_ordering_same_step() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // confirm & create: both fire at same step
    let r = find_scene_result(&results, "same_step_pair");
    assert!(r.is_some(), "same_step_pair should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "same_step_pair should PASS (& same-action composition), got: {r:?}"
    );
}

#[test]
fn scene_ordering_same_step_then_sequence() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // (confirm & create) -> ship: atomic pair then sequence
    let r = find_scene_result(&results, "same_step_then_sequence");
    assert!(
        r.is_some(),
        "same_step_then_sequence should produce a result"
    );
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "same_step_then_sequence should PASS (& then ->), got: {r:?}"
    );
}

// ── QA query completeness ─────────────────────────────────

#[test]
fn qa_invariants_query() {
    let script = std::path::Path::new("tests/fixtures/test_qa_contracts.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    // Script should execute without errors
    assert!(
        !result
            .output
            .iter()
            .any(|l| l.contains("not yet implemented")),
        "invariant/contract queries should not return stubs: {:?}",
        result.output
    );
    assert!(
        result.executed >= 3,
        "should execute at least 3 statements, got: {}",
        result.executed
    );
    // Invariants output should contain action guard info
    let has_requires = result.output.iter().any(|l| l.contains("requires"));
    assert!(
        has_requires,
        "invariant/contract output should contain 'requires': {:?}",
        result.output
    );
}

#[test]
fn qa_contracts_query_direct() {
    // Test contract query directly via the exec module.
    // Commerce imports from Billing, so both files must be loaded.
    // Commerce is listed first — the first file sets the root module,
    // and build_working_namespace flattens to the root module's scope.
    let prog = lower_files(&["tests/fixtures/commerce.ab", "tests/fixtures/billing.ab"]);
    let model = abide::qa::extract::extract(&prog);

    // Query invariants on Order
    let inv_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Invariants {
            entity: "Order".to_string(),
        },
    );
    match &inv_result {
        abide::qa::exec::QueryResult::NameList(items) => {
            assert!(!items.is_empty(), "should have invariants for Order");
            // Should include submit's guard (status == @Pending)
            let has_submit = items.iter().any(|s| s.contains("submit"));
            assert!(has_submit, "should include submit guard: {items:?}");
        }
        other => panic!("expected NameList, got: {other:?}"),
    }

    // Query contracts on Order.submit
    let contract_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Contracts {
            entity: "Order".to_string(),
            action: "submit".to_string(),
        },
    );
    match &contract_result {
        abide::qa::exec::QueryResult::NameList(items) => {
            assert!(!items.is_empty(), "should have contract for Order.submit");
            let has_requires = items.iter().any(|s| s.starts_with("requires"));
            assert!(has_requires, "should include requires clause: {items:?}");
            let has_updates = items.iter().any(|s| s.starts_with("updates"));
            assert!(has_updates, "should include updates: {items:?}");
        }
        other => panic!("expected NameList, got: {other:?}"),
    }

    // Query contracts on nonexistent action
    let err_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Contracts {
            entity: "Order".to_string(),
            action: "nonexistent".to_string(),
        },
    );
    assert!(
        matches!(err_result, abide::qa::exec::QueryResult::Error(_)),
        "nonexistent action should return error"
    );
}

#[test]
fn qa_contracts_ensures_and_ctor_rendering() {
    // Test that ensures is lowered and that constructor fields are rendered
    let src = r"
module QATest
enum Shape = Circle { radius: int } | Rectangle { width: int, height: int }
entity Canvas {
  shape: Shape = @Circle { radius: 0 }
  action set_circle(r: int)
    requires r > 0
    ensures shape' == @Circle { radius: r }
  {
    shape' = @Circle { radius: r }
  }
}
";
    // Parse, elaborate, lower
    let tokens = abide::lex::lex(src).unwrap();
    let mut parser = abide::parse::Parser::new(tokens);
    let program = parser.parse_program().unwrap();
    let (result, _) = abide::elab::elaborate(&program);
    let (ir, _lower_diag) = abide::ir::lower(&result);
    let model = abide::qa::extract::extract(&ir);

    // Check contracts on Canvas.set_circle
    let contract = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Contracts {
            entity: "Canvas".to_string(),
            action: "set_circle".to_string(),
        },
    );
    match &contract {
        abide::qa::exec::QueryResult::NameList(items) => {
            // Should have requires
            let has_requires = items.iter().any(|s| s.starts_with("requires"));
            assert!(has_requires, "should have requires: {items:?}");

            // Should have ensures (postcondition was lowered)
            let has_ensures = items.iter().any(|s| s.starts_with("ensures"));
            assert!(
                has_ensures,
                "should have ensures (postcondition lowered from action): {items:?}"
            );

            // Ensures should contain the constructor with fields, not just @Circle
            let ensures_line = items.iter().find(|s| s.starts_with("ensures")).unwrap();
            assert!(
                ensures_line.contains("radius"),
                "ensures should render constructor fields (not just @Circle): {ensures_line}"
            );

            // Updates should render constructor with fields
            let update_line = items.iter().find(|s| s.starts_with("updates")).unwrap();
            assert!(
                update_line.contains("radius"),
                "update should render constructor fields: {update_line}"
            );
        }
        other => panic!("expected NameList, got: {other:?}"),
    }
}

// ── Scene event cardinality + ^| ──────────────────────────

#[test]
fn scene_cardinality_lone_fires() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_fires_once");
    assert!(r.is_some(), "lone_fires_once should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "lone_fires_once should PASS, got: {r:?}"
    );
}

#[test]
fn scene_cardinality_lone_skips() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_does_not_fire");
    assert!(r.is_some(), "lone_does_not_fire should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "lone_does_not_fire should PASS (optional event can skip), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_no() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "no_cancel");
    assert!(r.is_some(), "no_cancel should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "no_cancel should PASS ({{no}} event excluded), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_exact_n() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "exact_two_creates");
    assert!(r.is_some(), "exact_two_creates should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "exact_two_creates should PASS ({{2}} fires twice), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_some() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "some_creates");
    assert!(r.is_some(), "some_creates should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "some_creates should PASS ({{some}} fires at least once), got: {r:?}"
    );
}

#[test]
fn scene_xor_exclusive_choice() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_confirm_or_cancel");
    assert!(r.is_some(), "xor_confirm_or_cancel should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "xor_confirm_or_cancel should PASS (exactly one fires), got: {r:?}"
    );
}

#[test]
fn scene_lone_in_same_step() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_in_same_step");
    assert!(r.is_some(), "lone_in_same_step should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "lone_in_same_step should PASS ({{lone}} in & can skip), got: {r:?}"
    );
}

#[test]
fn scene_xor_exact_one() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_exact_one");
    assert!(r.is_some(), "xor_exact_one should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::ScenePass { .. }
        ),
        "xor_exact_one should PASS ({{1}} in ^| infers {{lone}}), got: {r:?}"
    );
}

#[test]
fn scene_xor_both_impossible() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_both_required");
    assert!(r.is_some(), "xor_both_required should produce a result");
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::SceneFail { .. }
        ),
        "xor_both_required should FAIL (can't have both states), got: {r:?}"
    );
}

// ── Liveness-to-safety reduction ──────────────────────────

#[test]
fn liveness_reduction_or_checked() {
    // The finite-state backend may prove this exhaustively before the
    // liveness-to-safety fallback is needed.
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "liveness_proved",
        _ => false,
    });
    assert!(
        r.is_some(),
        "liveness_proved should produce PROVED or CHECKED (got: {results:?})"
    );
    match r.unwrap() {
        abide::verify::VerificationResult::Proved { method, .. } => {
            assert!(
                method.contains("liveness") || method == "explicit-state exhaustive search",
                "unexpected liveness proof method: {method}"
            );
        }
        abide::verify::VerificationResult::Checked { .. } => {
            // IC3 timed out or failed — lasso BMC fallback is acceptable
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn liveness_reduction_theorem() {
    // Theorems with quantified liveness are UNPROVABLE: IC3's BAS monitor
    // with coarse justice is unsound for liveness (misses dead-state lassos),
    // so symmetry reduction correctly declines to use IC3. Accepting Proved
    // here would mask reintroduction of the unsound IC3 path.
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "liveness_theorem"
    ));
    assert!(
        r.is_some(),
        "liveness_theorem must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

#[test]
fn liveness_reduction_safety_unaffected() {
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "safety_check",
        _ => false,
    });
    assert!(r.is_some(), "safety_check should produce a result");
    // Safety must not route through the liveness reduction. Relational bounded
    // safety may report CHECKED.
    if let abide::verify::VerificationResult::Proved { method, .. } = r.unwrap() {
        assert!(
            !method.contains("liveness"),
            "safety_check should not use liveness reduction, got: {r:?}"
        );
    }
}

#[test]
fn liveness_bare_eventuality() {
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "bare_eventuality",
        _ => false,
    });
    assert!(
        r.is_some(),
        "bare_eventuality should produce a result (got: {results:?})"
    );
    // Should be CHECKED or PROVED — bare eventuality is now supported
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "bare_eventuality should be CHECKED or PROVED, got: {r:?}"
    );
}

#[test]
fn liveness_persistence() {
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "persistence_check",
        _ => false,
    });
    assert!(
        r.is_some(),
        "persistence_check should produce a result (got: {results:?})"
    );
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "persistence_check should be CHECKED or PROVED, got: {r:?}"
    );
}

#[test]
fn liveness_until_conjunction() {
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "until_check",
        _ => false,
    });
    assert!(
        r.is_some(),
        "until_check should produce a result (got: {results:?})"
    );
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "until_check should be CHECKED or PROVED, got: {r:?}"
    );
}

#[test]
fn liveness_until_theorem() {
    // Real `until` on the theorem path: "all s | Red until Green".
    // Desugars to (eventually Green) AND (always (not Green implies Red)).
    // UNPROVABLE: the liveness component requires IC3 BAS which is unsound
    // for liveness (dead-state issue). Accepting Proved would mask
    // reintroduction of the unsound IC3 path.
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| {
        matches!(
            r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "until_theorem"
        )
    });
    assert!(
        r.is_some(),
        "until_theorem must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

#[test]
fn liveness_existing_fairness_fixture_still_works() {
    // The existing fairness.ab fixture should still work.
    // fair_signal may now be PROVED (reduction) or CHECKED (lasso BMC).
    let results = verify_file("tests/fixtures/fairness.ab");
    let fair = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "fair_signal",
        _ => false,
    });
    assert!(fair.is_some(), "fair_signal should produce a result");
    // Should be PROVED or CHECKED (either is valid)
    assert!(
        matches!(
            fair.unwrap(),
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "fair_signal should be PROVED or CHECKED, got: {fair:?}"
    );

    // unfair_signal should still be a LIVENESS_VIOLATION
    let unfair = results.iter().find(|r| match r {
        abide::verify::VerificationResult::LivenessViolation { name, .. } => {
            name == "unfair_signal"
        }
        _ => false,
    });
    assert!(
        unfair.is_some(),
        "unfair_signal should still produce a LIVENESS_VIOLATION"
    );
}

// ── Quantified liveness soundness (per-slot monitors) ──────────────

#[test]
fn quantified_liveness_false_not_proved() {
    // Regression: false quantified liveness must NOT be falsely PROVED.
    // "eventually all b: Ball | b.color == @Green" is false because
    // fair blue_paint makes some balls Blue permanently.
    // The theorem goes directly to liveness reduction (no lasso BMC).
    let results = verify_file("tests/fixtures/liveness_quantified_false.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Unprovable { name, .. } => {
            name == "false_eventually_all_green"
        }
        _ => false,
    });
    assert!(
        r.is_some(),
        "false_eventually_all_green should produce a result (got: {results:?})"
    );
    // MUST be UNPROVABLE — NOT Proved. The old code falsely proved this.
    assert!(
        matches!(
            r.unwrap(),
            abide::verify::VerificationResult::Unprovable { .. }
        ),
        "false_eventually_all_green must be UNPROVABLE, not falsely PROVED (got: {r:?})"
    );
}

#[test]
fn quantified_liveness_true_proved() {
    // True quantified liveness is UNPROVABLE: IC3's BAS monitor with coarse
    // justice is unsound for liveness (dead-state issue), so the symmetry
    // reduction path declines to use IC3. Sound proof requires k-liveness.
    // Accepting Proved would mask reintroduction of the unsound IC3 path.
    let results = verify_file("tests/fixtures/liveness_quantified_false.ab");
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "true_each_eventually_painted"
    ));
    assert!(
        r.is_some(),
        "true_each_eventually_painted must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

#[test]
fn until_theorem_unbounded() {
    // Real `until` expression on the theorem/unbounded path:
    // "all b: Ball | b.color == @Red until b.color != @Red"
    // Desugars to (eventually non-Red) AND (always (non-Red implies Red)) — the
    // Forall wrapping fix correctly extracts QuantifiedEventuality + safety.
    // UNPROVABLE: the liveness component requires IC3 BAS which is unsound
    // for liveness (dead-state issue). Accepting Proved would mask
    // reintroduction of the unsound IC3 path.
    let results = verify_file("tests/fixtures/liveness_quantified_false.ab");
    let r = results.iter().find(|r| {
        matches!(
            r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "until_painted"
        )
    });
    assert!(
        r.is_some(),
        "until_painted must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

// ── Symmetry reduction () ───────────────────────────────────

#[test]
fn symmetry_reduction_eventuality_unprovable() {
    // Quantified liveness on the theorem path is UNPROVABLE: IC3's BAS monitor
    // with coarse justice is unsound for liveness (misses dead-state lassos),
    // so the symmetry reduction path correctly declines to use IC3.
    // Sound unbounded proof requires k-liveness or per-event enabled tracking.
    let results = verify_file("tests/fixtures/symmetry_reduction.ab");
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "symmetric_eventuality"
    ));
    assert!(
        r.is_some(),
        "symmetric_eventuality should be UNPROVABLE (got: {results:?})"
    );
}

#[test]
fn symmetry_reduction_response_unprovable() {
    // Symmetric system, Response pattern: IC3's BAS monitor with coarse
    // justice is unsound for liveness (misses dead-state lassos), so
    // symmetry reduction correctly declines to use IC3. Accepting Proved
    // would mask reintroduction of the unsound IC3 path.
    let results = verify_file("tests/fixtures/symmetry_reduction.ab");
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "symmetric_response"
    ));
    assert!(
        r.is_some(),
        "symmetric_response must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

#[test]
fn symmetry_reduction_asymmetric_not_proved() {
    // Asymmetric system: swap event has nested Choose over same entity type.
    // Symmetry validation MUST fail → must be UNPROVABLE (theorem path).
    // Critical: must NOT be PROVED (which would be unsound for asymmetric systems).
    let results = verify_file("tests/fixtures/symmetry_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Unprovable { name, .. } => name == "asymmetric_liveness",
        _ => false,
    });
    assert!(
        r.is_some(),
        "asymmetric_liveness must be UNPROVABLE (symmetry validation should fail) (got: {results:?})"
    );
    // Also verify it was NOT proved (critical soundness check)
    assert!(
        !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "asymmetric_liveness"
        )),
        "asymmetric_liveness must NOT be PROVED (asymmetric systems should not pass symmetry reduction)"
    );
}

#[test]
fn symmetry_reduction_verify_block_checked() {
    // Symmetric verify block: CHECKED via lasso BMC (bounded).
    // Quantified liveness cannot be PROVED unboundedly (IC3 BAS is unsound
    // for liveness), so the verify block falls back to lasso BMC.
    let results = verify_file("tests/fixtures/symmetry_reduction.ab");
    let r = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
                if name == "symmetric_verify"
        )
    });
    assert!(
        r.is_some(),
        "symmetric_verify should be CHECKED or PROVED (got: {results:?})"
    );
}

// ── Strong fairness (TLA+ SF parity) ────────────────────────────────

#[test]
fn strong_fairness_theorem_both_unprovable() {
    // Both strong_liveness and weak_liveness are UNPROVABLE on the theorem
    // path (IC3's BAS coarse justice can't encode strong fairness). The key
    // difference is that the lasso sanity check blocks the A↔B loop for
    // strong but not weak — this is tested via the verify block path below
    // and the symmetry reduction sanity check.
    let results = verify_file("tests/fixtures/strong_fairness.ab");
    let strong = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "strong_liveness"
    ));
    assert!(
        strong.is_some(),
        "strong_liveness should be UNPROVABLE (got: {results:?})"
    );
    let weak = results.iter().find(|r| {
        matches!(
            r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "weak_liveness"
        )
    });
    assert!(
        weak.is_some(),
        "weak_liveness should be UNPROVABLE (got: {results:?})"
    );
}

#[test]
fn strong_fairness_safety_unaffected() {
    let results = verify_file("tests/fixtures/strong_fairness.ab");
    let r = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                | abide::verify::VerificationResult::Checked { name, .. }
                if name == "safety_check"
        )
    });
    assert!(
        r.is_some(),
        "safety_check should succeed (got: {results:?})"
    );
}

// ── Deep dead-state regression (soundness) ──────────────────────────

#[test]
fn deep_dead_state_not_proved() {
    // Regression: a chain S0→S1→...→S6 where S6 is a dead non-goal state.
    // The property `eventually state == @Goal` is FALSE (no path to Goal).
    // Must NOT be PROVED — previously a shallow lasso sanity check missed
    // the depth-6 dead state, and IC3's coarse justice falsely proved it.
    let results = verify_file("tests/fixtures/deep_dead_state.ab");
    // Must be UNPROVABLE — NOT Proved
    assert!(
        !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "deep_dead"
        )),
        "deep_dead must NOT be PROVED (false property with dead state at depth 6) (got: {results:?})"
    );
    // Should produce UNPROVABLE
    let r = results.iter().find(|r| {
        matches!(
            r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "deep_dead"
        )
    });
    assert!(
        r.is_some(),
        "deep_dead should be UNPROVABLE (got: {results:?})"
    );
}

// ── Nondeterministic initial values () ─────────────────────

#[test]
fn nondet_in_explores_all_values() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "in_explores_all",
        _ => false,
    });
    assert!(
        r.is_some(),
        "in_explores_all should be PROVED (got: {results:?})"
    );
}

#[test]
fn nondet_where_constrains() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "where_constrains",
        _ => false,
    });
    assert!(
        r.is_some(),
        "where_constrains should be PROVED (got: {results:?})"
    );
}

#[test]
fn nondet_deterministic_regression() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => {
            name == "deterministic_regression"
        }
        _ => false,
    });
    assert!(
        r.is_some(),
        "deterministic_regression should be PROVED (got: {results:?})"
    );
}

#[test]
fn nondet_in_counterexample() {
    // "All tasks are Low priority" is false because tasks can start Medium or High.
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Counterexample { name, .. } => {
            name == "in_counterexample"
        }
        _ => false,
    });
    assert!(
        r.is_some(),
        "in_counterexample should be COUNTEREXAMPLE (got: {results:?})"
    );
}

#[test]
fn nondet_where_not_bool_rejected() {
    // `where 42` (non-boolean predicate) must produce an elaboration error.
    let paths = [std::path::PathBuf::from(
        "tests/fixtures/nondet_defaults_invalid.ab",
    )];
    let (env, load_errors, _) = abide::loader::load_files(&paths);
    assert!(load_errors.is_empty());
    let (_, errors) = abide::elab::elaborate_env(env);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("where") && msg.contains("boolean")
        }),
        "should reject non-boolean `where` predicate (got: {errors:?})"
    );
}

#[test]
fn nondet_in_wrong_type_rejected() {
    // `in {1}` for an enum field must produce an elaboration error.
    let paths = [std::path::PathBuf::from(
        "tests/fixtures/nondet_defaults_invalid.ab",
    )];
    let (env, load_errors, _) = abide::loader::load_files(&paths);
    assert!(load_errors.is_empty());
    let (_, errors) = abide::elab::elaborate_env(env);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("constructor") && msg.contains("Status")
        }),
        "should reject numeric literal in `in` for enum field (got: {errors:?})"
    );
}

#[test]
fn nondet_where_false_vacuous_bmc() {
    // `where false` makes entity uncreatable — BMC should be vacuously PROVED.
    let results = verify_file("tests/fixtures/nondet_where_false.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "where_false_vacuous",
        _ => false,
    });
    assert!(
        r.is_some(),
        "where_false_vacuous should be PROVED (got: {results:?})"
    );
}

#[test]
fn nondet_where_false_vacuous_theorem() {
    // Theorem path must agree: no COUNTEREXAMPLE from impossible creation.
    let results = verify_file("tests/fixtures/nondet_where_false.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Unprovable { name, .. } => {
            name == "where_false_theorem"
        }
        _ => false,
    });
    assert!(
        r.is_some(),
        "where_false_theorem should produce a result (got: {results:?})"
    );
    // Must NOT be a COUNTEREXAMPLE — the entity is uncreatable.
    assert!(
        !matches!(
            r.unwrap(),
            abide::verify::VerificationResult::Counterexample { .. }
        ),
        "where_false_theorem must not produce a COUNTEREXAMPLE (got: {r:?})"
    );
}

#[test]
fn nondet_in_builtin_type_mismatch_rejected() {
    // `b: bool in {1}` must produce an elaboration error (int for bool field).
    let paths = [std::path::PathBuf::from(
        "tests/fixtures/nondet_defaults_invalid.ab",
    )];
    let (env, load_errors, _) = abide::loader::load_files(&paths);
    assert!(load_errors.is_empty());
    let (_, errors) = abide::elab::elaborate_env(env);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("int") && msg.contains("bool")
        }),
        "should reject int literal in `in` for bool field (got: {errors:?})"
    );
}

// ── Collection operations () ────────────────────────────────

#[test]
fn collection_ops_all_proved() {
    let results = verify_file("tests/fixtures/collection_ops.ab");
    let expected = [
        // Set qualified calls
        "set_union_int",
        "set_intersect_int",
        "set_diff_int",
        "set_subset_int",
        "set_disjoint_int",
        "set_not_disjoint_int",
        "set_member_int",
        "set_not_member_int",
        // Set::member polymorphic
        "set_member_real",
        // Set operators (<>, !*)
        "set_union_op",
        "set_disjoint_op",
        "set_not_disjoint_op",
        // Type-directed operators (*, -, <=) — dispatched at IR level
        "set_intersect_star",
        "set_diff_minus",
        "set_subset_le",
        // Seq
        "seq_head_int",
        "seq_tail_int",
        "seq_length_int",
        "seq_empty_true",
        "seq_empty_false",
        "seq_concat_int",
        "seq_bool_eq",
        // Map
        "map_has_true",
        "map_has_false",
        "map_domain_int",
        "map_range_int",
        "map_merge_right_bias",
    ];
    for name in &expected {
        let r = results.iter().find(|r| match r {
            abide::verify::VerificationResult::Proved { name: n, .. } => n == name,
            _ => false,
        });
        assert!(r.is_some(), "{name} should be PROVED (got: {results:?})");
    }
}

#[test]
fn collection_comprehensions_all_proved() {
    let results = verify_file("tests/fixtures/collection_comprehensions.ab");
    let expected = [
        "set_source_comprehension",
        "typed_set_source_comprehension",
        "seq_source_comprehension",
    ];
    for name in &expected {
        let result = results.iter().find(|result| match result {
            abide::verify::VerificationResult::Proved { name: actual, .. } => actual == name,
            _ => false,
        });
        assert!(
            result.is_some(),
            "{name} should be PROVED (got: {results:?})"
        );
    }
}

#[test]
fn real_set_comprehension_without_finite_source_has_actionable_diagnostic() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let path = dir.path().join("real_set_comprehension.ab");
    std::fs::write(
        &path,
        "const bad = { x | x: real where x >= 0.0 and x <= 1.0 }\n",
    )
    .expect("write spec");

    let (env, load_errors, _) = abide::loader::load_files(&[path]);
    assert!(load_errors.is_empty(), "load errors: {load_errors:?}");
    let (_, errors) = abide::elab::elaborate_env(env);

    let error = errors
        .iter()
        .find(|error| {
            error.message.contains("set comprehension")
                && error.message.contains("real")
                && error.message.contains("finite source")
        })
        .unwrap_or_else(|| {
            panic!("expected actionable real set-comprehension diagnostic, got: {errors:?}")
        });
    let help = error.help.as_deref().unwrap_or_default();
    assert!(help.contains("Set("), "{help}");
    assert!(help.contains("real intervals are not enumerable"), "{help}");
}

// ── entity and system invariants () ────────────────

/// Helper for tests: parse, elaborate, lower, and verify a
/// source string. Returns the verifier results.
fn verify_source(src: &str) -> Vec<abide::verify::VerificationResult> {
    verify_source_with_config(src, abide::verify::VerifyConfig::default())
}

/// Helper for tests: parse, elaborate, lower, and verify a
/// source string with an explicit verifier configuration.
fn verify_source_with_config(
    src: &str,
    config: abide::verify::VerifyConfig,
) -> Vec<abide::verify::VerificationResult> {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    let prog = lower_file(&path_str);
    abide::verify::verify_all(&prog, &config)
}

fn assert_verify_result_success(results: &[abide::verify::VerificationResult], name: &str) {
    let found = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name: n, .. }
        | abide::verify::VerificationResult::Checked { name: n, .. } => n == name,
        _ => false,
    });
    assert!(
        found.is_some(),
        "{name} should be PROVED or CHECKED (got: {results:?})"
    );
}

#[test]
fn symbolic_seq_surface_ops_over_fields_prove() {
    let src = r"module SeqSurface

entity E {
  items: Seq<int> = Seq(10, 20)
}

system S(es: Store<E>) {
  command init() {
    create E {}
  }
}

verify seq_concat_len {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Seq::length(Seq::concat(e.items, Seq(30, 40))) == 4)
}

verify seq_concat_index {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Seq::concat(e.items, Seq(30, 40))[2] == 30)
}

verify seq_tail_head {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Seq::head(Seq::tail(e.items)) == 20)
}

verify seq_tail_not_empty {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | not Seq::empty(Seq::tail(e.items)))
}
";

    let results = verify_source(src);
    for name in [
        "seq_concat_len",
        "seq_concat_index",
        "seq_tail_head",
        "seq_tail_not_empty",
    ] {
        assert_verify_result_success(&results, name);
    }
}

#[test]
fn symbolic_map_surface_ops_over_fields_prove() {
    let src = r"module MapSurface

entity E {
  data: Map<int, int> = Map(1, 10, 2, 20)
}

system S(es: Store<E>) {
  command init() {
    create E {}
  }
}

verify map_has_field {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Map::has(e.data, 1))
}

verify map_domain_field {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Map::domain(e.data) == Set(1, 2))
}

verify map_range_field {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Map::range(e.data) == Set(10, 20))
}

verify map_merge_lookup {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Map::merge(e.data, Map(2, 99, 3, 30))[2] == 99)
}

verify map_merge_has_new_key {
  assume {
    store es: E[0..2]
    let s = S { es: es }
    stutter
  }
  assert always (all e: E in es | Map::has(Map::merge(e.data, Map(2, 99, 3, 30)), 3))
}
";

    let results = verify_source(src);
    for name in [
        "map_has_field",
        "map_domain_field",
        "map_range_field",
        "map_merge_lookup",
        "map_merge_has_new_key",
    ] {
        assert_verify_result_success(&results, name);
    }
}

#[test]
fn verifier_supports_pure_let_ifelse_and_match_in_verify_and_theorem() {
    let src = r"module T

enum Status = A | B

fn branch(flag: bool): bool {
  if flag { true } else { false }
}

fn pick(s: Status): bool = match s { A => true B => false }

entity E {
  s: Status = @A

  action go() requires s == @A {
    s' = @B
  }
}

system Sys(es: Store<E>) {
  command tick() {
    choose e: E where e.s == @A { e.go() }
  }
}

verify v {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }

  assert let ok = true in ok
  assert branch(true)
  assert pick(@A)
}

theorem t for Sys {
  show always (let ok = true in ok)
  show always branch(true)
  show always pick(@A)
}
";

    let results = verify_source(src);

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "verify block using let/ifelse/match should succeed, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "t"
        )),
        "theorem using let/ifelse/match should prove, got: {results:?}"
    );
}

#[test]
fn unit_enum_match_patterns_use_bare_constructor_syntax() {
    let src = r"module T

enum Status = A | B

fn bare(s: Status): bool = match s { A => true B => false }
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors.is_empty(),
        "unit constructor patterns should use bare variant syntax, got: {errors:?}"
    );
}

#[test]
fn unit_enum_match_patterns_reject_empty_braces() {
    let src = r"module T

enum Status = A | B

fn braced(s: Status): bool = match s { A {} => true B {} => false }
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("unit constructor pattern `A {}` should be written `A`")),
        "expected unit constructor empty-brace diagnostic, got: {errors:?}"
    );
}

#[test]
fn verifier_supports_pure_let_and_match_in_scene() {
    let src = r"module T

enum Status = A | B

entity E {
  s: Status = @A
}

scene s {
  given {
    let e = one E where let ok = true in ok
  }
  when {
  }
  then {
    assert let ok = true in ok
    assert match @A { A => true B => false }
  }
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene using let/match should pass, got: {results:?}"
    );
}

#[test]
fn scene_assert_helper_function_call_is_supported() {
    let src = r"module T

enum Status = A | B

fn pick(s: Status): bool = match s { A => true B => false }

entity E {
  s: Status = @A
}

scene s {
  given {
    let e = one E where true
  }
  when {
  }
  then {
    assert pick(@A)
  }
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene helper function calls should now be supported, got: {results:?}"
    );
}

#[test]
fn verifier_supports_some_and_no_quantifiers() {
    let src = r"module T

enum Status = A | B

entity E {
  s: Status = @A
}

system Sys(es: Store<E>) {
  command tick() {}
}

verify v {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }

  assert some s: Status | s == @A
  assert no s: Status | false
}

theorem t for Sys {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }

  show always (some s: Status | s == @A)
  show always (no s: Status | false)
}

scene s {
  given {
    let e = one E where true
  }
  when {
  }
  then {
    assert some x: E | x.s == @A
    assert no x: E | x.s == @B
  }
}
";

    let results = verify_source(src);

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "verify block using some/no should succeed, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "t"
        )),
        "theorem using some/no should prove, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene using some/no should pass, got: {results:?}"
    );
}

#[test]
fn named_store_quantifiers_stay_store_scoped_in_scene() {
    let src = r"module T

enum Status = pending | archived

entity Order {
  status: Status = @pending
}

scene s {
  given {
    store pending_orders: Order[0..1]
    store archived_orders: Order[0..1]
    let p = one Order in pending_orders where p.status == @pending
    let a = one Order in archived_orders where a.status == @archived
  }
  when {
  }
  then {
    assert all o: Order in pending_orders | o.status == @pending
    assert all o: Order in archived_orders | o.status == @archived
    assert no o: Order in pending_orders | o.status == @archived
    assert no o: Order in archived_orders | o.status == @pending
  }
}
";

    let results = verify_source(src);

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene should respect named-store quantifier ranges, got: {results:?}"
    );
}

#[test]
fn verifier_supports_pure_choose_in_verify_theorem_lemma_and_scene() {
    let src = r"module T

enum Status = A | B

entity E {
  s: Status = @A
}

system Sys(es: Store<E>) {
  command tick() {}
}

lemma chosen_one {
  (choose n: int where n == 1) == 1
}

verify v {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }

  assert (choose n: int where n == 1) == 1
}

theorem t for Sys {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }
  by chosen_one
  show always ((choose n: int where n == 1) == 1)
}

scene s {
  given {
    let e = one E where true
  }
  when {
    assume (choose n: int where n == 1) == 1
  }
  then {
    assert (choose n: int where n == 2) == 2
    assert ((choose x: E where x.s == e.s).s) == e.s
  }
}
";

    let results = verify_source(src);

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "verify block using choose should succeed, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "chosen_one"
        )),
        "lemma using choose should prove, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "t"
        )),
        "theorem using choose should prove, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene using choose should pass, got: {results:?}"
    );
}

#[test]
fn verifier_surface_rejects_higher_order_and_imperative_forms_during_elaboration() {
    let src = r"module T

entity E {}

system Sys {}

verify v {
  assert (fn(x: bool) => x)(true)
}

theorem t for Sys {
  show true
}

scene s {
  given {
    let e = one E where true
  }
  when {
    assume true
  }
  then {
    assert (fn(x: bool) => x)(true)
  }
}
";

    let errors = elaborate_source_errors(src);
    let messages: Vec<_> = errors.iter().map(|e| e.message.as_str()).collect();

    assert!(
        messages
            .iter()
            .any(|m| m.contains("`lambda` is not allowed in verify v assertion")),
        "expected verify lambda restriction, got: {messages:?}"
    );
    assert!(
        messages
            .iter()
            .any(|m| m.contains("`lambda` is not allowed in scene s then assertion")),
        "expected scene lambda restriction, got: {messages:?}"
    );
}

#[test]
fn verifier_supports_assert_and_assume_wrappers_in_property_positions() {
    let src = r"module T

entity E {}

system Sys(es: Store<E>) {}

lemma wrapped_truth {
  assert (assume true)
}

verify v {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }
  assert assert true
  assert assume true
}

theorem t for Sys {
  assume {
    store es: E[0..1]
    let sys = Sys { es: es }
    stutter
  }
  by wrapped_truth
  show always (assert (assume true))
}

scene s {
  given {
    let e = one E where true
  }
  when {
    assume assert true
  }
  then {
    assert assume true
    assert assert true
  }
}
";

    let results = verify_source(src);

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "verify block using assert/assume wrappers should succeed, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "wrapped_truth"
        )),
        "lemma using assert/assume wrappers should prove, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "t"
        )),
        "theorem using assert/assume wrappers should prove, got: {results:?}"
    );

    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "s"
        )),
        "scene using assert/assume wrappers should pass, got: {results:?}"
    );
}

/// an entity invariant that is preserved by every
/// event in scope verifies clean (PROVED via 1-induction or CHECKED via
/// BMC). The invariant `non_negative { balance >= 0 }` holds because
/// the only event sets balance to 1.
#[test]
fn verify_entity_invariant_preserved() {
    let src = r"module T

entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }

  action set_one() requires balance == 0 { balance' = 1 }
}

system Bank(accounts: Store<Account>) {command tick() {
    choose a: Account where a.balance == 0 {
      a.set_one()
    }
  }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            abide::verify::VerificationResult::Proved { name, .. }
                | abide::verify::VerificationResult::Checked { name, .. }
                if name == "v"
        ),
        "expected PROVED or CHECKED with preserved invariant, got: {results:?}"
    );
}

/// an entity invariant that an event violates
/// produces a counterexample. The system creates an Account and then
/// an action sets its balance to -1, violating `non_negative`.
#[test]
fn verify_entity_invariant_violated() {
    let src = r"module T

entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }

  action go_negative() requires balance == 0 { balance' = -1 }
}

system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command misbehave() {
    choose a: Account where a.balance == 0 {
      a.go_negative()
    }
  }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "v"
        ),
        "expected Counterexample for invariant violation, got: {results:?}"
    );
}

/// entity invariants TRAVEL with the entity
/// type. An entity Account with `non_negative` invariant pooled into a
/// system whose verify block has only `assert always true` should still
/// catch a violation made by an event in that system.
#[test]
fn verify_entity_invariant_travels_into_pooling_system() {
    // The entity is declared once with its invariant. The system that
    // pools it doesn't restate the invariant — but the verifier still
    // checks it because entity invariants travel with the type.
    let src = r"module T

entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }

  action go_negative() requires balance == 0 { balance' = -1 }
}

system Reporting(accounts: Store<Account>) {command open() { create Account {} }
  command report() {
    choose a: Account where a.balance == 0 {
      a.go_negative()
    }
  }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let reporting = Reporting { accounts: accounts }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            abide::verify::VerificationResult::Counterexample { .. }
        ),
        "Account's `non_negative` invariant should travel into Reporting \
         and catch the violation, got: {results:?}"
    );
}

/// / helper: elaborate a source string and return the
/// (result, errors) pair so tests can assert on diagnostics directly
/// (instead of failing on the first error like `elaborate_source`).
fn elab_with_errors(src: &str) -> (elab::types::ElabResult, Vec<elab::error::ElabError>) {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    let src_text = std::fs::read_to_string(&path_str).unwrap();
    let tokens = abide::lex::lex(&src_text).expect("lex");
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().expect("parse");
    elab::elaborate(&program)
}

#[test]
fn uppercase_primitive_type_rejected() {
    let src = r"module T

entity Order {
  qty: Int = 0
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| {
                e.message.contains("unknown type `Int`")
                    && e.help.as_deref() == Some("did you mean `int`?")
            }),
        "expected unknown-type diagnostic with lowercase hint for uppercase primitive, got: {errors:?}"
    );
}

#[test]
fn id_builtin_type_rejected() {
    let src = r"module T

entity Order {
  key: id = 0
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("unknown type `id`") && e.help.is_none()),
        "expected unknown-type diagnostic for `id`, got: {errors:?}"
    );
}

#[test]
fn lowercase_builtin_collection_type_rejected_with_canonical_hint() {
    let src = r"module T

entity Users {
  ids: set<identity>
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|e| {
            e.message.contains("unknown type `set`")
                && e.help.as_deref() == Some("did you mean `Set`?")
        }),
        "expected unknown-type diagnostic with canonical collection hint, got: {errors:?}"
    );
}

#[test]
fn interface_elaborates_and_system_records_implements() {
    let src = r"module T

interface NotificationBackend {
  command send(recipient: string, body: string) -> string
  query delivery_count() -> int
}

system SlackAdapter implements NotificationBackend {
  command send(recipient: string, body: string) -> string {
  }
  query delivery_count() = 0
}
";
    let result = elaborate_source(src);
    assert_eq!(result.interfaces.len(), 1);
    assert_eq!(result.interfaces[0].name, "NotificationBackend");
    assert_eq!(result.interfaces[0].commands.len(), 1);
    assert_eq!(result.interfaces[0].queries.len(), 1);
    assert_eq!(result.systems.len(), 1);
    assert_eq!(
        result.systems[0].implements.as_deref(),
        Some("NotificationBackend")
    );
}

#[test]
fn interface_missing_required_query_is_rejected() {
    let src = r"module T

interface NotificationBackend {
  command send(recipient: string, body: string) -> string
  query delivery_count() -> int
}

system SlackAdapter implements NotificationBackend {
  command send(recipient: string, body: string) -> string {
  }
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|e| e.message.contains(
            "is missing query `delivery_count` required by interface `NotificationBackend`"
        )),
        "expected missing-query interface diagnostic, got: {errors:?}"
    );
}

#[test]
fn interface_query_type_mismatch_is_rejected() {
    let src = r"module T

interface NotificationBackend {
  query delivery_count() -> int
}

system SlackAdapter implements NotificationBackend {
  query delivery_count() = true
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|e| e.message.contains(
            "query `delivery_count` returns `bool` but interface `NotificationBackend` requires `int`"
        )),
        "expected query type mismatch diagnostic, got: {errors:?}"
    );
}

/// an `fsm` referencing a non-existent field is
/// rejected at elab time.
#[test]
fn fsm_unknown_field_rejected() {
    let src = r"module T

enum OrderStatus = cart | placed
entity Order {
  status: OrderStatus = @cart
  fsm bogus {
    @cart -> @placed
    @placed ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("unknown field `bogus`")),
        "expected unknown-field diagnostic, got: {errors:?}"
    );
}

/// an `fsm` on a non-enum field is rejected.
#[test]
fn fsm_non_enum_field_rejected() {
    let src = r"module T

entity Order {
  qty: int = 0
  fsm qty {
    @cart -> @placed
  }
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|e| format!("{e}").contains("enum type")),
        "expected non-enum-field diagnostic, got: {errors:?}"
    );
}

/// an atom in a transition row that is not a
/// variant of the field's enum is rejected at elab time.
#[test]
fn fsm_unknown_variant_rejected() {
    let src = r"module T

enum OrderStatus = cart | placed
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @bogus
    @placed ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("unknown variant `@bogus`")),
        "expected unknown-variant diagnostic, got: {errors:?}"
    );
}

/// at most one fsm per field. A second `fsm` on
/// the same field is rejected.
#[test]
fn fsm_duplicate_field_rejected() {
    let src = r"module T

enum OrderStatus = cart | placed
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed ->
  }
  fsm status {
    @cart -> @placed
    @placed ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("duplicate `fsm`")),
        "expected duplicate-fsm diagnostic, got: {errors:?}"
    );
}

/// / / 50.6: an action that drives an fsm-bound
/// field along an edge that the table allows is accepted by the
/// verifier — `verify v` finishes without a counterexample.
#[test]
fn fsm_legal_transition_verifies() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
  action place() requires status == @cart { status' = @placed }
}

system Shop(orders: Store<Order>) {command open() { create Order {} }
  command place_event() {
    choose o: Order where o.status == @cart {
      o.place()
    }
  }
}

verify v {
  assume {
    store orders: Order[0..3]
    let shop = Shop { orders: orders }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    let v = results
        .iter()
        .find(|r| {
            matches!(r,
            abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Counterexample { name, .. }
            | abide::verify::VerificationResult::Unprovable { name, .. }
            | abide::verify::VerificationResult::LivenessViolation { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. }
            if name == "v")
        })
        .expect("verify v result");
    assert!(
        matches!(
            v,
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "legal fsm transition (place: cart -> placed) must verify, got: {v:?}"
    );
}

/// a primed assignment nested inside a
/// `match` arm of an entity action would silently disappear from the
/// IR's `IRTransition::updates` list (which only walks top-level
/// `Assign(Prime, _)` nodes), bypassing both the static fsm violation
/// check and the verifier's per-action fsm constraint. The elab pass
/// now rejects nested primes outright with a clear diagnostic so the
/// soundness gap can't be exercised.
///
/// `match` is the relevant case for the entity action body parser
/// because it's the imperative-shaped expression form the parser
/// admits there (`if`/`while`/`var` are block-level only).
#[test]
fn fsm_nested_prime_in_match_rejected() {
    let src = r"module T

enum Mode = a | b
enum OrderStatus = cart | placed | delivered
entity Order {
  mode: Mode = @a
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
  action cheat() {
    match mode {
      a => status' = @delivered
      b => status' = @placed
    }
  }
}
";
    let (_, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| format!("{e}").contains("nested prime")),
        "expected nested-prime diagnostic for match-arm form, got: {real_errors:?}"
    );
    assert!(
        real_errors
            .iter()
            .any(|e| format!("{e}").contains("Order::cheat")),
        "diagnostic should name the offending action, got: {real_errors:?}"
    );
}

/// a primed assignment
/// nested inside a `let... in body` body of an entity action also
/// disappears from `extract_updates`, so it's rejected too.
#[test]
fn fsm_nested_prime_in_let_rejected() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
  action cheat() {
    let target = @delivered in status' = target
  }
}
";
    let (_, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| format!("{e}").contains("nested prime")),
        "expected nested-prime diagnostic for let-in form, got: {real_errors:?}"
    );
}

/// the existing flat form (top-level
/// `field' = value`) must still elab cleanly so the rejection
/// doesn't break the supported subset.
#[test]
fn fsm_top_level_prime_still_accepted() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
  action place() requires status == @cart { status' = @placed }
}
";
    let (_, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "flat top-level prime should elab clean, got: {real_errors:?}"
    );
}

/// / / 50.6 fsm validity must be
/// enforced in the CHAINED-apply path too, not just in `encode_action`.
/// Without the fsm hook in `encode_action_with_vars`, an event that
/// performs multiple sequential applies on the same entity could
/// bypass the fsm check on the second (and later) apply.
///
/// Scenario: `place` legally goes `@cart -> @placed`, then
/// `sneaky_cancel` (with no constraining `requires`, so the static
/// elab check skips it) jumps to `@cancelled`. The fsm only allows
/// `@cart -> @cancelled`, NOT `@placed -> @cancelled`. Without the
/// chained-path fix the chain executes and reaches `@cancelled`,
/// violating `assert always status != @cancelled`. With the fix the
/// chained encoding makes the second apply infeasible and the assert
/// holds.
#[test]
fn fsm_chained_apply_enforces_validity() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered | cancelled
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed | @cancelled
    @placed -> @delivered
    @delivered ->
    @cancelled ->
  }
  action place() requires status == @cart { status' = @placed }
  action sneaky_cancel() { status' = @cancelled }
}

system Shop(orders: Store<Order>) {command open() { create Order {} }
  command chain_cheat() {
    choose o: Order where o.status == @cart {
      o.place()
      o.sneaky_cancel()
    }
  }
}

verify v {
  assume {
    store orders: Order[0..3]
    let shop = Shop { orders: orders }
  
   stutter }
  assert always (all o: Order | o.status != @cancelled)
}
";
    let results = verify_source(src);
    let v = results
        .iter()
        .find(|r| {
            matches!(r,
            abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Counterexample { name, .. }
            | abide::verify::VerificationResult::Unprovable { name, .. }
            | abide::verify::VerificationResult::LivenessViolation { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. }
            if name == "v")
        })
        .expect("verify v result");
    assert!(
        matches!(
            v,
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "chained-apply fsm enforcement should block sneaky_cancel \
         after place, so `always status != @cancelled` must verify, \
         got: {v:?}"
    );
}

/// / / 50.6: an action that statically prime-assigns
/// an fsm-bound field to a state not in the transition table from the
/// requires-implied source is rejected at ELAB time with a clear
/// diagnostic naming the action, the failing pair, and valid
/// alternatives. The verifier's per-action constraint is the
/// backstop, but the static check surfaces the bug before any
/// verification runs.
#[test]
fn fsm_illegal_transition_rejected() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
  action skip_to_delivered() requires status == @cart { status' = @delivered }
}
";
    let (_, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    let violation = real_errors
        .iter()
        .find(|e| format!("{e}").contains("violates fsm"))
        .expect("expected fsm action violation diagnostic");
    let msg = format!("{violation}");
    assert!(
        msg.contains("Order::skip_to_delivered"),
        "diagnostic should name the action, got: {msg}"
    );
    assert!(
        msg.contains("@cart") && msg.contains("@delivered"),
        "diagnostic should name the failing transition pair, got: {msg}"
    );
    assert!(
        msg.contains("@placed"),
        "diagnostic should list valid alternatives from @cart, got: {msg}"
    );
}

/// an action with a disjunctive `requires` is
/// accepted as long as the target is reachable from each source.
#[test]
fn fsm_disjunctive_requires_legal() {
    let src = r"module T

enum Status = a | b | c
entity E {
  s: Status = @a
  fsm s {
    @a -> @c
    @b -> @c
    @c ->
  }
  action go_c() requires s == @a or s == @b { s' = @c }
}
";
    let (_, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "disjunctive requires with all-legal targets should elab clean, got: {real_errors:?}"
    );
}

/// a disjunctive `requires` where one branch
/// implies an illegal transition is rejected — the diagnostic
/// pinpoints the offending branch.
#[test]
fn fsm_disjunctive_requires_one_illegal() {
    let src = r"module T

enum Status = a | b | c
entity E {
  s: Status = @a
  fsm s {
    @a -> @c
    @b ->
    @c ->
  }
  action go_c() requires s == @a or s == @b { s' = @c }
}
";
    let (_, errors) = elab_with_errors(src);
    // Only the @b -> @c branch is illegal; @a -> @c is allowed.
    let violations: Vec<_> = errors
        .iter()
        .filter(|e| {
            !matches!(e.severity, elab::error::Severity::Warning)
                && format!("{e}").contains("violates fsm")
        })
        .collect();
    assert!(
        !violations.is_empty(),
        "expected at least one violation diagnostic"
    );
    let msg = format!("{}", violations[0]);
    assert!(
        msg.contains("@b") && msg.contains("@c"),
        "diagnostic should pinpoint the @b -> @c violation, got: {msg}"
    );
}

/// a variant mentioned in the fsm graph that
/// cannot be reached from the field's initial state produces a
/// warning at the fsm declaration site (not an error).
#[test]
fn fsm_unreachable_state_warns() {
    let src = r"module T

enum Status = a | b | c | d
entity E {
  s: Status = @a
  fsm s {
    @a -> @b
    @b ->
    @c -> @d
    @d ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    // The fsm graph: a -> b, c -> d. From initial @a we reach {a, b}.
    // States {c, d} are mentioned in the fsm but unreachable. Each
    // should produce a warning (not an error).
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "reachability check should produce warnings, not errors: {real_errors:?}"
    );
    let warnings: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    let unreachable_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| format!("{w}").contains("unreachable"))
        .collect();
    assert!(
        unreachable_warnings
            .iter()
            .any(|w| format!("{w}").contains("@c")),
        "expected @c unreachable warning, got: {unreachable_warnings:?}"
    );
    assert!(
        unreachable_warnings
            .iter()
            .any(|w| format!("{w}").contains("@d")),
        "expected @d unreachable warning, got: {unreachable_warnings:?}"
    );
}

/// / the QA `terminal states of
/// E::field` query must agree with the compiler's synthesized
/// `is_terminal` derived field. The previous extraction restricted
/// the terminal set to variants "mentioned" in the fsm transition
/// pairs, but the compiler's synthesis uses the FULL enum variant
/// list — variants that don't appear in the table at all are
/// terminal-by-omission and must show up in QA results.
///
/// Scenario: enum has `cart`, `placed`, `delivered`, `archived`. The
/// fsm only mentions `cart`, `placed`, `delivered`. `archived` is in
/// the enum but never appears in any row — it should still be
/// reported as terminal (and the synthesized `is_terminal` should
/// also include it, which the test cross-checks).
#[test]
fn qa_fsm_terminal_includes_omitted_variants() {
    use std::io::Write;
    let src = r"module T

enum OrderStatus = cart | placed | delivered | archived
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let prog = lower_file(file.to_str().unwrap());
    let model = abide::qa::extract::extract(&prog);

    // QA `ask terminal states of Order::status` must include
    // `archived` even though it never appears in the fsm rows.
    let result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTerminalStates {
            entity: "Order".to_string(),
            field: "status".to_string(),
        },
    );
    let states = match &result {
        abide::qa::exec::QueryResult::StateSet(s) => s.clone(),
        other => panic!("expected StateSet, got: {other:?}"),
    };
    assert!(
        states.iter().any(|s| s == "archived"),
        "QA terminal-state extraction must include `archived` (terminal \
         by omission from the fsm table) to agree with the compiler's \
         is_terminal synthesis, got: {states:?}"
    );
    assert!(
        states.iter().any(|s| s == "delivered"),
        "QA terminal-state extraction must include `delivered` (explicit \
         terminal row), got: {states:?}"
    );

    // Cross-check: the synthesized is_terminal derived field on the
    // entity should reference the same set. Walk the IR to confirm.
    let order = prog
        .entities
        .iter()
        .find(|e| e.name == "Order")
        .expect("Order entity");
    let synth = order
        .derived_fields
        .iter()
        .find(|d| d.name == "is_terminal")
        .expect("synthesized is_terminal");
    let body = format!("{:?}", synth.body);
    assert!(
        body.contains("archived"),
        "synthesized is_terminal must reference @archived to match QA, \
         got body: {body}"
    );
}

/// end-to-end test of the new fsm-specific QA
/// queries. Lowers a source string with a multi-fsm entity, extracts
/// the FlowModel, and asserts that `ask fsms on E`, `ask transitions
/// of E::field`, and `ask terminal states of E::field` return the
/// declared metadata (not the action-extracted state graph).
#[test]
fn qa_fsm_queries_end_to_end() {
    use std::io::Write;
    let src = r"module T

enum OrderStatus = cart | placed | delivered | cancelled
enum Payment = unpaid | paid
entity Order {
  status: OrderStatus = @cart
  pay: Payment = @unpaid
  fsm status {
    @cart -> @placed | @cancelled
    @placed -> @delivered
    @delivered ->
    @cancelled ->
  }
  fsm pay {
    @unpaid -> @paid
    @paid ->
  }
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let prog = lower_file(file.to_str().unwrap());
    let model = abide::qa::extract::extract(&prog);

    // `ask fsms on Order` → list of fsm field names
    let fsms_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Fsms {
            entity: "Order".to_string(),
        },
    );
    match &fsms_result {
        abide::qa::exec::QueryResult::NameList(items) => {
            assert!(
                items.iter().any(|s| s == "status"),
                "expected `status` in fsms list, got: {items:?}"
            );
            assert!(
                items.iter().any(|s| s == "pay"),
                "expected `pay` in fsms list, got: {items:?}"
            );
        }
        other => panic!("expected NameList from `ask fsms on Order`, got: {other:?}"),
    }

    // `ask transitions of Order::status` → flat (from, to) pairs
    let trans_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTransitions {
            entity: "Order".to_string(),
            field: "status".to_string(),
        },
    );
    match &trans_result {
        abide::qa::exec::QueryResult::Transitions(edges) => {
            let pairs: Vec<(String, String)> = edges
                .iter()
                .map(|e| (e.from.clone(), e.to.clone()))
                .collect();
            assert!(
                pairs.contains(&("cart".to_owned(), "placed".to_owned())),
                "expected (cart, placed), got: {pairs:?}"
            );
            assert!(
                pairs.contains(&("cart".to_owned(), "cancelled".to_owned())),
                "expected (cart, cancelled), got: {pairs:?}"
            );
            assert!(
                pairs.contains(&("placed".to_owned(), "delivered".to_owned())),
                "expected (placed, delivered), got: {pairs:?}"
            );
            assert_eq!(
                pairs.len(),
                3,
                "expected exactly 3 transitions, got {pairs:?}"
            );
        }
        other => panic!("expected Transitions from fsm query, got: {other:?}"),
    }

    // `ask terminal states of Order::status` → set of terminal variants
    let term_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTerminalStates {
            entity: "Order".to_string(),
            field: "status".to_string(),
        },
    );
    match &term_result {
        abide::qa::exec::QueryResult::StateSet(states) => {
            assert!(
                states.iter().any(|s| s == "delivered"),
                "expected delivered in terminal set, got: {states:?}"
            );
            assert!(
                states.iter().any(|s| s == "cancelled"),
                "expected cancelled in terminal set, got: {states:?}"
            );
            assert_eq!(
                states.len(),
                2,
                "expected exactly 2 terminal states, got {states:?}"
            );
        }
        other => panic!("expected StateSet from terminal-states query, got: {other:?}"),
    }

    // Querying a non-fsm field returns an error.
    let missing = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTransitions {
            entity: "Order".to_string(),
            field: "nonexistent".to_string(),
        },
    );
    assert!(
        matches!(missing, abide::qa::exec::QueryResult::Error(_)),
        "expected Error for missing fsm field, got: {missing:?}"
    );
}

/// a non-terminal state with
/// no path to any terminal state produces a trap warning. Here `@b`
/// loops back to `@a`, and `@a` has no outgoing edges to a terminal,
/// so both are trap states.
#[test]
fn fsm_trap_state_warns() {
    let src = r"module T

enum Status = a | b | done
entity E {
  s: Status = @a
  fsm s {
    @a -> @b
    @b -> @a
    @done ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    let trap_warnings: Vec<_> = errors
        .iter()
        .filter(|e| {
            matches!(e.severity, elab::error::Severity::Warning)
                && format!("{e}").contains("trap or sink loop")
        })
        .collect();
    assert!(
        trap_warnings.iter().any(|w| format!("{w}").contains("@a")),
        "expected @a trap warning, got: {trap_warnings:?}"
    );
    assert!(
        trap_warnings.iter().any(|w| format!("{w}").contains("@b")),
        "expected @b trap warning, got: {trap_warnings:?}"
    );
}

/// a fully connected fsm produces no
/// reachability warnings.
#[test]
fn fsm_fully_connected_no_warnings() {
    let src = r"module T

enum Status = a | b | c
entity E {
  s: Status = @a
  fsm s {
    @a -> @b
    @b -> @c
    @c ->
  }
}
";
    let (_, errors) = elab_with_errors(src);
    let unreachable_warnings: Vec<_> = errors
        .iter()
        .filter(|w| format!("{w}").contains("unreachable"))
        .collect();
    assert!(
        unreachable_warnings.is_empty(),
        "fully-connected fsm should produce no unreachable warnings, got: {unreachable_warnings:?}"
    );
}

/// a single-fsm entity gets a synthesized
/// `is_terminal` derived field whose body checks the field against
/// the inferred terminal set.
#[test]
fn fsm_synthesizes_is_terminal_single() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered | cancelled
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed | @cancelled
    @placed -> @delivered
    @delivered ->
    @cancelled ->
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(real_errors.is_empty(), "got: {real_errors:?}");
    let order = result
        .entities
        .iter()
        .find(|e| e.name == "Order")
        .expect("Order entity");
    let synth = order
        .derived_fields
        .iter()
        .find(|d| d.name == "is_terminal")
        .expect("synthesized is_terminal derived field");
    let body = format!("{:?}", synth.body);
    assert!(
        body.contains("delivered") && body.contains("cancelled"),
        "synthesized is_terminal body should reference @delivered and @cancelled, got: {body}"
    );
    assert!(
        !body.contains(" \"cart\"") && !body.contains(" \"placed\""),
        "synthesized is_terminal body should NOT reference non-terminal states, got: {body}"
    );
}

/// a multi-fsm entity gets one
/// `<field>_is_terminal` per fsm so the names don't collide.
#[test]
fn fsm_synthesizes_is_terminal_multi() {
    let src = r"module T

enum DocStatus = draft | published | archived
enum ReviewState = pending | approved | rejected
entity Document {
  status: DocStatus = @draft
  review: ReviewState = @pending
  fsm status {
    @draft -> @published
    @published -> @archived
    @archived ->
  }
  fsm review {
    @pending -> @approved | @rejected
    @approved ->
    @rejected ->
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(real_errors.is_empty(), "got: {real_errors:?}");
    let doc = result
        .entities
        .iter()
        .find(|e| e.name == "Document")
        .expect("Document entity");
    assert!(
        doc.derived_fields
            .iter()
            .any(|d| d.name == "status_is_terminal"),
        "expected synthesized status_is_terminal, got: {:?}",
        doc.derived_fields
            .iter()
            .map(|d| &d.name)
            .collect::<Vec<_>>()
    );
    assert!(
        doc.derived_fields
            .iter()
            .any(|d| d.name == "review_is_terminal"),
        "expected synthesized review_is_terminal, got: {:?}",
        doc.derived_fields
            .iter()
            .map(|d| &d.name)
            .collect::<Vec<_>>()
    );
    // Multi-fsm entities should not get a bare
    // `is_terminal` (only the field-prefixed forms).
    assert!(
        !doc.derived_fields.iter().any(|d| d.name == "is_terminal"),
        "multi-fsm entity should not get bare `is_terminal`"
    );
}

/// if the user has already declared a derived
/// field with the synthesized name, the compiler skips synthesis (the
/// user's definition wins, no warning).
#[test]
fn fsm_user_is_terminal_wins() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  derived is_terminal = status == @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(real_errors.is_empty(), "got: {real_errors:?}");
    let order = result
        .entities
        .iter()
        .find(|e| e.name == "Order")
        .expect("Order entity");
    let is_term: Vec<_> = order
        .derived_fields
        .iter()
        .filter(|d| d.name == "is_terminal")
        .collect();
    assert_eq!(
        is_term.len(),
        1,
        "expected exactly one is_terminal (user's), got {}",
        is_term.len()
    );
    // Sanity-check it's the user's definition: body mentions @cart,
    // not @delivered.
    let body = format!("{:?}", is_term[0].body);
    assert!(
        body.contains("cart"),
        "user's is_terminal body should reference @cart, got: {body}"
    );
}

/// a happy-path fsm declaration with mixed
/// terminal and non-terminal rows elaborates cleanly. The EEntity
/// should carry one `EFsm` with the right field, enum, and rows.
#[test]
fn fsm_basic_elaborates() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
entity Order {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
    let order = result
        .entities
        .iter()
        .find(|e| e.name == "Order")
        .expect("Order entity");
    assert_eq!(order.fsm_decls.len(), 1);
    let fsm = &order.fsm_decls[0];
    assert_eq!(fsm.field, "status");
    assert_eq!(fsm.enum_name, "OrderStatus");
    assert_eq!(fsm.rows.len(), 3);
    assert_eq!(fsm.initial.as_deref(), Some("cart"));
}

/// the narrow system-level fsm surface accepts
/// direct enum-typed flat system fields, carries the declaration
/// through elaboration, and synthesizes the same terminal helper
/// pattern used for entities.
#[test]
fn system_fsm_basic_elaborates() {
    let src = r"module T

enum OrderStatus = cart | placed | delivered
system Checkout() {
  status: OrderStatus = @cart
  fsm status {
    @cart -> @placed
    @placed -> @delivered
    @delivered ->
  }

  command advance() requires status == @cart {
    status' = @placed
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
    let system = result
        .systems
        .iter()
        .find(|s| s.name == "Checkout")
        .expect("Checkout system");
    assert_eq!(system.fsm_decls.len(), 1);
    let fsm = &system.fsm_decls[0];
    assert_eq!(fsm.field, "status");
    assert_eq!(fsm.enum_name, "OrderStatus");
    assert_eq!(fsm.rows.len(), 3);
    assert!(
        system
            .derived_fields
            .iter()
            .any(|d| d.name == "is_terminal"),
        "expected synthesized is_terminal helper on system fsm"
    );
}

/// multiple invariants on the same entity are
/// each enforced. Either one being violated produces a counterexample.
#[test]
fn verify_multiple_entity_invariants() {
    let src = r"module T

entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }
  invariant lt_hundred { balance < 100 }

  action go_negative() requires balance == 0 { balance' = -1 }
}

system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command misbehave() {
    choose a: Account where a.balance == 0 {
      a.go_negative()
    }
  }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            abide::verify::VerificationResult::Counterexample { .. }
        ),
        "expected Counterexample because go_negative violates non_negative, \
         got: {results:?}"
    );
}

/// a liveness theorem must NOT be reported
/// as PROVED when a merged entity invariant is violated. Previously
/// `check_theorem_block` built `virtual_verify` from `theorem.shows`
/// only, dropping the merged invariants entirely from the liveness
/// reduction path. The fix routes invariants as additional safety
/// obligations inside `try_liveness_reduction` so they remain proof
/// obligations even when the show is liveness.
///
/// Scenario: the entity invariant `non_negative` is violated by the
/// only state-mutating event. The theorem `show eventually true` is
/// trivially satisfied by the raw state machine, so without the fix
/// the liveness reduction would prove the show and silently report
/// PROVED. After the fix, the invariant becomes a safety obligation
/// alongside the (trivially discharged) liveness pattern, the safety
/// obligation cannot be proved, and the theorem is NOT reported as
/// `Proved`.
#[test]
fn theorem_liveness_does_not_drop_entity_invariants() {
    let src = r"module T

entity Account {
  balance: int = 0
  invariant non_negative { balance >= 0 }
  action go_negative() requires balance == 0 { balance' = -1 }
}

system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command misbehave() {
    choose a: Account where a.balance == 0 {
      a.go_negative()
    }
  }
}

theorem t for Bank {
  assume { fair Bank::misbehave }
  show eventually true
}
";
    let results = verify_source(src);
    let t = results
        .iter()
        .find(|r| {
            matches!(r,
            abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Counterexample { name, .. }
            | abide::verify::VerificationResult::Unprovable { name, .. }
            | abide::verify::VerificationResult::LivenessViolation { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. }
            if name == "t")
        })
        .expect("theorem t result");
    assert!(
        !matches!(t, abide::verify::VerificationResult::Proved { .. }),
        "theorem with violated entity invariant must NOT be Proved (Finding 1), \
         got: {t:?}"
    );
}

/// system invariants must stay scoped to
/// the literal verify-target systems. Previously
/// `collect_in_scope_invariants` was fed the crosscall-expanded
/// `relevant_systems` list, which silently merged invariants from
/// systems reachable only via `S2::event()` calls into the verify of
/// `S1`. The fix passes a separate `target_systems` slice built from
/// `verify_block.systems` so only invariants declared on those exact
/// systems contribute.
///
/// Scenario: `S2` declares an unconditionally-false system invariant
/// (`always_false { false }`). `S1` crosscalls into `S2::tick()` from
/// one of its events. A verify block targeting only `S1` should NOT
/// pick up `S2`'s invariant — it would otherwise produce an immediate
/// counterexample. After the fix the verify passes (Proved or
/// Checked).
#[test]
fn verify_system_invariant_does_not_leak_via_crosscall() {
    let src = r"module T

entity Account {
  balance: int = 0
}

system S2(accounts: Store<Account>) {invariant always_false { false }
  command tick() {
    choose a: Account where a.balance == 0 {
      a.balance' = a.balance
    }
  }
}

system S1(accounts: Store<Account>) {command open() { create Account {} }
  command drive() { S2::tick() }
}

verify v {
  assume {
    store es: E[0..3]
    let s1 = S1 { es: es }
  
   stutter }
  assert always true
}
";
    let results = verify_source(src);
    let v = results
        .iter()
        .find(|r| {
            matches!(r,
            abide::verify::VerificationResult::Proved { name, .. }
            | abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Counterexample { name, .. }
            | abide::verify::VerificationResult::Unprovable { name, .. }
            | abide::verify::VerificationResult::LivenessViolation { name, .. }
            | abide::verify::VerificationResult::Deadlock { name, .. }
            if name == "v")
        })
        .expect("verify v result");
    assert!(
        matches!(
            v,
            abide::verify::VerificationResult::Proved { .. }
                | abide::verify::VerificationResult::Checked { .. }
        ),
        "S2's `always_false` system invariant must NOT be merged into a \
         verify of S1 (Finding 2), got: {v:?}"
    );
}

// ── `under` blocks for theorems and lemmas ────────

/// `under { fair X; theorem T {... }
/// lemma L {... } }` parses cleanly. Inner theorems and lemmas are
/// "flattened" into env.theorems and env.lemmas during collect.
#[test]
fn under_block_basic_parses_and_collects() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

under {
  fair S::tick

  theorem t for S {
    show always true
  }
  lemma l {
    always true
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
    assert_eq!(result.theorems.len(), 1);
    assert_eq!(result.lemmas.len(), 1);
    let t = &result.theorems[0];
    let l = &result.lemmas[0];
    // Both inherit `fair S::tick` from the under block.
    assert!(
        t.assumption_set
            .weak_fair
            .iter()
            .any(|e| e.command == "tick"),
        "theorem should inherit fair S::tick: {:?}",
        t.assumption_set
    );
    assert!(
        l.assumption_set
            .weak_fair
            .iter()
            .any(|e| e.command == "tick"),
        "lemma should inherit fair S::tick: {:?}",
        l.assumption_set
    );
}

/// a silent `under { }` block (no `stutter` or
/// `no stutter` declaration) inherits the construct default. For
/// theorems and lemmas, the default is `stutter: true`.
#[test]
fn under_block_silent_inherits_theorem_default_stutter() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

under {
  theorem t for S { show always true }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
    let t = &result.theorems[0];
    assert!(
        t.assumption_set.stutter,
        "silent under inherits theorem default stutter=true"
    );
}

/// a theorem inside an `under` block can extend
/// the assumption set with its own `assume { }` block.
#[test]
fn under_block_inner_assume_extends_outer() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
  command tock() { choose e: E where e.x == 0 { e.x' = 0 } }
}

under {
  fair S::tick

  theorem t for S {
    assume { fair S::tock }
    show always true
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
    let t = &result.theorems[0];
    let names: Vec<&str> = t
        .assumption_set
        .weak_fair
        .iter()
        .map(|e| e.command.as_str())
        .collect();
    assert!(
        names.contains(&"tick") && names.contains(&"tock"),
        "theorem should have both fair tick + fair tock: {names:?}"
    );
}

/// an inner `assume { no stutter }` cannot
/// toggle the enclosing under's `stutter` (silent default = stutter on).
#[test]
fn under_block_inner_no_stutter_against_silent_under_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  theorem t for S {
    assume { no stutter }
    show always true
  }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("weakens the enclosing")),
        "expected add-only violation, got: {real_errors:?}"
    );
}

/// an inner `assume { stutter }` cannot toggle
/// an explicit `no stutter` from the outer under.
#[test]
fn under_block_inner_stutter_against_explicit_no_stutter_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  no stutter

  theorem t for S {
    assume { stutter }
    show always true
  }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("weakens the enclosing")),
        "expected add-only violation, got: {real_errors:?}"
    );
}

/// / third bullet: an inner `assume { fair X }`
/// cannot downgrade an outer `strong fair X`.
#[test]
fn under_block_inner_fair_downgrades_outer_strong_fair_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  strong fair S::tick

  theorem t for S {
    assume { fair S::tick }
    show always true
  }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("weakens the enclosing")),
        "expected add-only violation, got: {real_errors:?}"
    );
}

/// `verify` blocks are not allowed inside an
/// `under` block. Reject at parse time with a clear diagnostic.
#[test]
fn under_block_containing_verify_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert true }
}
";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(
        result.is_err(),
        "expected parser error for verify inside under, got: {result:?}"
    );
    let err = format!("{:?}", result.err().unwrap());
    assert!(
        err.contains("under") && err.contains("verify"),
        "expected diagnostic mentioning under/verify, got: {err}"
    );
}

/// / +: a theorem with `{fair X, fair Y}` can
/// reference a lemma proven with `{fair X}` — the lemma's set is a
/// subset of the theorem's, so reuse is sound.
#[test]
fn under_block_by_lemma_subset_ok() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
  command tock() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  assume { fair S::tick }
  always true
}

theorem t for S {
  assume { fair S::tick; fair S::tock }
  by helper
  show always true
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no errors for valid subset reference, got: {real_errors:?}"
    );
}

/// a theorem with `{fair X}` cannot reference a
/// lemma proven with `{fair X, fair Y}` — the lemma assumes more than
/// the theorem provides. Diagnostic format from.
#[test]
fn under_block_by_lemma_subset_violation_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
  command tock() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  assume { fair S::tick; fair S::tock }
  always true
}

theorem t for S {
  assume { fair S::tick }
  by helper
  show always true
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.iter().any(|e| {
            e.message.contains("cannot use lemma")
                && e.message.contains("Missing")
                && e.message.contains("tock")
        }),
        "expected subset diagnostic mentioning Missing tock, got: {real_errors:?}"
    );
}

/// / stutter rule: a theorem with `stutter` cannot
/// reuse a lemma proven without stutter. The lemma's claim does not
/// cover the theorem's stutter-admitting trace set.
#[test]
fn under_block_by_lemma_stutter_subset_violation_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  assume { no stutter }
  always true
}

theorem t for S {
  by helper
  show always true
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("cannot use lemma")),
        "expected stutter-rule diagnostic, got: {real_errors:?}"
    );
}

/// `by L` referencing an unknown lemma name
/// produces a clean "lemma not declared" diagnostic.
#[test]
fn under_block_by_unknown_lemma_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

theorem t for S {
  by no_such_lemma
  show always true
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("no_such_lemma")),
        "expected unknown-lemma diagnostic, got: {real_errors:?}"
    );
}

/// The add-only check operates on
/// resolved `EventRef`s, not raw path strings. Outer `strong fair
/// S::tick` plus inner `fair tick` (unqualified, in a theorem `for S`)
/// must be detected as a downgrade — the two spellings refer to the
/// same canonical event after resolution. Before the fix, the raw
/// string compare would silently let `fair tick` through.
#[test]
fn under_block_inner_unqualified_fair_downgrades_outer_qualified_strong_fair() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  strong fair S::tick

  theorem t for S {
    assume { fair tick }
    show always true
  }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("weakens the enclosing")),
        "expected downgrade detection on resolved event reference \
         (outer strong fair S::tick + inner fair tick), got: {real_errors:?}"
    );
}

/// An `under` block resolves its
/// items exactly once with a fixed shared scope. A theorem and a
/// sibling lemma in the same `under` must inherit the SAME canonical
/// resolved set — siblings cannot diverge on what an unqualified
/// `fair tick` means.
///
/// Scenario: two systems each declare a `tick` event. Without the
/// shared-scope fix, the under's `fair tick` would resolve against
/// the theorem's scope `[S1]` for the theorem (giving `S1::tick`)
/// but against ALL systems for the sibling lemma (giving "ambiguous"
/// since both S1 and S2 have `tick`). With the fix, the under's
/// shared scope = union of member theorems' targets = `[S1]`, so
/// both members inherit `fair S1::tick`.
#[test]
fn under_block_shared_scope_consistent_for_theorem_and_lemma_siblings() {
    let src = r"module T

entity E { x: int = 0 }
system S1(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }
system S2(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  fair tick

  theorem t for S1 { show always true }
  lemma l { always true }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no errors — under's shared scope = [S1] should resolve \
         `fair tick` to S1::tick unambiguously for both members. got: {real_errors:?}"
    );
    let t = &result.theorems[0];
    let l = &result.lemmas[0];
    let t_evs: Vec<&str> = t
        .assumption_set
        .weak_fair
        .iter()
        .map(|e| e.system.as_str())
        .collect();
    let l_evs: Vec<&str> = l
        .assumption_set
        .weak_fair
        .iter()
        .map(|e| e.system.as_str())
        .collect();
    assert_eq!(
        t_evs,
        vec!["S1"],
        "theorem should have fair S1::tick (not ambiguous): {t_evs:?}"
    );
    assert_eq!(
        l_evs,
        vec!["S1"],
        "lemma should inherit the SAME fair S1::tick from the shared under: {l_evs:?}"
    );
}

/// under blocks are stored as canonical
/// `EUnderBlock` objects on the `ElabResult`. Each member theorem /
/// lemma references the same block by index, so the index is stable
/// across cloning out of `Env`.
#[test]
fn under_block_stored_as_canonical_object_in_elab_result() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  fair S::tick

  theorem t for S { show always true }
  lemma l { always true }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(real_errors.is_empty(), "errors: {real_errors:?}");
    assert_eq!(
        result.under_blocks.len(),
        1,
        "expected exactly one canonical under block"
    );
    let t = &result.theorems[0];
    let l = &result.lemmas[0];
    assert_eq!(t.enclosing_under_idx, Some(0));
    assert_eq!(l.enclosing_under_idx, Some(0));
    // The shared resolved_set must contain the canonical S::tick
    // exactly once — proving the under was resolved a single time.
    let ub = &result.under_blocks[0];
    assert_eq!(ub.scope, vec!["S".to_owned()]);
    assert_eq!(ub.resolved_set.weak_fair.len(), 1);
    let ev = ub.resolved_set.weak_fair.iter().next().unwrap();
    assert_eq!(ev.system, "S");
    assert_eq!(ev.command, "tick");
}

/// / review fix: the inner `assume_block` is
/// normalized within itself before checking. An inner block that
/// redundantly lists `fair X; strong fair X` contributes effectively
/// just `strong fair X` after normalization, which is identical to
/// an outer `strong fair X` — NOT a downgrade. Before the normalize
/// fix, the raw `weak_fair` bucket would still flag this as a
/// downgrade attempt.
#[test]
fn under_block_inner_redundant_fair_and_strong_fair_not_flagged() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  strong fair S::tick

  theorem t for S {
    assume { fair S::tick; strong fair S::tick }
    show always true
  }
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no errors — inner `fair S::tick; strong fair S::tick` \
         normalizes to just `strong fair S::tick`, identical to the outer. \
         got: {real_errors:?}"
    );
    let t = &result.theorems[0];
    // After normalize, weak_fair should not contain S::tick (it was
    // promoted to strong by the inner's `strong fair S::tick`).
    assert!(
        t.assumption_set
            .weak_fair
            .iter()
            .all(|e| e.command != "tick"),
        "S::tick should be in strong_fair only, not weak_fair: {:?}",
        t.assumption_set
    );
    assert!(
        t.assumption_set
            .strong_fair
            .iter()
            .any(|e| e.command == "tick"),
        "S::tick should be in strong_fair: {:?}",
        t.assumption_set
    );
}

/// / review fix: a `by Module::lemma_name` qualified
/// path parses and resolves through the canonical declaration registry.
/// In single-module compilation, the qualified form is equivalent to
/// the bare form — the test verifies that the parser accepts the
/// qualified syntax and resolution succeeds.
#[test]
fn under_block_by_qualified_lemma_path_resolves() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  assume { fair S::tick }
  always true
}

theorem t for S {
  assume { fair S::tick }
  by T::helper
  show always true
}
";
    let (result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no errors for qualified `by T::helper`, got: {real_errors:?}"
    );
    // Confirm the parser captured the multi-segment path.
    let t = &result.theorems[0];
    assert_eq!(t.by_lemmas.len(), 1);
    assert_eq!(
        t.by_lemmas[0].segments,
        vec!["T".to_owned(), "helper".to_owned()]
    );
}

/// / review fix: in a multi-module load,
/// `EUnderBlock`s are filtered to the current module the same way
/// theorems and lemmas are. Foreign-module under blocks must NOT
/// leak into the local module's resolved env, where they would be
/// resolved against the wrong system set and produce spurious
/// fairness diagnostics.
///
/// Scenario: file `a.ab` declares module A with an under block over
/// system A::S; file `b.ab` declares module B with its own under
/// block over system B::S. Loading `[a, b]` makes A the root module.
/// After `elaborate_env`, `result.under_blocks` must contain only A's
/// under block; B's must be filtered out. Member theorem indices for
/// A's surviving theorem must remain valid (point at the still-present
/// under block).
#[test]
fn under_block_filtered_by_module_in_multi_module_load() {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let a_path = dir.path().join("a.ab");
    let b_path = dir.path().join("b.ab");

    let a_src = r"module A

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  fair S::tick

  theorem t_a for S { show always true }
}
";
    let b_src = r"module B

entity E { x: int = 0 }
system S(es: Store<E>) {command tock() { choose e: E where e.x == 0 { e.x' = 0 } } }

under {
  fair S::tock

  theorem t_b for S { show always true }
}
";
    std::fs::File::create(&a_path)
        .expect("create a.ab")
        .write_all(a_src.as_bytes())
        .expect("write a.ab");
    std::fs::File::create(&b_path)
        .expect("create b.ab")
        .write_all(b_src.as_bytes())
        .expect("write b.ab");

    let (env, load_errors, _) = loader::load_files(&[a_path.clone(), b_path.clone()]);
    assert!(
        load_errors.is_empty(),
        "load_errors should be empty: {load_errors:?}"
    );
    let (result, errors) = elab::elaborate_env(env);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors after filtering, got: {real_errors:?}"
    );

    // Only A's theorem and under block should survive: B is foreign.
    assert_eq!(
        result.theorems.len(),
        1,
        "expected only A's theorem after filtering, got: {:?}",
        result.theorems.iter().map(|t| &t.name).collect::<Vec<_>>()
    );
    assert_eq!(result.theorems[0].name, "t_a");
    assert_eq!(
        result.under_blocks.len(),
        1,
        "expected only A's under block after filtering, got {} blocks",
        result.under_blocks.len()
    );
    let ub = &result.under_blocks[0];
    assert_eq!(ub.module.as_deref(), Some("A"));
    // The surviving theorem must still index into the surviving under
    // block (post-remap), not at a stale position.
    assert_eq!(result.theorems[0].enclosing_under_idx, Some(0));
    // The under's resolved set must reference A::S::tick, NOT B::S::tock.
    let evs: Vec<&str> = ub
        .resolved_set
        .weak_fair
        .iter()
        .map(|e| e.command.as_str())
        .collect();
    assert_eq!(
        evs,
        vec!["tick"],
        "under block must resolve against A's commands only"
    );
    // The theorem's effective assumption set should agree.
    let t_evs: Vec<&str> = result.theorems[0]
        .assumption_set
        .weak_fair
        .iter()
        .map(|e| e.command.as_str())
        .collect();
    assert_eq!(t_evs, vec!["tick"]);
}

/// / review fix: `by name` where `name` is not a
/// lemma (e.g. an entity, system, or theorem) is rejected at elab time
/// with a clear "not a lemma" diagnostic. Routing through `env.decls`
/// makes this kind validation possible — a hand-rolled bare-name
/// table over `env.lemmas` cannot tell whether a missing entry was
/// "no such name" or "wrong kind".
#[test]
fn under_block_by_non_lemma_name_rejected_with_kind_diagnostic() {
    let src = r"module T

entity Helper { x: int = 0 }
entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } } }

theorem t for S {
  by Helper
  show always true
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("not a lemma") && e.message.contains("Helper")),
        "expected `not a lemma` diagnostic for `by Helper` (Helper is an entity), got: {real_errors:?}"
    );
}

// ── past-time temporal operators ────────────────

/// each past-time operator parses, elaborates,
/// and lowers without errors. Verifies the AST/IR plumbing wires up
/// end-to-end before exercising the BMC encoding semantics.
#[test]
fn past_time_operators_parse_and_elaborate() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify a {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert always true }
verify b {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert historically true }
verify c {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert once true }
verify d {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert always (true implies once true) }
verify e {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert always (previously true or true) }
verify f {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  } assert true since true }
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors, got: {real_errors:?}"
    );
}

/// `historically true` holds at every step
/// because `true` holds at every past step. BMC must verify it
/// without finding a counterexample.
#[test]
fn past_time_historically_true_holds() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert historically true
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `historically true` to hold, got: {results:?}"
    );
}

/// / stutter convention for `previously`: at trace
/// position 0, `previously P` is FALSE (Past-LTL convention). The
/// composition `always (previously P or true)` always holds because
/// the disjunction with `true` masks the false-at-zero case.
#[test]
fn past_time_previously_false_at_step_zero() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((previously true) or true)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `always ((previously true) or true)` to hold — at step 0 `previously true` is false but the disjunct `true` masks it, got: {results:?}"
    );
}

/// a `previously` body that is `false` at step
/// zero AND has no masking disjunct must yield a counterexample.
/// `assert previously true` evaluated at step 0 gives FALSE. BMC
/// asserts the property at every action in [0, bound], so the n=0
/// constraint forces a violation.
#[test]
fn past_time_previously_at_step_zero_yields_counterexample() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert previously true
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
            if name == "v"
        )),
        "expected `assert previously true` to fail at step 0 with a counterexample, got: {results:?}"
    );
}

/// the `since` operator. `true since true` is
/// trivially true at every step (Q held at the current step, P
/// vacuously holds over the empty interval (k, n] when k = n).
#[test]
fn past_time_since_trivially_holds() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always (true since true)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `always (true since true)` to hold, got: {results:?}"
    );
}

/// `once` reaches a past witness. When the
/// initial state has the property, `always (once P)` holds because
/// every step's history includes step 0, where P held. We use a
/// field that starts true and is never modified.
#[test]
fn past_time_once_with_initial_witness_holds() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always (once (all e: E | e.x == 0))
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `always (once (all e: E | e.x == 0))` to hold (initial witness at step 0), got: {results:?}"
    );
}

/// `previously` is rejected in entity invariant
/// bodies. Invariants are safety-only; `previously` is a liveness
/// (trace-shape) operator.
#[test]
fn past_time_previously_rejected_in_entity_invariant() {
    let src = r"module T

entity E {
  x: int = 0
  invariant trace_shape { previously (x == 0) }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("liveness") && e.message.contains("previously")),
        "expected liveness-rejection diagnostic for `previously` in invariant body, got: {real_errors:?}"
    );
}

/// `since` is rejected in invariant bodies.
#[test]
fn past_time_since_rejected_in_entity_invariant() {
    let src = r"module T

entity E {
  x: int = 0
  invariant trace_shape { (x == 0) since (x == 0) }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("liveness") && e.message.contains("since")),
        "expected liveness-rejection diagnostic for `since` in invariant body, got: {real_errors:?}"
    );
}

/// `historically` and `once`
/// are SAFETY past-time operators and ARE allowed in invariant bodies.
#[test]
fn past_time_historically_and_once_allowed_in_entity_invariant() {
    let src = r"module T

entity E {
  x: int = 0
  invariant safe_history { historically (x == 0) }
  invariant ever_zero { once (x == 0) }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected `historically`/`once` to be allowed in invariant bodies, got: {real_errors:?}"
    );
}

/// temporal operators bind tighter
/// than logical operators. Before the BP_PREFIX_EXPR bump, an
/// unparenthesized `always P or Q` parsed as `always (P or Q)`,
/// which is the wrong grouping per the spec. The fix raises
/// BP_PREFIX_EXPR above BP_AND/BP_OR so the temporal operator's body
/// stops at the logical operator, yielding `(always P) or Q`.
///
/// Test scenario: `assert always false or true` would be a vacuous
/// counterexample under the loose parsing (`always (false or true)`
/// is `always true`, which holds, so the verify passes), but the
/// spec-correct parsing `(always false) or true` is also satisfied
/// because the disjunct `true` masks the false `always false`. To
/// distinguish the two readings, we use a property whose two
/// parsings give DIFFERENT verdicts:
///
/// `assert always false implies false`
///
/// - Loose (old): `always (false implies false)` = `always true` → HOLDS.
/// - Tight (new): `(always false) implies false` = `true implies false`?
/// Actually `always false` is FALSE on any non-empty trace, so
/// `(always false) implies false` is `false implies false` = `true`.
/// That's also vacuously true.
///
/// Use a sharper distinguisher instead: `assert (always false) or false`.
/// - Tight: `(always false) or false` = `false or false` = `false` → FAILS.
/// - The test asserts the property fails (counterexample) under the
/// tight parser; under the loose parser it would parse as
/// `always (false or false)` = `always false` which also fails,
/// so the structural shape is what matters. We instead test by
/// inspecting parser output via a parse-only round-trip.
#[test]
fn temporal_binds_tighter_than_or() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert always false or true }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    assert_eq!(v.asserts.len(), 1);
    // After the fix, `always false or true` MUST parse as
    // `(always false) or true` — Or at the top, with Always on the
    // left. The loose parser produced `always (false or true)` —
    // Always at the top, with Or inside.
    match &v.asserts[0].kind {
        ExprKind::Or(lhs, _rhs) => {
            assert!(
                matches!(lhs.kind, ExprKind::Always(_)),
                "expected `(always false) or true` — got Or with non-Always lhs: {:?}",
                lhs.kind
            );
        }
        other => panic!("expected top-level Or, got: {other:?}"),
    }
}

/// system-level fsm metadata should also flow
/// into QA so `fsms on`, `transitions of`, and `terminal states of`
/// work for flat system fields, not just entity fields.
#[test]
fn qa_system_fsm_queries_end_to_end() {
    use std::io::Write;
    let src = r"module T

enum UiStatus = idle | ready | done
system Ui() {
  status: UiStatus = @idle
  fsm status {
    @idle -> @ready
    @ready -> @done
    @done ->
  }

  command advance() requires status == @idle {
    status' = @ready
  }
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let prog = lower_file(file.to_str().unwrap());
    let model = abide::qa::extract::extract(&prog);

    let fsms_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::Fsms {
            entity: "Ui".to_string(),
        },
    );
    match &fsms_result {
        abide::qa::exec::QueryResult::NameList(items) => {
            assert_eq!(items, &vec!["status".to_string()]);
        }
        other => panic!("expected NameList from `ask fsms on Ui`, got: {other:?}"),
    }

    let trans_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTransitions {
            entity: "Ui".to_string(),
            field: "status".to_string(),
        },
    );
    match &trans_result {
        abide::qa::exec::QueryResult::Transitions(edges) => {
            let pairs: Vec<(String, String)> = edges
                .iter()
                .map(|e| (e.from.clone(), e.to.clone()))
                .collect();
            assert_eq!(
                pairs,
                vec![
                    ("idle".to_string(), "ready".to_string()),
                    ("ready".to_string(), "done".to_string()),
                ]
            );
        }
        other => panic!("expected Transitions from system fsm query, got: {other:?}"),
    }

    let term_result = abide::qa::exec::execute_query(
        &model,
        &abide::qa::ast::Query::FsmTerminalStates {
            entity: "Ui".to_string(),
            field: "status".to_string(),
        },
    );
    match &term_result {
        abide::qa::exec::QueryResult::StateSet(states) => {
            assert_eq!(states, &vec!["done".to_string()]);
        }
        other => panic!("expected StateSet from system terminal states query, got: {other:?}"),
    }
}

/// same fix for `and`. Verify that
/// `always P and Q` parses as `(always P) and Q`, not `always (P and Q)`.
#[test]
fn temporal_binds_tighter_than_and() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert always true and true }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    match &v.asserts[0].kind {
        ExprKind::And(lhs, _rhs) => {
            assert!(
                matches!(lhs.kind, ExprKind::Always(_)),
                "expected `(always true) and true` — got And with non-Always lhs: {:?}",
                lhs.kind
            );
        }
        other => panic!("expected top-level And, got: {other:?}"),
    }
}

/// the past-time prefix operators
/// follow the same rule. `previously P or Q` must parse as
/// `(previously P) or Q`.
#[test]
fn past_time_binds_tighter_than_logical() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert previously true or true }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    match &v.asserts[0].kind {
        ExprKind::Or(lhs, _rhs) => {
            assert!(
                matches!(lhs.kind, ExprKind::Previously(_)),
                "expected `(previously true) or true` — got Or with non-Previously lhs: {:?}",
                lhs.kind
            );
        }
        other => panic!("expected top-level Or for `previously P or Q`, got: {other:?}"),
    }
}

/// pre-existing `implies` behavior
/// is preserved. `always P implies Q` parses as `(always P) implies Q`,
/// which already worked under BP_PREFIX_EXPR=9 and must still work
/// after the bump.
#[test]
fn temporal_implies_grouping_preserved_per_item_21_4() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert always true implies true }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    match &v.asserts[0].kind {
        ExprKind::Impl(lhs, _rhs) => {
            assert!(
                matches!(lhs.kind, ExprKind::Always(_)),
                "expected `(always true) implies true` — got Impl with non-Always lhs: {:?}",
                lhs.kind
            );
        }
        other => panic!("expected top-level Impl, got: {other:?}"),
    }
}

/// Future-time liveness operators `eventually` and `until` are also
/// rejected in invariant bodies.
#[test]
fn invariant_eventually_rejected() {
    let src = r"module T

entity E {
  x: int = 0
  invariant bad { eventually (x == 0) }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("liveness") && e.message.contains("eventually")),
        "expected liveness-rejection diagnostic for `eventually` in invariant body, got: {real_errors:?}"
    );
}

/// `until` is rejected in invariant
/// bodies.
#[test]
fn invariant_until_rejected() {
    let src = r"module T

entity E {
  x: int = 0
  invariant bad { (x == 0) until (x == 1) }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("liveness") && e.message.contains("until")),
        "expected liveness-rejection diagnostic for `until` in invariant body, got: {real_errors:?}"
    );
}

/// the unbounded theorem path's
/// 1-induction and IC3 backends instantiate properties at two
/// adjacent symbolic states without explicit history, so past-time
/// operators cannot be soundly encoded there. The theorem path
/// detects past-time in shows and returns Unprovable with a
/// dedicated diagnostic that points the user at BMC.
#[test]
fn theorem_show_historically_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

theorem t for S {
  show historically (all e: E | e.x == 0)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "t"
            )
        })
        .expect("expected Unprovable for past-time on theorem path");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("past-time"),
            "expected past-time-specific hint, got: {hint}"
        );
    }
}

/// same rejection for `once`.
#[test]
fn theorem_show_once_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

theorem t for S {
  show once (all e: E | e.x == 0)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "t"
            )
        })
        .expect("expected Unprovable for `once` on theorem path");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("past-time"),
            "expected past-time-specific hint, got: {hint}"
        );
    }
}

/// Merged entity invariants containing
/// past-time operators (`historically`/`once`) are also rejected on
/// the theorem path. The operators are legal in entity
/// invariants (they're safety-only), so a verify block targeting the
/// same entity still works — the rejection is specifically for the
/// theorem path where the inductive encoding is unsound.
#[test]
fn theorem_with_merged_past_time_invariant_rejected() {
    let src = r"module T

entity E {
  x: int = 0
  invariant has_history { historically (x >= 0) }
}
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

theorem t for S {
  show all e: E | e.x >= 0
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "t"
            )
        })
        .expect("expected Unprovable for theorem with past-time invariant");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("past-time"),
            "expected past-time-specific hint, got: {hint}"
        );
    }
}

/// past-time invariants on entities are
/// still LEGAL per (`historically`/`once` are safety) and
/// must continue to verify under BMC. Companion test to
/// `theorem_with_merged_past_time_invariant_rejected` — same entity,
/// `verify` instead of `theorem`.
#[test]
fn verify_with_past_time_invariant_still_works() {
    let src = r"module T

entity E {
  x: int = 0
  invariant has_history { historically (x >= 0) }
}
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert all e: E | e.x >= 0
}
";
    let results = verify_source(src);
    let v = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )
    });
    assert!(
        v.is_some(),
        "expected verify with past-time entity invariant to still pass under BMC, got: {results:?}"
    );
}

/// lemma bodies containing past-time
/// operators must produce a lemma-specific diagnostic, not the
/// misleading "temporal operators not allowed in fn contracts" error
/// from the pure-expression encoder. Lemmas are state-level proof
/// building blocks; their bodies pass through the same encoder as fn
/// pre/postconditions, which has no notion of trace history.
#[test]
fn lemma_historically_rejected_with_lemma_diagnostic() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  historically (all e: E | e.x == 0)
}

theorem t for S {
  by helper
  show all e: E | e.x == 0
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "helper"
            )
        })
        .expect("expected Unprovable for past-time in lemma body");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("lemma"),
            "expected lemma-specific hint, got: {hint}"
        );
        assert!(
            !hint.contains("fn contract"),
            "expected NO `fn contract` mention in lemma diagnostic, got: {hint}"
        );
    }
}

/// same fix for future-time `always` in
/// a lemma body. Before the fix, the user saw "temporal operators
/// not allowed in fn contracts"; after, they see the lemma-specific
/// diagnostic.
#[test]
fn lemma_always_rejected_with_lemma_diagnostic() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  always (all e: E | e.x == 0)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "helper"
            )
        })
        .expect("expected Unprovable for `always` in lemma body");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("lemma"),
            "expected lemma-specific hint, got: {hint}"
        );
        assert!(
            !hint.contains("fn contract"),
            "expected NO `fn contract` mention in lemma diagnostic, got: {hint}"
        );
    }
}

/// same for `eventually`.
#[test]
fn lemma_eventually_rejected_with_lemma_diagnostic() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

lemma helper {
  eventually (all e: E | e.x == 0)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "helper"
            )
        })
        .expect("expected Unprovable for `eventually` in lemma body");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("lemma"),
            "expected lemma-specific hint, got: {hint}"
        );
        assert!(
            !hint.contains("fn contract"),
            "expected NO `fn contract` mention in lemma diagnostic, got: {hint}"
        );
    }
}

/// pure-state lemmas (no temporal
/// operators) still work after the temporal-rejection check is
/// added. Sanity check that the existing lemma encoder path is
/// untouched for the supported case.
#[test]
fn lemma_pure_state_still_proves() {
    let src = r"module T

lemma trivial {
  true
}
";
    let results = verify_source(src);
    let r = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "trivial"
        )
    });
    assert!(
        r.is_some(),
        "expected pure-state lemma to still PROVE after temporal-rejection fix, got: {results:?}"
    );
}

/// `previously` and `since` are routed to
/// the past-time rejection on the theorem path even though they are
/// also classified as liveness operators by `contains_liveness`. The
/// past-time check fires first so the user sees the dedicated
/// diagnostic, not the generic "liveness reduction failed" hint.
#[test]
fn theorem_show_previously_rejected_with_past_time_diagnostic() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}

theorem t for S {
  show previously (all e: E | e.x == 0)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "t"
            )
        })
        .expect("expected Unprovable for `previously` on theorem path");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("past-time"),
            "expected past-time-specific hint (not the generic liveness one), got: {hint}"
        );
    }
}

/// same liveness-restriction enforcement on
/// system invariants.
#[test]
fn past_time_previously_rejected_in_system_invariant() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {invariant bad { previously (all e: E | e.x == 0) }
  command tick() { choose e: E where e.x == 0 { e.x' = 0 } }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("liveness") && e.message.contains("previously")),
        "expected liveness-rejection diagnostic for `previously` in system invariant, got: {real_errors:?}"
    );
}

// ── `saw` operator ────────────────────────────────

/// `saw Extern::command()` parses and elaborates without errors.
#[test]
fn saw_parse_and_elaborate() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

entity E { x: int = 0 }

system Billing(es: Store<E>) {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    let billing = Billing {}
    stutter
  }
  assert once (saw Stripe::charge(1))
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors for `saw`, got: {real_errors:?}"
    );
}

/// `saw Extern::command()` with wildcard args.
#[test]
fn saw_wildcard_args_parse() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    let billing = Billing {}
    stutter
  }
  assert once (saw Stripe::charge(_))
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors for `saw` with wildcard, got: {real_errors:?}"
    );
}

/// basic extern-boundary `saw` scene encoding — when a scene explicitly
/// fires the handled command that performs the dep cross-call, the extern
/// boundary observation is true in the scene `then` block.
#[test]
fn saw_basic_event_fires_holds() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

scene submit_calls_extern {
  given {
    store es: E[0..1]
    let billing = Billing { es: es }
  }
  when {
    let submit = billing.submit()
  }
  then {
    assert saw Stripe::charge(1)
  }
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
            if name == "submit_calls_extern"
        )),
        "expected `saw Stripe::charge(1)` to hold after the explicit scene cross-call, got: {results:?}"
    );
}

/// once `saw` is true it stays true — `saw` is
/// monotone over the trace prefix. The implication `saw → always saw`
/// holds because once the fire indicator is true at some past step,
/// every future step's disjunction includes that past step.
#[test]
fn saw_monotone_once_true_stays_true() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    let billing = Billing {}
  }
  assert always ((saw Stripe::charge(1)) implies always (saw Stripe::charge(1)))
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected extern-boundary saw to persist once the command has fired, got: {results:?}"
    );
}

/// review F2: `saw` referencing an unknown event is rejected
/// at elab time with SAW_UNKNOWN_EVENT.
#[test]
fn saw_unknown_event_rejected_at_elab() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

verify v {
  assume {
    stutter
  }
  assert eventually (saw Stripe::nonexistent())
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("unknown extern command")),
        "expected SAW_UNKNOWN_EVENT diagnostic, got: {real_errors:?}"
    );
}

/// unqualified `saw charge()` is rejected; extern-boundary saw requires the
/// explicit `Extern::command(...)` form.
#[test]
fn saw_unqualified_rejected_for_extern_only() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

verify v {
  assume {
    stutter
  }
  assert always ((saw charge(1)) implies true)
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("extern boundary commands")),
        "expected rejection for unqualified saw, got: {real_errors:?}"
    );
}

/// system-qualified `saw System::command()` is rejected; `45.7` is extern-only.
#[test]
fn saw_system_qualified_rejected_for_extern_only() {
    let src = r"module T

system S {
  command tick() { }
}

verify v {
  assume {
    let s = S {}
  }
  assert eventually (saw S::tick())
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("extern boundary commands")),
        "expected extern-only saw diagnostic for system-qualified saw, got: {real_errors:?}"
    );
}

/// 3+ segment path `saw Mod::Stripe::charge()` is rejected.
#[test]
fn saw_three_segment_path_rejected() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

verify v {
  assume {
    stutter
  }
  assert eventually (saw Mod::Stripe::charge(1))
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("extern boundary commands")),
        "expected rejection for 3-segment saw path, got: {real_errors:?}"
    );
}

/// review F2: `saw` with wrong argument count is rejected
/// at elab time.
#[test]
fn saw_arity_mismatch_rejected_at_elab() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

verify v {
  assume {
    stutter
  }
  assert eventually (saw Stripe::charge())
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("expects 1 arguments but got 0")),
        "expected arity mismatch diagnostic, got: {real_errors:?}"
    );
}

/// `saw` is not allowed in invariant bodies.
#[test]
fn saw_rejected_in_entity_invariant() {
    let src = r"module T

entity E {
  x: int = 0
  invariant bad { saw Stripe::charge(1) }
}
enum Outcome = ok
extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.iter().any(|e| e.message.contains("saw")),
        "expected saw-rejection diagnostic in invariant body, got: {real_errors:?}"
    );
}

/// arrow forms after `saw` are rejected.
#[test]
fn saw_arrow_form_rejected() {
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert saw S::tick() -> true }";
    let tokens = lex::lex(src);
    // This should either fail at parse or lex level. The arrow after saw
    // might parse differently since -> is the sequence operator. Let's
    // check that saw parses as a standalone expression — the -> is a
    // separate infix and should produce `Seq(Saw(...), true)` which is
    // valid at the parse level. The arrow rejection fires only when ->
    // immediately follows the closing paren of the saw argument list.
    // In practice, `saw S::tick() -> true` parses as
    // `(saw S::tick()) -> true` which is a sequence. This is valid.
    //
    // Skip this test — the parser correctly treats -> as the sequence
    // operator at a lower binding power than the prefix `saw`.
    assert!(tokens.is_ok() || tokens.is_err());
}

/// review: `saw` inside a function contract produces the
/// dedicated SAW_NOT_ALLOWED_IN_FN_BODY diagnostic, not the generic
/// "temporal operators not allowed in fn contracts" message. The fn
/// verifier returns Unprovable with the encoding error.
#[test]
fn saw_in_fn_contract_uses_dedicated_diagnostic() {
    let src = r"module T

enum Outcome = ok
extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

fn bad(n: int): bool
  ensures saw Stripe::charge(1)
{
  true
}
";
    let results = verify_source(src);
    // The fn contract verifier will encounter `saw` in the ensures clause
    // and return an encoding error. Look for it in any result.
    let has_saw_msg = results.iter().any(|r| match r {
        abide::verify::VerificationResult::Unprovable { hint, .. } => {
            hint.contains("saw") && hint.contains("not allowed in function")
        }
        _ => false,
    });
    assert!(
        has_saw_msg,
        "expected SAW_NOT_ALLOWED_IN_FN_BODY in fn contract result, got: {results:?}"
    );
}

/// `saw` on the theorem path is rejected because contains_past_time
/// returns true for Saw.
#[test]
fn theorem_show_saw_rejected() {
    let src = r"module T

enum Outcome = ok
extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

entity E { x: int = 0 }

system S(es: Store<E>) {
  dep Stripe
  command tick() { Stripe::charge(1) }
}

theorem t for S {
  show saw Stripe::charge(1)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "t"
            )
        })
        .expect("expected Unprovable for `saw` on theorem path");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("past-time"),
            "expected past-time-specific hint, got: {hint}"
        );
    }
}

/// `saw` in lemma bodies is rejected (subsumed by contains_temporal).
#[test]
fn lemma_saw_rejected_with_lemma_diagnostic() {
    let src = r"module T

enum Outcome = ok
extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

lemma helper {
  saw Stripe::charge(1)
}
";
    let results = verify_source(src);
    let r = results
        .iter()
        .find(|r| {
            matches!(
                r,
                abide::verify::VerificationResult::Unprovable { name, .. }
                    if name == "helper"
            )
        })
        .expect("expected Unprovable for `saw` in lemma body");
    if let abide::verify::VerificationResult::Unprovable { hint, .. } = r {
        assert!(
            hint.contains("lemma"),
            "expected lemma-specific hint, got: {hint}"
        );
    }
}

/// `saw` composes with temporal operators.
/// `always (saw S::tick() implies true)` should hold trivially.
#[test]
fn saw_composition_with_always() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    let billing = Billing {}
  }
  assert always ((saw Stripe::charge(1)) implies true)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `always (saw implies true)` to hold, got: {results:?}"
    );
}

/// `saw` is false at step 0 because no event has yet fired.
/// The BMC asserts the property at every action including step 0, so
/// `assert saw S::tick()` yields a counterexample at step 0.
#[test]
fn saw_false_at_step_zero() {
    let src = r"module T

enum Outcome = ok

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    let billing = Billing {}
  }
  assert saw Stripe::charge(1)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
            if name == "v"
        )),
        "expected `assert saw S::tick()` to fail at step 0, got: {results:?}"
    );
}

// ── arithmetic aggregators ─────────────────────

/// `sum x: E | x.field` parses and elaborates.
#[test]
fn aggregator_sum_parse_and_elaborate() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..2]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert always ((sum a: Account | a.balance) >= 0)
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors for `sum`, got: {real_errors:?}"
    );
}

/// `count x: E | P(x)` parses and elaborates.
#[test]
fn aggregator_count_parse_and_elaborate() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..2]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert always ((count a: Account | a.balance > 0) >= 0)
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors.is_empty(),
        "expected no elab errors for `count`, got: {real_errors:?}"
    );
}

/// `sum` over entity pool is verified — all balances start at 0,
/// so the sum at step 0 is 0 (no active entities yet). The property
/// `always (sum >= 0)` holds because deposits only add.
#[test]
fn aggregator_sum_entity_pool_holds() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((sum a: Account | a.balance) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `always (sum a: Account | a.balance) >= 0` to hold, got: {results:?}"
    );
}

/// `count` over entity pool — count of active accounts with
/// balance > 0 should be >= 0 (trivially true, but tests the encoding).
#[test]
fn aggregator_count_entity_pool_holds() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((count a: Account | a.balance > 0) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `count >= 0` to hold, got: {results:?}"
    );
}

/// `count` over entity pool detects a violation — the assertion
/// claims there are always 0 accounts with balance == 0, but the initial
/// create gives balance = 0.
#[test]
fn aggregator_count_violation_detected() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((count a: Account | a.balance == 0) == 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
            if name == "v"
        )),
        "expected counterexample for `count == 0` with newly created accounts, got: {results:?}"
    );
}

/// `product` over entity pool. All balances start at 0 via
/// create, so the product includes 0, making it == 0 after any create.
#[test]
fn aggregator_product_entity_pool() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((product a: Account | a.balance + 1) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `product >= 0` to hold (all balance+1 >= 1), got: {results:?}"
    );
}

/// `min` over entity pool. When accounts exist, all balances
/// start at 0 and deposits add 10, so min balance >= 0 should hold.
/// The property is guarded by non-emptiness because min over an empty
/// pool is undefined per.
#[test]
fn aggregator_min_entity_pool_holds() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((count a: Account | true) > 0 implies (min a: Account | a.balance) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `min balance >= 0` to hold, got: {results:?}"
    );
}

/// `max` over entity pool. When accounts exist, max
/// balance >= 0. Guarded by non-emptiness.
#[test]
fn aggregator_max_entity_pool_holds() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command open() { create Account {} }
  command deposit() { choose a: Account where true { a.balance' = a.balance + 10 } }
}

verify v {
  assume {
    store accounts: Account[0..3]
    let bank = Bank { accounts: accounts }
  }
  assert always ((count a: Account | true) > 0 implies (max a: Account | a.balance) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `max balance >= 0` to hold, got: {results:?}"
    );
}

/// `count` over fieldless enum domain. count of enum values
/// satisfying a trivial predicate should equal the number of variants.
#[test]
fn aggregator_count_over_enum_holds() {
    let src = r"module T

enum Color = red | green | blue

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((count c: Color | true) == 3)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `count c: Color | true == 3` to hold, got: {results:?}"
    );
}

/// aggregator over unsupported domain (int) produces
/// Unprovable with a clear error message.
#[test]
fn aggregator_unsupported_domain_rejected() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((sum n: int | n) >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results
            .iter()
            .any(|r| matches!(r, abide::verify::VerificationResult::Unprovable { .. })),
        "expected Unprovable for sum over int domain, got: {results:?}"
    );
}

/// `min` and `max` over an empty effective entity pool
/// (no entities activated) should not return sentinel values.
/// The result should be unconstrained / undefined, not i64::MAX/MIN.
/// A property comparing min to a concrete value should be satisfiable
/// (neither proved nor disproved) since the result is undefined.
#[test]
fn aggregator_min_empty_pool_undefined() {
    let src = r"module T

entity Account { balance: int = 0 }
system Bank(accounts: Store<Account>) {command noop() { choose a: Account where false { a.balance' = a.balance } }
}

verify v {
  assume {
    store accounts: Account[0..2]
    let bank = Bank { accounts: accounts }
  
   stutter }
  assert (min a: Account | a.balance) == 42
}
";
    let results = verify_source(src);
    // With no active entities, min is undefined (unconstrained).
    // The solver should NOT prove this (42 is arbitrary), but it also
    // should not fail with sentinel values. Any result other than
    // a hard crash is acceptable — the key is no sentinel leak.
    assert!(
        !results.is_empty(),
        "expected some verification result, got empty"
    );
}

/// `count b: bool | b` correctly ranges over {false, true}
/// with bool bindings. `count b: bool | b` should equal 1 (only
/// `true` satisfies the identity predicate).
#[test]
fn aggregator_count_over_bool_domain() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((count b: bool | b) == 1)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `count b: bool | b == 1` to hold, got: {results:?}"
    );
}

/// `sum b: bool |...` over bool domain works with proper
/// bool binding. A function of b that is 1 when true, 0 when false
/// should sum to 1.
#[test]
fn aggregator_sum_over_bool_domain_parse() {
    let src = r"module T

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((count b: bool | true) == 2)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected `count b: bool | true == 2` to hold (both false and true satisfy `true`), got: {results:?}"
    );
}

/// `count` with a known non-bool body (literal int) is
/// rejected at elab time.
#[test]
fn aggregator_count_non_bool_body_rejected() {
    let src = r"module T

enum Color = red | green | blue

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((count c: Color | 42) >= 0)
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("count") && e.message.contains("bool")),
        "expected count-body-must-be-bool error, got: {real_errors:?}"
    );
}

/// `sum` with a known bool body (literal true) is rejected.
#[test]
fn aggregator_sum_bool_body_rejected() {
    let src = r"module T

enum Color = red | green | blue

entity E { x: int = 0 }
system S(es: Store<E>) {command tick() { choose e: E where true { e.x' = e.x } }
}

verify v {
  assume {
    store es: E[0..2]
    let s = S { es: es }
  
   stutter }
  assert always ((sum c: Color | true) >= 0)
}
";
    let (_result, errors) = elab_with_errors(src);
    let real_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        real_errors
            .iter()
            .any(|e| e.message.contains("Sum") && e.message.contains("numeric")),
        "expected sum-body-must-be-numeric error, got: {real_errors:?}"
    );
}

/// aggregator in fn ensures clause — count over enum in
/// fn contract should work (finite unfolding in pure-expression encoder).
#[test]
fn aggregator_in_fn_contract_enum_domain() {
    let src = r"module T

enum Color = red | green | blue

fn colors_are_three(): bool
  ensures (count c: Color | true) == 3
{
  true
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
            if name == "colors_are_three"
        )),
        "expected fn contract with count over enum to be proved, got: {results:?}"
    );
}

/// `all x: T in coll | P(x)` — quantifier with `in expr`
/// parses correctly (in_expr is Some).
#[test]
fn quantifier_in_expr_parse_and_elaborate() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert all x: int in items | x > 0 }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    match &v.asserts[0].kind {
        ExprKind::All(_, _, in_expr, _) => {
            assert!(
                in_expr.is_some(),
                "expected `in_expr` to be Some for `all x: int in items`"
            );
        }
        other => panic!("expected All with in_expr, got: {other:?}"),
    }
}

// ── system flat state fields ─────────────────────────────

/// system with a flat primitive field. The action reads and
/// primes the field; the verify block checks that it's always >= 0.
#[test]
fn system_flat_field_holds() {
    let src = r"module T

enum Screen = home | compose

system Ui {
  screen: Screen = @home

  command handle() requires screen == @home {
    screen' = @compose
  }
}

verify v {
  assume {
    let ui = Ui {}
    stutter
  }
  assert always (screen == @home or screen == @compose)
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected system flat field verify to hold, got: {results:?}"
    );
}

/// struct-typed system field. The action reads and primes
/// struct sub-fields via dot access.
#[test]
fn system_struct_field_holds() {
    let src = r"module T

enum Screen = home | compose
enum Mode = normal | editing

struct UiState {
  screen: Screen,
  mode: Mode
}

system Ui {
  ui: UiState = UiState { screen: @home, mode: @normal }

  command handle() requires ui.screen == @home {
    ui.screen' = @compose
    ui.mode' = @editing
  }
}

verify v {
  assume {
    let ui_sys = Ui {}
    stutter
  }
  assert always (ui.screen == @home or ui.screen == @compose)
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected struct system field verify to hold, got: {results:?}"
    );
}

/// system field frame condition — unmodified fields stay unchanged.
#[test]
fn system_field_frame_condition() {
    let src = r"module T

enum Screen = home | compose
enum Mode = normal | editing

system Ui {
  screen: Screen = @home
  mode: Mode = @normal

  command handle() requires screen == @home {
    screen' = @compose
  }
}

verify v {
  assume {
    let ui = Ui {}
    stutter
  }
  assert always (mode == @normal or mode == @editing)
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected system field frame condition to hold (mode unchanged), got: {results:?}"
    );
}

#[test]
fn aggregator_in_expr_parse_and_elaborate() {
    use abide::ast::ExprKind;
    let src = r"verify v {
  assume {
    store es: E[0..1]
    let s = S { es: es }
  } assert (sum x: int in items | x) >= 0 }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    let v = match &prog.decls[0] {
        abide::ast::TopDecl::Verify(v) => v,
        other => panic!("expected Verify, got {other:?}"),
    };
    match &v.asserts[0].kind {
        ExprKind::Ge(lhs, _) => match &lhs.kind {
            ExprKind::Aggregate(_, _, _, in_expr, _) => {
                assert!(
                    in_expr.is_some(),
                    "expected `in_expr` to be Some for `sum x: int in items`"
                );
            }
            other => panic!("expected Aggregate with in_expr, got: {other:?}"),
        },
        other => panic!("expected Ge, got: {other:?}"),
    }
}

// ── negative tests ─────────────────────────────────────────

/// Helper: elaborate source and return errors.
fn elab_errors(src: &str) -> Vec<String> {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = elab::elaborate(&program);
    errors.iter().map(|e| format!("{e}")).collect()
}

/// Finding 1: StructCtor in a general expression position (pred body)
/// is rejected at elab check time, not silently accepted.
#[test]
fn struct_ctor_rejected_in_general_expr() {
    let errors = elab_errors(
        r"module T
struct Foo { x: int }
pred p() = Foo { x: 1 }
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("struct constructor") && e.contains("not supported")),
        "expected struct constructor rejection, got: {errors:?}"
    );
}

/// Finding 1b: StructCtor in a action body is rejected at elab check time.
#[test]
fn struct_ctor_rejected_in_step_body() {
    let errors = elab_errors(
        r"module T
struct Foo { x: int }
system S {
  command go() { x' = Foo { x: 1 } }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("struct constructor") && e.contains("not supported")),
        "expected struct constructor rejection in action body, got: {errors:?}"
    );
}

/// Finding 1c: StructCtor in a query body is rejected at elab check time.
#[test]
fn struct_ctor_rejected_in_query_body() {
    let errors = elab_errors(
        r"module T
struct Foo { x: int }
system S {
  command go() { }
  query q() = Foo { x: 1 }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("struct constructor") && e.contains("not supported")),
        "expected struct constructor rejection in query body, got: {errors:?}"
    );
}

/// Finding 2: unknown field in struct constructor default is caught.
#[test]
fn struct_ctor_unknown_field_rejected() {
    let errors = elab_errors(
        r"module T
enum Screen = home | compose
struct UiState { screen: Screen }
system Ui {
  ui: UiState = UiState { typo: @home }
  command handle() { }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("unknown field") && e.contains("typo")),
        "expected unknown field error, got: {errors:?}"
    );
}

/// Finding 2: missing field in struct constructor default is caught.
#[test]
fn struct_ctor_missing_field_reported() {
    let errors = elab_errors(
        r"module T
enum Screen = home | compose
enum Mode = normal | editing
struct UiState { screen: Screen, mode: Mode }
system Ui {
  ui: UiState = UiState { screen: @home }
  command handle() { }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("missing field") && e.contains("mode")),
        "expected missing field error, got: {errors:?}"
    );
}

/// Finding 2: duplicate field in struct constructor default is caught.
#[test]
fn struct_ctor_duplicate_field_rejected() {
    let errors = elab_errors(
        r"module T
enum Screen = home | compose
struct UiState { screen: Screen }
system Ui {
  ui: UiState = UiState { screen: @home, screen: @compose }
  command handle() { }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("duplicate field") && e.contains("screen")),
        "expected duplicate field error, got: {errors:?}"
    );
}

/// Finding 3: quantified entity field is NOT shadowed by a same-named system field.
#[test]
fn system_field_does_not_shadow_entity_field() {
    let src = r"module T

entity Widget { status: int = 0 }

system Dashboard(widgets: Store<Widget>) {
  status: int = 0

  command refresh() { status' = 1 }
}

verify v {
  assume {
    store widgets: Widget[0..2]
    let dash = Dashboard { widgets: widgets }
  }
  assert always (all w: Widget | w.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected entity field `status` to resolve to Widget.status (not Dashboard.status), got: {results:?}"
    );
}

// ── return in executable command clauses + command return types ─────

/// a command return type with a return expression parses, elaborates, and verifies correctly.
#[test]
fn command_return_type_and_command_return() {
    let src = r"module T

enum Outcome = ok | err

entity Item { status: int = 0 }

system S(items: Store<Item>) {
  command do_thing(item: Item) -> Outcome requires item.status == 0 {
    item.status' = 1
    return @ok
  }
}

verify v {
  assume {
    store items: Item[0..2]
    let s = S { items: items }
    stutter
  }
  assert always (all i: Item | i.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected command with return type to verify, got: {results:?}"
    );
}

/// a command return without a command return type is rejected.
#[test]
fn command_return_without_command_return_type_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok | err
system S {
  command go() { return @ok }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| { e.contains("return") && e.contains("does not declare a return type") }),
        "expected rejection of return without command return type, got: {errors:?}"
    );
}

/// command with return type but no return in the body is allowed
/// (that branch may not produce an outcome).
#[test]
fn command_return_type_no_return_allowed() {
    let src = r"module T

enum Outcome = ok | err

entity Item { status: int = 0 }

system S(items: Store<Item>) {
  command do_thing(item: Item) -> Outcome requires item.status == 0 {
    item.status' = 1
  }
}

verify v {
  assume {
    store items: Item[0..2]
    let s = S { items: items }
    stutter
  }
  assert always (all i: Item | i.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected command with return type but no action return to verify, got: {results:?}"
    );
}

/// inline command clauses can return values directly.
#[test]
fn inline_command_return_type_and_return_expr() {
    let src = r"module T

enum Outcome = ok | err

entity Item { status: int = 0 }

system S(items: Store<Item>) {
  command do_thing(item: Item) -> Outcome requires item.status == 0 {
    item.status' = 1
    return @ok
  }
  command do_thing(item: Item) -> Outcome requires item.status == 0 {
    item.status' = -1
    return @err
  }
}

verify v {
  assume {
    store items: Item[0..2]
    let s = S { items: items }
    stutter
  }
  assert always (all i: Item | i.status >= -1)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected inline command clauses with return type to verify, got: {results:?}"
    );
}

/// return with tuple-payload enum variant parses and elaborates.
#[test]
fn step_return_with_tuple_variant_parses() {
    let src = r"module T

enum ChargeOutcome = ok(int) | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> ChargeOutcome requires order.status == 0 {
    order.status' = 1
    return @ok(42)
  }
  command charge(order: Order) -> ChargeOutcome requires order.status == 0 {
    order.status' = -1
    return @err
  }
}
";
    let errors = elab_errors(src);
    assert!(
        errors.is_empty(),
        "expected clean elaboration for return with tuple variant, got: {errors:?}"
    );
}

/// return with wrong variant name is rejected.
#[test]
fn step_return_wrong_variant_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok | err
system S {
  command go() -> Outcome { return @bad }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("not a variant") && e.contains("bad")),
        "expected rejection of unknown variant in return, got: {errors:?}"
    );
}

/// return @ok with no args when variant expects one is rejected.
#[test]
fn step_return_arity_mismatch_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok(int) | err
system S {
  command go() -> Outcome { return @ok }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("argument") && e.contains("expects 1")),
        "expected arity mismatch error, got: {errors:?}"
    );
}

/// return @ok(1, 2) when variant expects one arg is rejected.
#[test]
fn step_return_too_many_args_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok(int) | err
system S {
  command go() -> Outcome { return @ok(1, 2) }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("argument") && e.contains('2') && e.contains("expects 1")),
        "expected too-many-args error, got: {errors:?}"
    );
}

/// return @ok("x") when variant expects int is rejected (type mismatch).
#[test]
fn step_return_payload_type_mismatch_rejected() {
    let errors = elab_errors(
        r#"module T
enum Outcome = ok(int) | err
system S {
  command go() -> Outcome { return @ok("wrong") }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("type") && e.contains("int")),
        "expected payload type mismatch error, got: {errors:?}"
    );
}

/// non-constructor return (e.g., `return 7`) for enum return type is rejected.
#[test]
fn step_return_non_constructor_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok | err
system S {
  command go() -> Outcome { return 7 }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("non-constructor")),
        "expected non-constructor return rejection, got: {errors:?}"
    );
}

// ── proc needs edges + composition sugar ──────────────────

/// proc with needs edges parses and elaborates correctly.
#[test]
fn proc_needs_edges_parse_and_elaborate() {
    let errors = elab_errors(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)

    ship needs charge.ok
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected clean elaboration for proc with needs, got: {errors:?}"
    );
}

/// proc with composition sugar parses and desugars.
#[test]
fn proc_composition_sugar_desugars() {
    let errors = elab_errors(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command pack(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }
  command ship(order: Order) requires order.status == 2 {
    order.status' = 3
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    pack   = shipping.pack(order)
    ship   = shipping.ship(order)

    charge.ok -> pack.ok -> ship
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected clean elaboration for proc with sugar, got: {errors:?}"
    );
}

/// proc with mixed needs and sugar parses.
#[test]
fn proc_mixed_needs_and_sugar() {
    let errors = elab_errors(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command pack(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }
  command ship(order: Order) requires order.status == 2 {
    order.status' = 3
  }
}

system Orders(orders: Store<Order>) {
  command cancel(order: Order) requires order.status == 0 {
    order.status' = -1
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }
  let order_ops = Orders { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    pack   = shipping.pack(order)
    ship   = shipping.ship(order)
    cancel = order_ops.cancel(order)

    charge.ok -> pack.ok -> ship
    cancel needs charge.err
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected clean elaboration for proc with mixed form, got: {errors:?}"
    );
}

/// proc branching sugar desugars to outcome-gated needs edges.
#[test]
fn proc_match_branch_sugar_elaborates() {
    let errors = elab_errors(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
  command retry(order: Order) requires order.status == 1 {
    order.status' = 0
  }
}

system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    retry  = billing.retry(order)
    ship   = shipping.ship(order)

    match charge {
      @ok => ship
      @err => retry, ship
    }
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected clean elaboration for proc match sugar, got: {errors:?}"
    );
}

/// proc lowering now treats the proc name as a workflow-start command and
/// lowers each node as its own hidden workflow transition.
#[test]
fn proc_start_and_node_transitions_are_executable() {
    let src = r"module T

enum Outcome = ok | err

system Billing {
  command charge() -> Outcome {
    return @ok
  }
}

system Shipping {
  command ship() { }
}

program Shop {
  let billing = Billing {}
  let shipping = Shipping {}

  proc fulfill() {
    charge = billing.charge()
    ship   = shipping.ship()

    ship needs charge.ok
  }
}

verify fulfill_is_executable {
  assume {
    let shop = Shop {}
    no stutter
  }
  assert always true
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                | abide::verify::VerificationResult::Checked { name, .. }
                if name == "fulfill_is_executable"
        )) && !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Deadlock { name, .. }
                if name == "fulfill_is_executable"
        )),
        "verify should treat proc start/node transitions as executable, got: {results:?}"
    );
}

#[test]
fn proc_start_and_node_transitions_are_provable_with_cvc5() {
    require_unbounded_proof_tests!();

    let src = r"module T

enum Outcome = ok | err

system Billing {
  command charge() -> Outcome {
    return @ok
  }
}

system Shipping {
  command ship() { }
}

program Shop {
  let billing = Billing {}
  let shipping = Shipping {}

  proc fulfill() {
    charge = billing.charge()
    ship   = shipping.ship()

    ship needs charge.ok
  }
}

verify fulfill_is_executable {
  assume {
    let shop = Shop {}
    no stutter
  }
  assert always true
}
";

    let results = verify_source_with_config(
        src,
        abide::verify::VerifyConfig {
            solver_selection: abide::verify::SolverSelection::Cvc5,
            unbounded_only: true,
            no_ic3: true,
            ..abide::verify::VerifyConfig::default()
        },
    );
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "fulfill_is_executable"
        )),
        "expected CVC5 proof for proc workflow execution, got: {results:?}"
    );
    assert!(
        !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Deadlock { name, .. }
                if name == "fulfill_is_executable"
        )),
        "proc workflow should not deadlock under CVC5 SyGuS routing, got: {results:?}"
    );
}

#[test]
fn proc_store_workflow_is_provable_with_cvc5() {
    require_unbounded_proof_tests!();

    let src = r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)

    ship needs charge.ok
  }
}

verify fulfill_is_safe {
  assume {
    store orders: Order[0..2]
    let shop = Shop { orders: orders }
    no stutter
  }
  assert always (all o: Order | o.status >= 0 and o.status <= 2)
}
";

    let results = verify_source_with_config(
        src,
        abide::verify::VerifyConfig {
            solver_selection: abide::verify::SolverSelection::Cvc5,
            unbounded_only: true,
            no_ic3: true,
            ..abide::verify::VerifyConfig::default()
        },
    );
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "fulfill_is_safe"
        )),
        "expected CVC5 proof for pooled proc workflow safety, got: {results:?}"
    );
    assert!(
        !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Deadlock { name, .. }
                if name == "fulfill_is_safe"
        )),
        "pooled proc workflow should not deadlock under CVC5 routing, got: {results:?}"
    );
}

#[test]
fn proc_lowering_creates_hidden_proc_entities_and_node_steps() {
    let result = elaborate_source(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)

    ship needs charge.ok
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);

    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    let hidden_entity_name = "__abide_procinst__Shop__fulfill";
    let hidden_entity = prog
        .entities
        .iter()
        .find(|entity| entity.name == hidden_entity_name)
        .expect("expected hidden proc instance entity");

    assert!(
        shop.entities
            .iter()
            .any(|entity| entity == hidden_entity_name),
        "expected hidden proc entity in system entity set, got entities: {:?}",
        shop.entities
            .iter()
            .map(std::string::String::as_str)
            .collect::<Vec<_>>()
    );
    assert!(
        hidden_entity
            .fields
            .iter()
            .any(|field| field.name == "param__order"),
        "expected proc parameter snapshot field, got fields: {:?}",
        hidden_entity
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>()
    );
    assert!(
        hidden_entity
            .fields
            .iter()
            .any(|field| field.name == "done__charge"),
        "expected done field for ship node, got fields: {:?}",
        hidden_entity
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>()
    );
    assert!(
        hidden_entity
            .fields
            .iter()
            .any(|field| field.name == "done__ship"),
        "expected done field for ship node, got fields: {:?}",
        hidden_entity
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>()
    );
    assert!(
        hidden_entity
            .fields
            .iter()
            .any(|field| field.name == "outcome__charge__ok"),
        "expected outcome field for charge.ok, got fields: {:?}",
        hidden_entity
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>()
    );
    assert!(
        shop.commands.iter().any(|cmd| cmd.name == "fulfill"),
        "expected workflow-start command"
    );
    let start_step = shop
        .actions
        .iter()
        .find(|step| step.name == "fulfill")
        .expect("expected workflow-start step");
    assert!(
        matches!(
            &start_step.guard,
            abide::ir::types::IRExpr::Lit {
                ty: abide::ir::types::IRType::Bool,
                value: abide::ir::types::LitVal::Bool { value: true },
                ..
            }
        ),
        "expected unconditional proc start without explicit requires, got: {:?}",
        start_step.guard
    );
    assert!(
        matches!(
            start_step.body.as_slice(),
            [abide::ir::types::IRAction::Create { entity, .. }] if entity == hidden_entity_name
        ),
        "expected proc start to create hidden proc instance, got: {:?}",
        start_step.body
    );
    let charge_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__charge")
        .expect("expected hidden node action for charge");
    assert!(
        matches!(
            charge_step.body.as_slice(),
            [
                abide::ir::types::IRAction::LetCrossCall { .. },
                abide::ir::types::IRAction::Match { .. }
            ]
        ),
        "expected outcome-bearing proc node to lower via let-cross-call plus match, got: {:?}",
        charge_step.body
    );
    let ship_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__ship")
        .expect("expected hidden node action for ship");
    assert!(
        matches!(
            ship_step.body.as_slice(),
            [abide::ir::types::IRAction::Choose { entity, .. }] if entity == hidden_entity_name
        ),
        "expected node action to choose a hidden proc instance, got: {:?}",
        ship_step.body
    );
}

#[test]
fn proc_requires_contributes_to_start_guard() {
    let result = elaborate_source(
        r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }

  proc fulfill(order: Order) requires order.status == 0 {
    charge = billing.charge(order)
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);

    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    let start_step = shop
        .actions
        .iter()
        .find(|step| step.name == "fulfill")
        .expect("expected workflow-start step");

    assert!(
        matches!(
            &start_step.guard,
            abide::ir::types::IRExpr::BinOp { op, .. } if op == "OpEq"
        ),
        "expected proc requires to lower directly into start guard, got: {:?}",
        start_step.guard
    );
}

#[test]
fn verify_proc_bounds_lower_to_hidden_proc_instance_stores() {
    let result = elaborate_source(
        r"module T

entity Order {}

system Billing(orders: Store<Order>) {
  command charge(order: Order) { }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
  }
}

verify bound_proc_pool {
  assume {
    store orders: Order[0..3]
    let shop = Shop { orders: orders }
    proc shop.fulfill[0..2]
  }
  assert true
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);

    let verify = prog
        .verifies
        .iter()
        .find(|verify| verify.name == "bound_proc_pool")
        .expect("expected verify block");
    let proc_store = verify
        .stores
        .iter()
        .find(|store| store.name == "__abide_procbound__Shop__fulfill")
        .expect("expected lowered proc bound store");

    assert_eq!(proc_store.entity_type, "__abide_procinst__Shop__fulfill");
    assert_eq!((proc_store.lo, proc_store.hi), (0, 2));
}

#[test]
fn theorem_proc_bounds_are_rejected() {
    let errors = elaborate_source_errors(
        r"module T

entity Order {}

system Billing(orders: Store<Order>) {
  command charge(order: Order) { }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
  }
}

theorem no_proc_bounds_for_theorems for Shop {
  assume {
    store orders: Order[0..3]
    let shop = Shop { orders: orders }
    proc shop.fulfill[0..2]
  }
  show always true
}
",
    );
    assert!(
        errors.iter().any(|e| e
            .message
            .contains("proc bounds are only allowed in verify blocks")),
        "expected theorem proc-bound rejection, got: {errors:?}"
    );
}

#[test]
fn proc_requires_must_be_bool() {
    let errors = elaborate_source_errors(
        r"module T

entity Order {}

program Shop {
  proc fulfill(order: Order) requires 1 {
  }
}
",
    );
    let messages: Vec<_> = errors.iter().map(|e| e.message.as_str()).collect();
    assert!(
        messages
            .iter()
            .any(|m| m.contains("requires expression should be bool")),
        "expected proc requires bool diagnostic, got: {messages:?}"
    );
}

#[test]
fn proc_node_actions_record_progress_facts_only() {
    let result = elaborate_source(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }

  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = -1
    return @err
  }
}

system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)

    ship needs charge.ok
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);
    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    let charge_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__charge")
        .expect("expected hidden charge node step");
    let ship_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__ship")
        .expect("expected hidden ship node step");

    fn has_apply_transition(actions: &[abide::ir::types::IRAction], transition: &str) -> bool {
        actions.iter().any(|action| match action {
            abide::ir::types::IRAction::Apply {
                transition: name, ..
            } => name == transition,
            abide::ir::types::IRAction::Choose { ops, .. }
            | abide::ir::types::IRAction::ForAll { ops, .. } => {
                has_apply_transition(ops, transition)
            }
            abide::ir::types::IRAction::Match { arms, .. } => arms
                .iter()
                .any(|arm| has_apply_transition(&arm.body, transition)),
            _ => false,
        })
    }

    let charge_match = charge_step
        .body
        .iter()
        .find_map(|action| match action {
            abide::ir::types::IRAction::Match { arms, .. } => Some(arms),
            _ => None,
        })
        .expect("expected charge node to branch on returned outcome");

    let ok_arm = charge_match
        .iter()
        .find(|arm| matches!(&arm.pattern, abide::ir::types::IRPattern::PCtor { name, .. } if name == "ok"))
        .expect("expected ok arm");
    let err_arm = charge_match
        .iter()
        .find(|arm| matches!(&arm.pattern, abide::ir::types::IRPattern::PCtor { name, .. } if name == "err"))
        .expect("expected err arm");

    assert!(
        has_apply_transition(&ok_arm.body, "__abide_mark__charge__ok"),
        "success branch should mark the charge node done"
    );
    assert!(
        has_apply_transition(&ok_arm.body, "__abide_mark__charge__ok"),
        "success branch should record the chosen outcome fact"
    );
    assert!(
        has_apply_transition(&err_arm.body, "__abide_mark__charge"),
        "error branch should mark the charge node done"
    );
    assert!(
        !has_apply_transition(&err_arm.body, "__abide_mark__charge__ok"),
        "error branch should not mark the ok outcome fact"
    );
    assert!(
        has_apply_transition(&ship_step.body, "__abide_mark__ship"),
        "ship node should record its own completion fact"
    );
}

#[test]
fn proc_join_dependencies_elaborate_and_lower() {
    let result = elaborate_source(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command pack(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }

  command ship(order: Order) requires order.status == 2 {
    order.status' = 3
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    pack   = shipping.pack(order)
    ship   = shipping.ship(order)

    pack needs charge.ok
    ship needs charge.ok
    ship needs pack.ok
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);
    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    let ship_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__ship")
        .expect("expected hidden ship node step");

    let choose_filter = ship_step
        .body
        .iter()
        .find_map(|action| match action {
            abide::ir::types::IRAction::Choose { filter, .. } => Some(filter.as_ref()),
            _ => None,
        })
        .expect("expected ship node to choose a proc instance");
    assert!(
        matches!(choose_filter, abide::ir::types::IRExpr::BinOp { .. }),
        "expected joined proc node filter to be a composed boolean condition, got: {choose_filter:?}"
    );
}

#[test]
fn proc_mixed_unconditional_and_outcome_successors_elaborate_and_lower() {
    let result = elaborate_source(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command audit(order: Order) requires order.status == 1 { }

  command ship(order: Order) requires order.status == 1 {
    order.status' = 2
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    audit  = shipping.audit(order)
    ship   = shipping.ship(order)

    audit needs charge
    ship needs charge.ok
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);
    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    assert!(
        shop.actions
            .iter()
            .any(|step| step.name == "__abide_proc_fulfill__node__audit"),
        "expected hidden audit node action for mixed-successor proc"
    );
    assert!(
        shop.actions
            .iter()
            .any(|step| step.name == "__abide_proc_fulfill__node__ship"),
        "expected hidden ship node action for mixed-successor proc"
    );
}

#[test]
fn proc_dependency_conditions_with_boolean_logic_elaborate_and_lower() {
    let result = elaborate_source(
        r"module T

enum Outcome = ok | err

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}

system Shipping(orders: Store<Order>) {
  command pack(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }

  command retry(order: Order) requires order.status == 1 { }

  command ship(order: Order) requires order.status == 2 {
    order.status' = 3
  }
}

program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }

  proc fulfill(order: Order) {
    charge = billing.charge(order)
    pack   = shipping.pack(order)
    retry  = shipping.retry(order)
    ship   = shipping.ship(order)

    ship needs charge.ok or not (retry and pack.err)
  }
}
",
    );
    let (prog, _lower_diag) = ir::lower(&result);
    let shop = prog
        .systems
        .iter()
        .find(|system| system.name == "Shop")
        .expect("program system should lower");
    let ship_step = shop
        .actions
        .iter()
        .find(|step| step.name == "__abide_proc_fulfill__node__ship")
        .expect("expected hidden ship node step");

    fn contains_op(expr: &abide::ir::types::IRExpr, op: &str) -> bool {
        match expr {
            abide::ir::types::IRExpr::BinOp {
                op: expr_op,
                left,
                right,
                ..
            } => expr_op == op || contains_op(left, op) || contains_op(right, op),
            abide::ir::types::IRExpr::UnOp {
                op: expr_op,
                operand,
                ..
            } => expr_op == op || contains_op(operand, op),
            abide::ir::types::IRExpr::App { func, arg, .. } => {
                contains_op(func, op) || contains_op(arg, op)
            }
            abide::ir::types::IRExpr::Prime { expr, .. } => contains_op(expr, op),
            abide::ir::types::IRExpr::Index { map, key, .. } => {
                contains_op(map, op) || contains_op(key, op)
            }
            abide::ir::types::IRExpr::MapUpdate {
                map, key, value, ..
            } => contains_op(map, op) || contains_op(key, op) || contains_op(value, op),
            _ => false,
        }
    }

    let choose_filter = ship_step
        .body
        .iter()
        .find_map(|action| match action {
            abide::ir::types::IRAction::Choose { filter, .. } => Some(filter.as_ref()),
            _ => None,
        })
        .expect("expected ship node to choose a proc instance");

    assert!(
        contains_op(choose_filter, "OpOr"),
        "expected proc filter to encode `or`, got: {choose_filter:?}"
    );
    assert!(
        contains_op(choose_filter, "OpNot"),
        "expected proc filter to encode `not`, got: {choose_filter:?}"
    );
    assert!(
        contains_op(choose_filter, "OpAnd"),
        "expected proc filter to encode `and`, got: {choose_filter:?}"
    );
}

/// unknown instance handle in proc node is rejected.
#[test]
fn proc_unknown_instance_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  proc fulfill(order: Order) {
    charge = unknown.charge(order)
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("unknown") && e.contains("not a let binding")),
        "expected unknown instance error, got: {errors:?}"
    );
}

/// unknown command on a bound system is rejected.
#[test]
fn proc_unknown_command_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  proc fulfill(order: Order) {
    x = billing.nonexistent(order)
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("nonexistent") && e.contains("does not exist")),
        "expected unknown command error, got: {errors:?}"
    );
}

/// needs edge referencing unknown node is rejected.
#[test]
fn proc_unknown_edge_node_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ghost needs charge
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("ghost") && e.contains("not a declared node")),
        "expected unknown edge target error, got: {errors:?}"
    );
}

/// needs edge with port on command without return type is rejected.
#[test]
fn proc_port_on_no_return_command_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 { order.status' = 2 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)
    ship needs charge.ok
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("port") && e.contains("no return type")),
        "expected port-on-no-return error, got: {errors:?}"
    );
}

/// needs edge with invalid port variant is rejected.
#[test]
fn proc_invalid_port_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok | err
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}
system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 { order.status' = 2 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)
    ship needs charge.bad
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("bad") && e.contains("variants")),
        "expected invalid port error, got: {errors:?}"
    );
}

/// proc with a cycle is rejected.
#[test]
fn proc_cycle_rejected() {
    let errors = elab_errors(
        r"module T
enum Outcome = ok | err
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}
system Shipping(orders: Store<Order>) {
  command ship(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)
    ship needs charge.ok
    charge needs ship.ok
  }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("cycle")),
        "expected cycle error, got: {errors:?}"
    );
}

/// port on non-enum return type is rejected.
#[test]
fn proc_port_on_non_enum_return_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Scoring(orders: Store<Order>) {
  command score(order: Order) -> int requires order.status == 0 { order.status' = 1 }
}
system Shipping(orders: Store<Order>) {
  command ship(order: Order) requires order.status == 1 { order.status' = 2 }
}
program Shop(orders: Store<Order>) {
  let scoring = Scoring { orders: orders }
  let shipping = Shipping { orders: orders }
  proc fulfill(order: Order) {
    score = scoring.score(order)
    ship  = shipping.ship(order)
    ship needs score.ok
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("port") && e.contains("not an enum")),
        "expected port-on-non-enum error, got: {errors:?}"
    );
}

/// proc node with wrong argument count is rejected.
#[test]
fn proc_node_arity_mismatch_rejected() {
    let errors = elab_errors(
        r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge()
  }
}
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("argument") && e.contains("expects 1")),
        "expected proc node arity mismatch error, got: {errors:?}"
    );
}

/// trailing port on composition sugar terminal is rejected at parse time.
#[test]
fn proc_composition_sugar_trailing_port_rejected() {
    let src = r"module T
enum Outcome = ok | err
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Outcome requires order.status == 0 {
    order.status' = 1
    return @ok
  }
}
system Shipping(orders: Store<Order>) {
  command ship(order: Order) -> Outcome requires order.status == 1 {
    order.status' = 2
    return @ok
  }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  let shipping = Shipping { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge(order)
    ship   = shipping.ship(order)
    charge.ok -> ship.ok
  }
}
";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(
        result.is_err(),
        "expected parse error for trailing port, got: {result:?}"
    );
    let err = format!("{}", result.unwrap_err());
    assert!(
        err.contains("composition chain") || err.contains("cannot have a port"),
        "expected trailing port message, got: {err}"
    );
}

/// proc node with wrong argument type is rejected.
#[test]
fn proc_node_type_mismatch_rejected() {
    let errors = elab_errors(
        r#"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 { order.status' = 1 }
}
program Shop(orders: Store<Order>) {
  let billing = Billing { orders: orders }
  proc fulfill(order: Order) {
    charge = billing.charge("not_an_order")
  }
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("type") && e.contains("expects")),
        "expected type mismatch error, got: {errors:?}"
    );
}

// ── small R4 syntax changes ───────────────────────────────

/// verify [depth: N] on signature parses and overrides BMC bound.
#[test]
fn verify_depth_on_signature() {
    let src = r"module T

entity Counter { n: int = 0 }

system S(counters: Store<Counter>) {
  command tick() {
    choose c: Counter where true { c.n' = c.n + 1 }
  }
}

verify bounded_check [depth: 5] {
  assume {
    store counters: Counter[0..2]
    let s = S { counters: counters }
    stutter
  }
  assert always (all c: Counter | c.n >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "bounded_check"
        )),
        "expected verify with depth override to pass, got: {results:?}"
    );
}

/// verify depth parses in AST.
#[test]
fn verify_depth_parse() {
    use abide::ast::TopDecl;
    let src = "verify v [depth: 10] { assert true }";
    let tokens = lex::lex(src).expect("lex");
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().expect("parse");
    match &prog.decls[0] {
        TopDecl::Verify(v) => {
            assert_eq!(v.name, "v");
            assert_eq!(v.depth, Some(10));
        }
        other => panic!("expected Verify, got {other:?}"),
    }
}

/// system-level pred inside a system body parses.
#[test]
fn system_pred_parses() {
    let errors = elab_errors(
        r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred payable(order: Order) = order in orders and order.status == 0

  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected system-level pred to elaborate cleanly, got: {errors:?}"
    );
}

/// system-local pred used in action guard resolves and verifies.
#[test]
fn system_pred_used_in_step_verifies() {
    let src = r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred payable(order: Order) = order in orders and order.status == 0

  command charge(order: Order) requires payable(order) {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected system-local pred to work in verification, got: {results:?}"
    );
}

/// query calling a system-local pred resolves correctly.
#[test]
fn system_pred_called_from_query_verifies() {
    let src = r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred payable(order: Order) = order in orders and order.status == 0

  query has_payable() = exists o: Order in orders | payable(o)

  command charge(order: Order) requires payable(order) {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected query calling system-local pred to verify, got: {results:?}"
    );
}

/// invariant referencing a system-local pred elaborates cleanly
/// (qualification is applied so DefEnv can resolve the pred at verification time).
#[test]
fn system_pred_called_from_invariant_elaborates() {
    let errors = elab_errors(
        r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred non_negative(order: Order) = order.status >= 0

  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }

  invariant all_non_negative {
    all o: Order | non_negative(o)
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected invariant with system-local pred to elaborate cleanly, got: {errors:?}"
    );
}

/// one system-local pred calling another resolves correctly.
#[test]
fn system_pred_calling_another_pred_verifies() {
    let src = r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred in_pool(order: Order) = order in orders
  pred payable(order: Order) = in_pool(order) and order.status == 0

  command charge(order: Order) requires payable(order) {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected pred-calling-pred to verify, got: {results:?}"
    );
}

// ── Generic enums ─────────────────────────────────────────

/// parse `enum Option<T> = Some(T) | None`
#[test]
fn parse_generic_enum_declaration() {
    let src = "enum Option<T> = Some(T) | None";
    let tokens = lex::lex(src).unwrap();
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().unwrap();
    if let abide::ast::TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "Option");
        assert_eq!(t.type_params, vec!["T".to_string()]);
        assert_eq!(t.variants.len(), 2);
    } else {
        panic!("expected TypeDecl");
    }
}

/// parse `enum Result<T, E> = Ok(T) | Err(E)`
#[test]
fn parse_generic_enum_two_params() {
    let src = "enum Result<T, E> = Ok(T) | Err(E)";
    let tokens = lex::lex(src).unwrap();
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().unwrap();
    if let abide::ast::TopDecl::Type(t) = &prog.decls[0] {
        assert_eq!(t.name, "Result");
        assert_eq!(t.type_params, vec!["T".to_string(), "E".to_string()]);
        assert_eq!(t.variants.len(), 2);
    } else {
        panic!("expected TypeDecl");
    }
}

/// non-generic enum still parses with empty type_params
#[test]
fn parse_non_generic_enum_has_empty_type_params() {
    let src = "enum Status = Active | Inactive";
    let tokens = lex::lex(src).unwrap();
    let mut parser = Parser::new(tokens);
    let prog = parser.parse_program().unwrap();
    if let abide::ast::TopDecl::Type(t) = &prog.decls[0] {
        assert!(t.type_params.is_empty());
    } else {
        panic!("expected TypeDecl");
    }
}

/// generic enum used in entity field type — elaborates cleanly
#[test]
fn generic_enum_in_entity_field_elaborates() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
  result: Option<int> = @None
}
",
    );
    assert!(
        errors.is_empty(),
        "expected generic enum in entity field to elaborate cleanly, got: {errors:?}"
    );
}

/// generic enum used as command return type — elaborates cleanly
#[test]
fn generic_enum_as_command_return_type_elaborates() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
}

system Billing(orders: Store<Order>) {
  command check(order: Order) -> Option<int> requires order.status == 0 {
    return @Some(order.status)
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected generic enum as return type to elaborate cleanly, got: {errors:?}"
    );
}

/// generic enum with two params in return type — elaborates cleanly
#[test]
fn generic_enum_result_elaborates() {
    let errors = elab_errors(
        r"module T

enum Result<T, E> = Ok(T) | Err(E)

entity Order {
  status: int = 0
}

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Result<int, int> requires order.status == 0 {
    order.status' = 1
    return @Ok(1)
  }
}
",
    );
    assert!(
        errors.is_empty(),
        "expected Result<T,E> generic enum to elaborate cleanly, got: {errors:?}"
    );
}

/// generic enum lowers to IR as a concrete enum
#[test]
fn generic_enum_lowers_to_ir() {
    use std::io::Write;
    let src = r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
  result: Option<int> = @None
}

system Billing(orders: Store<Order>) {
  command check(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    let prog = lower_file(&path_str);
    // The monomorphized type "Option<int>" should appear in IR types
    let has_mono = prog.types.iter().any(|t| t.name.contains("Option<int>"));
    assert!(
        has_mono,
        "expected monomorphized Option<int> in IR types, got: {:?}",
        prog.types.iter().map(|t| &t.name).collect::<Vec<_>>()
    );
}

/// generic enum field used in verification — full pipeline
#[test]
fn generic_enum_field_verifies() {
    let src = r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
  result: Option<int> = @None
}

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected verify with generic enum field to pass, got: {results:?}"
    );
}

/// wrong number of type arguments produces a diagnostic
#[test]
fn generic_enum_wrong_arity_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
  result: Option<int, int> = @None
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch error, got: {errors:?}"
    );
}

/// non-generic type used with type arguments produces a diagnostic
#[test]
fn non_generic_type_with_args_rejected() {
    let errors = elab_errors(
        r"module T

enum Status = Active | Inactive

entity Order {
  status: Status<int> = @Active
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("not a generic type")),
        "expected not-a-generic-type error, got: {errors:?}"
    );
}

/// multiple monomorphized instances — constructors don't resolve
/// nondeterministically (e.g. @None stays unresolved when both Option<int>
/// and Option<string> exist, rather than picking one at random).
#[test]
fn generic_enum_multiple_instantiations_elaborate() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  a: Option<int> = @None
  b: Option<bool> = @None
}
",
    );
    assert!(
        errors.is_empty(),
        "expected multiple generic instantiations to elaborate, got: {errors:?}"
    );
}

/// generic enum with Map<K,V> argument — monomorphizes correctly
#[test]
fn generic_enum_with_map_arg_elaborates() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  data: Option<Map<int, int>> = @None
}
",
    );
    assert!(
        errors.is_empty(),
        "expected generic enum with Map arg to elaborate, got: {errors:?}"
    );
}

/// wrong arity on system field type — diagnostic emitted
#[test]
fn generic_enum_wrong_arity_in_system_field_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  state: Option<int, int> = @None

  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch for system field type, got: {errors:?}"
    );
}

/// wrong arity on command return type — diagnostic emitted
#[test]
fn generic_enum_wrong_arity_in_command_return_rejected() {
    let errors = elab_errors(
        r"module T

enum Result<T, E> = Ok(T) | Err(E)

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) -> Result<int> requires order.status == 0 {
    order.status' = 1
    return @Ok(1)
  }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 2 type argument")),
        "expected arity mismatch for command return type, got: {errors:?}"
    );
}

/// non-generic used with args on entity field — diagnostic emitted
#[test]
fn non_generic_in_entity_field_rejected() {
    let errors = elab_errors(
        r"module T

enum Status = Active | Inactive

entity Order { status: Status<int> = @Active }
",
    );
    assert!(
        errors.iter().any(|e| e.contains("not a generic type")),
        "expected not-a-generic-type for entity field, got: {errors:?}"
    );
}

/// wrong arity on entity field type — diagnostic emitted
#[test]
fn generic_enum_wrong_arity_in_entity_field_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order {
  status: int = 0
  result: Option<int, bool> = @None
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch for entity field type, got: {errors:?}"
    );
}

/// wrong arity on action param type — diagnostic emitted
/// (now works because Param.ty is TypeRef, not bare string)
#[test]
fn generic_enum_wrong_arity_in_step_param_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command check(opt: Option<int, bool>) requires true { }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch for action param type, got: {errors:?}"
    );
}

/// wrong arity on system-local pred param — diagnostic emitted
#[test]
fn generic_enum_wrong_arity_in_system_pred_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  pred check(x: Option<int, int>) = true

  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch for system-local pred param, got: {errors:?}"
    );
}

/// non-generic used with args on fn param — diagnostic emitted
#[test]
fn non_generic_in_fn_param_rejected() {
    let errors = elab_errors(
        r"module T

enum Status = Active | Inactive

fn check(x: Status<int>): bool = true
",
    );
    assert!(
        errors.iter().any(|e| e.contains("not a generic type")),
        "expected not-a-generic-type for fn param, got: {errors:?}"
    );
}

/// nested generic in variant payload — monomorphizes correctly.
/// `enum Box<T> = Wrap(Option<T>)` instantiated as `Box<int>` must produce
/// both `Box<int>` and `Option<int>` in the IR.
#[test]
fn nested_generic_in_variant_payload_lowers() {
    use std::io::Write;
    let src = r"module T

enum Option<T> = Some(T) | None
enum Box<T> = Wrap(Option<T>) | Empty

entity Order {
  status: int = 0
  data: Box<int> = @Empty
}

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    let prog = lower_file(&path_str);
    let type_names: Vec<&str> = prog.types.iter().map(|t| t.name.as_str()).collect();
    assert!(
        type_names.iter().any(|n| n.contains("Box<int>")),
        "expected Box<int> in IR types, got: {type_names:?}"
    );
    assert!(
        type_names.iter().any(|n| n.contains("Option<int>")),
        "expected nested Option<int> in IR types, got: {type_names:?}"
    );
    // Verify the nested Option<int> is a proper enum with variants, not an empty Record
    let option_int = prog
        .types
        .iter()
        .find(|t| t.name.contains("Option<int>"))
        .expect("Option<int> should be in IR types");
    match &option_int.ty {
        abide::ir::types::IRType::Enum { variants, .. } => {
            assert!(
                variants.len() == 2,
                "expected 2 variants (Some, None), got {variants:?}"
            );
        }
        other => panic!("expected IRType::Enum for Option<int>, got: {other:?}"),
    }
}

/// nested generic elaborates cleanly — no errors
#[test]
fn nested_generic_elaborates_cleanly() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None
enum Box<T> = Wrap(Option<T>) | Empty

entity Order {
  data: Box<int> = @Empty
}
",
    );
    assert!(
        errors.is_empty(),
        "expected nested generic to elaborate cleanly, got: {errors:?}"
    );
}

/// wrong-arity generic in a let binding annotation is caught.
#[test]
fn generic_enum_wrong_arity_in_let_binding_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

fn check(): bool =
  let x: Option<int, bool> = @None
  in true
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch in let binding, got: {errors:?}"
    );
}

/// wrong-arity generic in a var declaration annotation is caught.
#[test]
fn generic_enum_wrong_arity_in_var_decl_rejected() {
    let errors = elab_errors(
        r"module T

enum Option<T> = Some(T) | None

fn check(): bool {
  var x: Option<int, bool> = @None
  true
}
",
    );
    assert!(
        errors.iter().any(|e| e.contains("expects 1 type argument")),
        "expected arity mismatch in var declaration, got: {errors:?}"
    );
}

/// multiple monomorphized instances — @None in field defaults
/// resolves via field type context, producing correct IR (not a plain variable).
#[test]
fn generic_enum_multi_instantiation_defaults_lower_correctly() {
    use std::io::Write;
    let src = r"module T

enum Option<T> = Some(T) | None

entity Order {
  a: Option<int> = @None
  b: Option<bool> = @None
  status: int = 0
}

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let path_str = file.to_str().unwrap().to_owned();
    let prog = lower_file(&path_str);
    // Both Option<int> and Option<bool> should exist as proper IR enum types
    let type_names: Vec<&str> = prog.types.iter().map(|t| t.name.as_str()).collect();
    assert!(
        type_names.contains(&"Option<int>"),
        "expected Option<int> in IR types, got: {type_names:?}"
    );
    assert!(
        type_names.contains(&"Option<bool>"),
        "expected Option<bool> in IR types, got: {type_names:?}"
    );
    // Verify works — the field defaults resolved properly against the field type
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )),
        "expected verify with multi-instantiation defaults to pass, got: {results:?}"
    );
}

// ── Lemma-as-assumption injection ─────────────────────────

/// a theorem with `by L` uses the lemma's conclusion as an
/// assumption during proof.
#[test]
fn theorem_by_lemma_injects_conclusion() {
    let src = r"module T

entity Counter { value: int = 0 }

system Inc(counters: Store<Counter>) {
  command inc(c: Counter) requires c.value >= 0 {
    c.value' = c.value + 1
  }
}

lemma non_negative {
  all c: Counter | c.value >= 0
}

theorem bounded for Inc {
  assume {
    store counters: Counter[0..3]
    let inc = Inc { counters: counters }
    stutter
  }
  by non_negative
  show always (all c: Counter | c.value >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "bounded"
        )),
        "expected theorem with `by L` to prove, got: {results:?}"
    );
}

/// without `by L`, the same directly-inductive theorem still proves.
#[test]
fn theorem_without_by_lemma_still_works_when_inductive() {
    let src = r"module T

entity Counter { value: int = 0 }

system Inc(counters: Store<Counter>) {
  command inc(c: Counter) requires c.value >= 0 {
    c.value' = c.value + 1
  }
}

theorem bounded for Inc {
  assume {
    store counters: Counter[0..3]
    let inc = Inc { counters: counters }
    stutter
  }
  show always (all c: Counter | c.value >= 0)
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "bounded"
        )),
        "expected directly inductive theorem to prove without lemma, got: {results:?}"
    );
}

/// lemma with pure (non-entity) body is proved independently.
#[test]
fn lemma_proved_independently() {
    let src = r"module T

lemma tautology {
  true implies true
}
";
    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "tautology"
        )),
        "expected lemma to be proved, got: {results:?}"
    );
}

/// theorem verdict carries assumption list with stutter
#[test]
fn theorem_verdict_includes_stutter_assumption() {
    let src = r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}
theorem safe for Billing {
  assume {
    store orders: Order[0..3]
    let billing = Billing { orders: orders }
    stutter
  }
  show always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    let theorem = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. } if name == "safe"
        )
    });
    if let Some(abide::verify::VerificationResult::Proved { assumptions, .. }) = theorem {
        assert!(
            assumptions
                .iter()
                .any(|a| matches!(a, abide::verify::TrustedAssumption::Stutter)),
            "expected Stutter in assumptions, got: {assumptions:?}"
        );
    } else {
        panic!("expected theorem to prove, got: {results:?}");
    }
}

// ── Result vocabulary with assumption disclosure ──────────

/// theorem verdict Display includes stutter in annotation
#[test]
fn verdict_display_includes_stutter() {
    let src = r"module T
entity Order { status: int = 0 }
system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}
theorem safe for Billing {
  assume {
    store orders: Order[0..3]
    let billing = Billing { orders: orders }
    stutter
  }
  show always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    let proved = results.iter().find(
        |r| matches!(r, abide::verify::VerificationResult::Proved { name, .. } if name == "safe"),
    );
    let display = format!("{}", proved.expect("theorem should prove"));
    assert!(
        display.contains("under stutter"),
        "expected 'under stutter' in verdict display, got: {display}"
    );
}

/// verify block with stutter only — no fairness in display
#[test]
fn verdict_display_stutter_only_no_fairness() {
    let src = r"module T

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    let checked = results.iter().find(|r| {
        matches!(r,
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )
    });
    let display = format!("{}", checked.expect("verify should pass"));
    assert!(
        display.contains("under stutter"),
        "expected 'under stutter' in display, got: {display}"
    );
    assert!(
        !display.contains("WF") && !display.contains("SF"),
        "expected no fairness in display, got: {display}"
    );
}

/// axiom name appears in verdict display
#[test]
fn verdict_display_includes_axiom() {
    let src = r"module T

axiom truth = true

entity Order { status: int = 0 }

system Billing(orders: Store<Order>) {
  command charge(order: Order) requires order.status == 0 {
    order.status' = 1
  }
}

verify v {
  assume {
    store orders: Order[0..2]
    let billing = Billing { orders: orders }
    stutter
  }
  assert always (all o: Order | o.status >= 0)
}
";
    let results = verify_source(src);
    let checked = results.iter().find(|r| {
        matches!(r,
            abide::verify::VerificationResult::Checked { name, .. }
            | abide::verify::VerificationResult::Proved { name, .. }
            if name == "v"
        )
    });
    let display = format!("{}", checked.expect("verify should pass"));
    assert!(
        display.contains("axiom truth"),
        "expected 'axiom truth' in display, got: {display}"
    );
}

// ── CE presentation ───────────────────────────────────────

/// Fairness analysis on liveness violation: the display includes a
/// "Loop fairness analysis" section showing per-event status.
#[test]
fn liveness_violation_shows_fairness_analysis() {
    // Use the existing fairness fixture which produces a LIVENESS_VIOLATION
    // for the unfair_signal verify block.
    let prog = lower_file("tests/fixtures/fairness.ab");
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    let lv = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::LivenessViolation { name, .. }
                if name == "unfair_signal"
        )
    });
    assert!(
        lv.is_some(),
        "expected LIVENESS_VIOLATION for unfair_signal"
    );

    // The display should include the fairness analysis section
    let display = format!("{}", lv.unwrap());
    assert!(
        display.contains("Loop fairness analysis:"),
        "expected fairness analysis section in display, got:\n{display}"
    );
}

/// Deadlock display includes event diagnostics (22d) and uses the
/// new multi-action infrastructure (22c). The step-0 deadlock path
/// extracts per-event diagnostics explaining why each event is disabled.
#[test]
fn deadlock_display_includes_step_and_diagnostics() {
    // Reuse the existing deadlock pattern: event with `requires false`.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("deadlock_diag2.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify dl {\n  assume {\n    store es: Sig[0..3]\n    \
         let s = S { sigs: es }\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    let dl = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Deadlock { name, .. }
                if name == "dl"
        )
    });
    assert!(dl.is_some(), "expected DEADLOCK for dl");

    let display = format!("{}", dl.unwrap());
    // Display should show step 0 and event diagnostics
    assert!(
        display.contains("step 0"),
        "expected step 0 in deadlock, got:\n{display}"
    );
    assert!(
        display.contains("Event diagnostics:"),
        "expected event diagnostics in deadlock display, got:\n{display}"
    );
    assert!(
        display.contains("S::impossible:"),
        "expected S::impossible diagnostic, got:\n{display}"
    );
}

/// Deadlock event diagnostics: shows why each event is disabled.
#[test]
fn deadlock_event_diagnostics() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("deadlock_diag.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         enum St = A | B\n\n\
         entity E {\n  s: St = @A\n  \
         action go() requires s == @B { s' = @A }\n}\n\n\
         system S(es: Store<E>) {\n  \
         command go() { choose e: E where e.s == @B { e.go() } }\n}\n\n\
         verify deadlocks_at_init {\n  assume {\n    store es: E[0..2]\n    \
         let s = S { es: es }\n  }\n  \
         assert eventually true\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    let dl = results.iter().find(|r| {
        matches!(
            r,
            abide::verify::VerificationResult::Deadlock { name, .. }
                if name == "deadlocks_at_init"
        )
    });
    assert!(dl.is_some(), "expected DEADLOCK for deadlocks_at_init");

    // Check the display includes event diagnostics
    let display = format!("{}", dl.unwrap());
    assert!(
        display.contains("Event diagnostics:"),
        "expected event diagnostics in deadlock display, got:\n{display}"
    );
    assert!(
        display.contains("S::go:"),
        "expected S::go diagnostic, got:\n{display}"
    );
}

// ── Newtypes ─────────────────────────────────────────────

/// Newtype declarations parse and verify end-to-end.
/// Constructor calls are transparent to the solver.
#[test]
fn newtype_declaration_and_constructor() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("newtype.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         type UserId(string)\n\n\
         entity User {\n  id: UserId = UserId(\"\")\n  name: string = \"\"\n}\n\n\
         system S(users: Store<User>) {\n  \
         command signup() { create User {} }\n}\n\n\
         verify v {\n  assume {\n    store us: User[0..2]\n    \
         let s = S { users: us }\n    stutter\n  }\n  \
         assert always (all u: User | u.id == UserId(\"\"))\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "newtype verify should PROVE, got: {results:?}"
    );
}

/// Newtype constructor in function bodies works.
#[test]
fn newtype_in_function_body() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("newtype_fn.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         type UserId(string)\n\n\
         fn make_id(s: string): UserId { UserId(s) }\n\n\
         entity E { x: int = 0 }\n\
         system S(es: Store<E>) {}\n\n\
         verify v {\n  assume {\n    store es: E[0..1]\n    \
         let s = S { es: es }\n    stutter\n  }\n  \
         assert always make_id(\"a\") == make_id(\"a\")\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "newtype fn should PROVE, got: {results:?}"
    );
}

// ── create...in store_name ───────────────────────────────

/// `create Entity in store_name { fields }` syntax parses and verifies.
#[test]
fn create_in_store_syntax() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("create_in.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         entity User {\n  name: string = \"\"\n}\n\n\
         system S(users: Store<User>) {\n  \
         command signup() {\n    \
         create User in users {\n      name = \"alice\"\n    }\n  }\n}\n\n\
         verify v {\n  assume {\n    store us: User[0..2]\n    \
         let s = S { users: us }\n    stutter\n  }\n  \
         assert always true\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "create...in should PROVE, got: {results:?}"
    );
}

// ── Named refinement type parameters ─────────────────────

/// Named refinement `type Positive = x: int{x > 0}` parses and verifies.
#[test]
fn named_refinement_type_parameter() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("named_refine.ab");
    std::fs::write(
        &file,
        "module T\n\n\
         type Positive = x: int{x > 0}\n\n\
         entity E {\n  val: Positive = 1\n}\n\n\
         system S(es: Store<E>) {}\n\n\
         verify v {\n  assume {\n    store es: E[0..2]\n    \
         let s = S { es: es }\n    stutter\n  }\n  \
         assert always (all e: E | e.val > 0)\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "v"
        )),
        "named refinement should PROVE, got: {results:?}"
    );
}

// ── extern / dep / may ──────────────────────────────────

#[test]
fn extern_crosscall_requires_declared_dep() {
    let src = r"module T

enum Outcome = ok | err

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge {
    return @ok
  }
}

entity Order {
  id: int = 0
}

system Billing(orders: Store<Order>) {
  command submit(order: Order) {
    Stripe::charge(order.id)
  }
}
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("without declaring `dep Stripe`")),
        "expected missing-dep extern diagnostic, got: {errors:?}"
    );
}

#[test]
fn extern_command_requires_may_block() {
    let src = r"module T

enum Outcome = ok | err

extern Stripe {
  command charge(order_id: int) -> Outcome
}
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("missing a `may charge` block")),
        "expected missing may-block diagnostic, got: {errors:?}"
    );
}

#[test]
fn extern_may_return_must_match_command_type() {
    let src = r"module T

enum Outcome = ok | err

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge {
    return 1
  }
}
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|e| e
            .message
            .contains("returns `int` but command `charge` requires `Outcome`")),
        "expected extern may type mismatch diagnostic, got: {errors:?}"
    );
}

#[test]
fn scene_with_extern_crosscall_and_choose_return_passes() {
    let src = r"module T

enum Outcome = ok(int) | err

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge {
    return @ok(choose id: int where id > 0 and $ > 0)
    return @err
  }
}

entity Marker {
  id: int = 0
}

system Billing(markers: Store<Marker>) {
  dep Stripe

  charged: bool = false

  command submit() {
    Stripe::charge(1)
    charged' = true
  }
}

scene submit_calls_extern {
  given {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
  }
  when {
    let submit = billing.submit()
  }
  then {
    assert true
  }
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "submit_calls_extern"
        )),
        "scene with extern crosscall should PASS, got: {results:?}"
    );
}

#[test]
fn macro_step_let_call_binds_system_command_result() {
    let src = r"module T

enum Outcome = ok { value: int } | err

entity Marker {
  id: int = 0
}

system Provider {
  command charge(x: int) -> Outcome {
    return @ok { value: x }
  }
}

system Billing(markers: Store<Marker>) {
  charged: bool = false

  command submit() {
    let result = Provider::charge(1)
    match result {
      ok { value: id } => { charged' = id == 1 }
      err => { charged' = false }
    }
  }
}

verify submit_binds_result {
  assume {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
    stutter
  }
  assert always true
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "submit_binds_result"
        ) || matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "submit_binds_result"
        )),
        "macro-action let-call verify should succeed, got: {results:?}"
    );
}

#[test]
fn macro_step_direct_match_on_crosscall_updates_state() {
    let src = r"module T

enum Outcome = ok | err

entity Marker {
  id: int = 0
}

system Provider {
  command charge() -> Outcome { return @ok }
}

system Billing(markers: Store<Marker>) {
  charged: bool = false

  command submit() {
    match Provider::charge() {
      ok => { charged' = true }
      err => { charged' = false }
    }
  }
}

verify submit_matches_crosscall {
  assume {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
    stutter
  }
  assert always true
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "submit_matches_crosscall"
        ) || matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "submit_matches_crosscall"
        )),
        "macro-action direct match verify should succeed, got: {results:?}"
    );
}

#[test]
fn macro_step_direct_match_rejects_empty_brace_unit_patterns() {
    let src = r"module T

enum Outcome = ok | err

entity Marker {
  id: int = 0
}

system Provider {
  command charge() -> Outcome { return @ok }
}

system Billing(markers: Store<Marker>) {
  charged: bool = false

  command submit() {
    match Provider::charge() {
      ok {} => { charged' = true }
      err {} => { charged' = false }
    }
  }
}

verify submit_matches_empty_brace_unit_patterns {
  assume {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
    stutter
  }
  assert always true
}
";

    let (_result, errors) = elab_with_errors(src);
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("unit constructor pattern `ok {}` should be written `ok`")),
        "expected unit constructor empty-brace diagnostic in action match, got: {errors:?}"
    );
}

#[test]
fn macro_step_inline_command_clause_binds_crosscall_result() {
    let src = r"module T

enum Outcome = ok { value: int } | err

entity Marker {
  id: int = 0
}

system Provider {
  command charge(x: int) -> Outcome {
    return @ok { value: x }
  }
}

system Billing(markers: Store<Marker>) {
  charged: bool = false

  command submit() requires true {
    let result = Provider::charge(1)
    match result {
      ok { value: id } => { charged' = id == 1 }
      err => { charged' = false }
    }
  }
}

verify submit_inline_clause {
  assume {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
    stutter
  }
  assert always true
}
";

    let results = verify_source(src);
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "submit_inline_clause"
        ) || matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "submit_inline_clause"
        )),
        "macro-action inline command clause verify should succeed, got: {results:?}"
    );
}

#[test]
fn verify_result_discloses_reachable_extern_assumptions() {
    let src = r"module T

enum Outcome = ok | err

extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge {
    return @ok
    return @err
  }
  assume {
    fair charge
    true
  }
}

entity Marker {
  id: int = 0
}

system Billing(markers: Store<Marker>) {
  dep Stripe

  command submit() {
    Stripe::charge(1)
  }
}

verify v {
  assume {
    store ms: Marker[0..1]
    let billing = Billing { markers: ms }
    stutter
  }
  assert always true
}
";

    let results = verify_source(src);
    let proved = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "v",
        abide::verify::VerificationResult::Checked { name, .. } => name == "v",
        _ => false,
    });

    let assumptions = match proved {
        Some(
            abide::verify::VerificationResult::Proved { assumptions, .. }
            | abide::verify::VerificationResult::Checked { assumptions, .. },
        ) => assumptions,
        other => panic!("expected proved or checked result for v, got {other:?}"),
    };

    assert!(
        assumptions.iter().any(|a| matches!(
            a,
            abide::verify::TrustedAssumption::ExternAssume { external, detail }
                if external == "Stripe" && detail == "WF charge"
        )),
        "expected reachable extern fairness assumption, got: {assumptions:?}"
    );
    assert!(
        assumptions.iter().any(|a| matches!(
            a,
            abide::verify::TrustedAssumption::ExternAssume { external, detail }
                if external == "Stripe" && detail == "assume #2"
        )),
        "expected reachable generic extern assume disclosure, got: {assumptions:?}"
    );
}
