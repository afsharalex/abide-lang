use abide::elab;
use abide::ir;
use abide::lex;
use abide::parse::Parser;

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
    for err in &errors {
        eprintln!("{path}: {err}");
    }
    assert!(errors.is_empty(), "{path} should elaborate without errors");
    result
}

#[test]
fn parse_simple() {
    parse_file("tests/fixtures/simple.abide");
}

#[test]
fn parse_auth() {
    parse_file("tests/fixtures/auth.abide");
}

#[test]
fn parse_commerce() {
    parse_file("tests/fixtures/commerce.abide");
}

#[test]
fn parse_inventory() {
    parse_file("tests/fixtures/inventory.abide");
}

#[test]
fn parse_workflow() {
    parse_file("tests/fixtures/workflow.abide");
}

#[test]
fn lex_all_fixtures() {
    for name in &["simple", "auth", "commerce", "inventory", "workflow"] {
        let path = format!("tests/fixtures/{name}.abide");
        let src = std::fs::read_to_string(&path).unwrap();
        lex::lex(&src).unwrap_or_else(|errors| {
            panic!("lex errors in {path}: {errors:?}");
        });
    }
}

// ── Elaboration integration tests ────────────────────────────────────

#[test]
fn elaborate_simple() {
    let result = elaborate_file("tests/fixtures/simple.abide");
    assert!(!result.types.is_empty(), "should have types");
    assert!(!result.entities.is_empty(), "should have entities");
}

#[test]
fn elaborate_auth() {
    let result = elaborate_file("tests/fixtures/auth.abide");
    assert!(result.entities.len() >= 2, "should have User and Session");
    assert!(!result.systems.is_empty(), "should have Auth system");
    assert!(!result.preds.is_empty(), "should have predicates");
    assert!(!result.verifies.is_empty(), "should have verify blocks");
}

#[test]
fn elaborate_commerce() {
    let result = elaborate_file("tests/fixtures/commerce.abide");
    assert!(
        result.systems.len() >= 2,
        "should have Commerce and Billing"
    );
    assert!(!result.scenes.is_empty(), "should have scenes");
    assert!(!result.proofs.is_empty(), "should have proofs");
}

#[test]
fn elaborate_inventory() {
    let result = elaborate_file("tests/fixtures/inventory.abide");
    assert!(
        result.entities.len() >= 3,
        "should have Product, Reservation, Fulfillment"
    );
}

#[test]
fn elaborate_workflow() {
    let result = elaborate_file("tests/fixtures/workflow.abide");
    assert!(
        !result.lemmas.is_empty() || !result.proofs.is_empty(),
        "should have proofs or lemmas"
    );
}

// ── IR lowering + JSON integration tests ─────────────────────────────

fn lower_file(path: &str) -> ir::types::IRProgram {
    let result = elaborate_file(path);
    ir::lower(&result)
}

#[test]
fn lower_simple() {
    let prog = lower_file("tests/fixtures/simple.abide");
    assert!(!prog.types.is_empty(), "should have IR types");
    assert!(!prog.entities.is_empty(), "should have IR entities");
    // Verify JSON serialization doesn't panic
    let json = ir::emit_json(&prog);
    assert!(
        json.contains("\"entities\""),
        "JSON should contain entities key"
    );
}

#[test]
fn lower_commerce() {
    let prog = lower_file("tests/fixtures/commerce.abide");
    assert!(prog.systems.len() >= 2, "should have Commerce and Billing");
    assert!(!prog.verifies.is_empty(), "should have IR verifies");
    assert!(!prog.scenes.is_empty(), "should have IR scenes");
    let json = ir::emit_json(&prog);
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert!(parsed["systems"].is_array());
    assert!(parsed["scenes"].is_array());
}

#[test]
fn lower_all_fixtures() {
    for name in &["simple", "auth", "commerce", "inventory", "workflow"] {
        let path = format!("tests/fixtures/{name}.abide");
        let prog = lower_file(&path);
        let json = ir::emit_json(&prog);
        // Verify it's valid JSON
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
}
