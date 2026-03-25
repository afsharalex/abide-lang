use abide::lex;
use abide::parse::Parser;

fn parse_file(path: &str) {
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
