use std::path::PathBuf;

use abide::elab;
use abide::ir;
use abide::lex;
use abide::loader;
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
    ir::lower(&result)
}

/// Commerce fixture: multi-file via include (commerce.abide includes billing.abide).
const COMMERCE_FIXTURE: &[&str] = &["tests/fixtures/commerce.abide"];

/// Logistics fixture: two includes, wildcard + aliased imports.
const LOGISTICS_FIXTURE: &[&str] = &["tests/fixtures/logistics.abide"];

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
    assert!(result.systems.len() >= 1, "should have Logistics system");
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
        "logistics_safety should be PROVED or CHECKED, got: {:?}",
        results
    );
    // reserve_and_ship scene uses aliased (WSlot) and wildcard (Package) entity names
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::ScenePass { name, .. }
                if name == "reserve_and_ship"
        )),
        "reserve_and_ship scene should PASS, got: {:?}",
        results
    );
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
        !result.lemmas.is_empty() || !result.theorems.is_empty(),
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
    for name in &["simple", "auth", "inventory", "workflow"] {
        let path = format!("tests/fixtures/{name}.abide");
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
    let results = verify_file("tests/fixtures/auth.abide");
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
    let results = verify_file("tests/fixtures/workflow.abide");
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
    let results = verify_file("tests/fixtures/inventory.abide");
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
fn verify_commerce_fixture() {
    // Multi-file: commerce.abide includes billing.abide
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
    let path = std::path::PathBuf::from("tests/fixtures/auth.abide");
    let mut sources = vec![];
    let (result, _errors) = {
        let mut srcs: Vec<(String, String)> = vec![];
        let r = load_and_elaborate_for_test(&[path.clone()], &mut srcs);
        sources = srcs;
        r
    };
    let ir = abide::ir::lower(&result);
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
            file.contains("auth.abide"),
            "file should reference auth.abide, got: {file}"
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

/// Verify that `abide verify` on auth.abide produces miette-rendered output
/// for the lockout_correctness theorem (which fails with liveness).
/// Checks that stderr contains file path, line markers, and labeled span.
#[test]
fn cli_verify_renders_miette_snippet_for_failure() {
    let binary = env!("CARGO_BIN_EXE_abide");
    let output = std::process::Command::new(binary)
        .args(["verify", "tests/fixtures/auth.abide"])
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
        stderr.contains("auth.abide"),
        "stderr should reference auth.abide file: {stderr}"
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
        .args(["verify", "tests/fixtures/workflow.abide"])
        .output()
        .expect("failed to run abide verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should exit successfully
    assert!(
        output.status.success(),
        "expected zero exit: stdout={stdout}, stderr={stderr}"
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

// ── Multi-file diagnostic tests ──────────────────────────────────────

/// Verify that duplicate declarations across files produce errors with file tags.
#[test]
fn multi_file_duplicate_decl_has_file_tags() {
    let dir = tempfile::tempdir().expect("create tempdir");

    let file_a = dir.path().join("a.abide");
    std::fs::write(&file_a, "enum Color = Red | Blue\n").unwrap();

    let file_b = dir.path().join("b.abide");
    std::fs::write(&file_b, "enum Color = Green | Yellow\n").unwrap();

    let main_file = dir.path().join("main.abide");
    std::fs::write(&main_file, "include \"a.abide\"\ninclude \"b.abide\"\n").unwrap();

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
    let file = dir.path().join("test.abide");
    std::fs::write(
        &file,
        r#"
enum OrderStatus = Pending | Confirmed

entity Order {
    status: OrderStatus = @Pending
    action confirm() requires Confirmd == @Pending {
        status' = @Confirmed
    }
}
"#,
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
    let spec_file = std::path::Path::new("tests/fixtures/commerce.abide");
    let result = abide::qa::runner::run_qa_script(script, Some(spec_file), false);
    // With -f preloading + script's own load, commerce is loaded (possibly double-loaded
    // but module system deduplicates). Assertions should still pass.
    assert_eq!(result.failed, 0, "assertions should pass with -f preload");
}

#[test]
fn qa_script_load_from_directory() {
    // Create a temp directory with a single .abide file
    let tmp = tempfile::TempDir::new().unwrap();
    let spec_dir = tmp.path().join("specs");
    std::fs::create_dir(&spec_dir).unwrap();
    std::fs::copy(
        "tests/fixtures/hypo_base.abide",
        spec_dir.join("ticket.abide"),
    )
    .unwrap();

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
    // Multi-file: a.abide includes b.abide, b.abide includes a.abide → CircularInclude
    let dir = tempfile::tempdir().expect("create tempdir");

    let a_path = dir.path().join("a.abide");
    std::fs::write(&a_path, "include \"b.abide\"\nenum AType = X").unwrap();

    let b_path = dir.path().join("b.abide");
    std::fs::write(&b_path, "include \"a.abide\"\nenum BType = Y").unwrap();

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

    let a_path = dir.path().join("a.abide");
    std::fs::write(&a_path, "include \"b.abide\"").unwrap();

    let b_path = dir.path().join("b.abide");
    std::fs::write(&b_path, "include \"a.abide\"").unwrap();

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

    let a_path = dir.path().join("a.abide");
    std::fs::write(
        &a_path,
        "module Test\ninclude \"b.abide\"\nuse Missing::*\nenum A = X",
    )
    .unwrap();

    let b_path = dir.path().join("b.abide");
    std::fs::write(&b_path, "include \"a.abide\"\nenum B = Y").unwrap();

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
    let prog = lower_file("tests/fixtures/contracts.abide");
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

    // max: ensures result >= a, ensures result >= b
    assert!(
        results.iter().any(|r| matches!(
            &r,
            abide::verify::VerificationResult::FnContractProved { name, .. }
                if name == "max"
        )),
        "max contract should be PROVED"
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
        .arg("tests/fixtures/contracts.abide")
        .output()
        .expect("run CLI");
    assert!(
        output.status.success(),
        "CLI should succeed for valid contracts"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("PROVED  fn abs"), "should show abs proved");
    assert!(stdout.contains("PROVED  fn max"), "should show max proved");
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
        .arg("tests/fixtures/contracts.abide")
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
    let file = dir.path().join("bad.abide");
    std::fs::write(
        &file,
        "module Bad\n\nfn identity(x: Int): Int\n  ensures result > x\n{\n  x\n}\n",
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
    let prog = lower_file("tests/fixtures/imperative.abide");
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

    // abs and max: pure if/else with ensures
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
                if name == "max"
        )),
        "max should be PROVED"
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

    // Exactly 6 fn contracts verified (sum_to, gcd, abs, max, checked_divide, with_assertion)
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
        "should verify exactly 6 fn contracts in imperative.abide"
    );
}

#[test]
fn verify_assert_assume_fixture() {
    let prog = lower_file("tests/fixtures/assert_assume.abide");
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
    let file = dir.path().join("assert_false.abide");
    std::fs::write(
        &file,
        "module TestFail\n\nfn bad(x: Int): Int\n  ensures result == x\n{\n  assert false\n  x\n}\n",
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
    let file = dir.path().join("assert_false_no_ensures.abide");
    std::fs::write(
        &file,
        "module TestFail\n\nfn bad(x: Int): Int {\n  assert false\n  x\n}\n",
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
    let file = dir.path().join("nested_assert.abide");
    std::fs::write(
        &file,
        "module TestNested\n\nfn bad(x: Int): Int { x + (assert false) }\n",
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
    let file = dir.path().join("assume_false.abide");
    std::fs::write(
        &file,
        "module TestAssume\n\nfn vacuous(x: Int): Int\n  ensures result > 999\n{\n  assume false\n  x\n}\n",
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
    let file = dir.path().join("sorry_bool.abide");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn bool_sorry(x: Int): Bool\n  ensures result == true\n{\n  sorry\n}\n",
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
        "sorry in Bool fn should be ADMITTED (not PROVED)"
    );
}

#[test]
fn verify_sorry_int_fn_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_int.abide");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn int_sorry(x: Int): Int\n  ensures result > 0\n{\n  sorry\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // sorry in Int fn should be ADMITTED (previously errored with type mismatch)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::FnContractAdmitted { name, reason, .. }
                if name == "int_sorry" && reason.contains("sorry")
        )),
        "sorry in Int fn should be ADMITTED (not type error)"
    );
}

#[test]
fn verify_sorry_no_ensures_admitted() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("sorry_no_ensures.abide");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn no_ensures(x: Int): Int {\n  sorry\n}\n",
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
    let file = dir.path().join("sorry_nested.abide");
    std::fs::write(
        &file,
        "module TestSorry\n\nfn f(x: Int): Int { x + sorry }\n",
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
    let file = dir.path().join("sorry_term.abide");
    std::fs::write(
        &file,
        "module TestSorry\n\n\
         fn f(n: Int): Int\n  ensures result >= 0\n  decreases n\n\
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
        !results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Unprovable { .. }
        )),
        "sorry should not produce any UNKNOWN/Unprovable results"
    );
}

#[test]
fn verify_quantifiers_fixture() {
    let prog = lower_file("tests/fixtures/quantifiers.abide");
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
    let file = dir.path().join("enum_quant.abide");
    std::fs::write(
        &file,
        "module T\n\nenum E = A | B\n\n\
         fn bad(x: Int): Bool\n  ensures exists y: E | y != @E::A and y != @E::B\n{\n  true\n}\n",
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
    let file = dir.path().join("ref_quant.abide");
    std::fs::write(
        &file,
        "module T\n\ntype Positive = Int { $ > 0 }\n\n\
         fn bad(x: Int): Bool\n  ensures exists y: Positive | y < 0\n{\n  true\n}\n",
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
    let prog = lower_file("tests/fixtures/cardinality.abide");
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
    let file = dir.path().join("setcomp_false.abide");
    std::fs::write(
        &file,
        "module T\n\nfn bad(x: Int): Bool\n  ensures 0 in { y: Int where y > 0 }\n{\n  true\n}\n",
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
    let prog = lower_file("tests/fixtures/constructor_fields.abide");
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
    let file = dir.path().join("missing_field.abide");
    std::fs::write(
        &file,
        "module T\n\nenum S = R { w: Int, h: Int }\n\n\
         fn f(): Int\n  ensures true\n{\n  match @R { w: 1 } { _ => 0 }\n}\n",
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
    let file = dir.path().join("unknown_field.abide");
    std::fs::write(
        &file,
        "module T\n\nenum S = R { w: Int, h: Int }\n\n\
         fn f(): Int\n  ensures true\n{\n  match @R { z: 1, w: 2 } { _ => 0 }\n}\n",
    )
    .unwrap();

    // Front-end should catch unknown fields during elaboration
    let program = parse_file(file.to_str().unwrap());
    let (_result, errors) = abide::elab::elaborate(&program);

    assert!(
        errors.iter().any(|e| format!("{e}").contains("unknown field")),
        "constructor with unknown field should produce elab error"
    );
}

#[test]
fn verify_bare_field_ctor_rejected() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("bare_ctor.abide");
    std::fs::write(
        &file,
        "module T\n\nenum Option = None | Some { value: Int }\n\n\
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
    let prog = lower_file("tests/fixtures/lambdas.abide");
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
    let file = dir.path().join("weak.abide");
    std::fs::write(
        &file,
        "module Weak\n\n\
         fn counting(n: Int): Int\n\
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
    let file = dir.path().join("nested.abide");
    std::fs::write(
        &file,
        "module Nested\n\n\
         fn nested_unsound(n: Int): Int\n\
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
    let file = dir.path().join("nested_valid.abide");
    std::fs::write(
        &file,
        "module NestedValid\n\n\
         fn matrix_sum(rows: Int, cols: Int): Int\n\
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
    let file = dir.path().join("if_assign.abide");
    std::fs::write(
        &file,
        "module IfAssign\n\n\
         fn conditional_assign(flag: Bool): Int\n\
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
    let file = dir.path().join("branch_cond.abide");
    std::fs::write(
        &file,
        "module BranchCond\n\n\
         fn branch_inner(flag: Bool): Int\n\
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
    let file = dir.path().join("inner_no_inv.abide");
    std::fs::write(
        &file,
        "module InnerNoInv\n\n\
         fn inner_no_inv(n: Int): Int\n\
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
    // A while loop in an unreachable branch (if flag { if not flag { ... } })
    // must not pollute the solver — even with `invariant false`.
    // Previously, post-loop assertions were unguarded and collapsed the proof.
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("unreachable.abide");
    std::fs::write(
        &file,
        "module Unreachable\n\n\
         fn unreachable_branch_bug(flag: Bool): Int\n\
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
    let file = dir.path().join("loop_branch.abide");
    std::fs::write(
        &file,
        "module LoopBranch\n\n\
         fn loop_branch_pollute(flag: Bool): Int\n\
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

// ── Phase 2: Call-site precondition checking ────────────────────────

#[test]
fn verify_call_site_preconditions() {
    let prog = lower_file("tests/fixtures/call_site.abide");
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
        .arg("tests/fixtures/call_site.abide")
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
    let file = dir.path().join("val_call.abide");
    std::fs::write(
        &file,
        "module ValCall\n\n\
         fn positive(x: Int): Int\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 x\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S { use DummyE }\n\n\
         verify bad_prop for S[0..1] {\n\
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
    let file = dir.path().join("neg_call.abide");
    std::fs::write(
        &file,
        "module NegCall\n\n\
         fn ok(x: Int): Bool\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 true\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S { use DummyE }\n\n\
         verify neg_bad for S[0..1] {\n\
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
    let file = dir.path().join("guarded.abide");
    std::fs::write(
        &file,
        "module Guarded\n\n\
         fn positive(x: Int): Bool\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 true\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S { use DummyE }\n\n\
         verify guarded for S[0..1] {\n\
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
    let file = dir.path().join("leaked.abide");
    std::fs::write(
        &file,
        "module Leaked\n\n\
         fn positive(x: Int): Int\n\
         \x20 requires x > 0\n\
         {\n\
         \x20 x\n\
         }\n\n\
         enum Dummy = A\n\
         entity DummyE { status: Dummy = @A }\n\
         system S { use DummyE }\n\n\
         verify bad_encode for S[0..1] {\n\
         \x20 assert (0 > 0) implies (x == 0)\n\
         }\n\n\
         verify should_fail for S[0..1] {\n\
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

// ── Phase 3: Termination verification ───────────────────────────────

#[test]
fn verify_termination_fixture() {
    let prog = lower_file("tests/fixtures/termination.abide");
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
        .arg("tests/fixtures/termination.abide")
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
    let prog = lower_file("tests/fixtures/recursion_stress.abide");
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

    // Valid: multi-step let chain before recursive call
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

// ── Phase 4: Refinement type enforcement at call sites ──────────────

#[test]
fn verify_refinement_call_site_fixture() {
    let prog = lower_file("tests/fixtures/refinement_call_site.abide");
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
