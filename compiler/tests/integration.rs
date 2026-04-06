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
fn lex_all_fixtures() {
    for name in &["simple", "auth", "commerce", "inventory", "workflow"] {
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

// ── IR lowering + JSON integration tests ─────────────────────────────

fn lower_file(path: &str) -> ir::types::IRProgram {
    let result = elaborate_file(path);
    ir::lower(&result)
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
    for name in &["simple", "auth", "inventory", "workflow"] {
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
/// for the lockout_correctness theorem (which fails with liveness).
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
    let spec_file = std::path::Path::new("tests/fixtures/commerce.ab");
    let result = abide::qa::runner::run_qa_script(script, Some(spec_file), false);
    // With -f preloading + script's own load, commerce is loaded (possibly double-loaded
    // but module system deduplicates). Assertions should still pass.
    assert_eq!(result.failed, 0, "assertions should pass with -f preload");
}

#[test]
fn qa_script_load_from_directory() {
    // Create a temp directory with a single .ab file
    let tmp = tempfile::TempDir::new().unwrap();
    let spec_dir = tmp.path().join("specs");
    std::fs::create_dir(&spec_dir).unwrap();
    std::fs::copy(
        "tests/fixtures/hypo_base.ab",
        spec_dir.join("ticket.ab"),
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
        .arg("tests/fixtures/contracts.ab")
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
    let file = dir.path().join("assert_false_no_ensures.ab");
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
    let file = dir.path().join("nested_assert.ab");
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
    let file = dir.path().join("assume_false.ab");
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
    let file = dir.path().join("sorry_bool.ab");
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
    let file = dir.path().join("sorry_int.ab");
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
    let file = dir.path().join("sorry_no_ensures.ab");
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
    let file = dir.path().join("sorry_nested.ab");
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
    let file = dir.path().join("sorry_term.ab");
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
    let file = dir.path().join("ref_quant.ab");
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
    let file = dir.path().join("unknown_field.ab");
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
    let file = dir.path().join("bare_ctor.ab");
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
    let file = dir.path().join("nested.ab");
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
    let file = dir.path().join("nested_valid.ab");
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
    let file = dir.path().join("if_assign.ab");
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
    let file = dir.path().join("branch_cond.ab");
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
    let file = dir.path().join("inner_no_inv.ab");
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
    let file = dir.path().join("unreachable.ab");
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
    let file = dir.path().join("loop_branch.ab");
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
    let file = dir.path().join("neg_call.ab");
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
    let file = dir.path().join("guarded.ab");
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
    let file = dir.path().join("leaked.ab");
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

    // False property: not all Colors are Red
    let file = dir.path().join("enum_quant_verify.ab");
    std::fs::write(
        &file,
        "module T\n\nenum Color = Red | Green | Blue\n\nsystem S {}\n\n\
         verify q for S[0..1] {\n  assert all c: Color | c == @Color::Red\n}\n",
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

    // True property with lone: exactly one Color is Red
    let file2 = dir.path().join("lone_verify.ab");
    std::fs::write(
        &file2,
        "module T\n\nenum Color = Red | Green | Blue\n\nsystem S {}\n\n\
         verify q for S[0..1] {\n  assert lone c: Color | c == @Color::Red\n}\n",
    )
    .unwrap();

    let prog2 = lower_file(file2.to_str().unwrap());
    let results2 = abide::verify::verify_all(&prog2, &abide::verify::VerifyConfig::default());

    assert!(
        results2.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "q"
        )),
        "lone c: Color | c == @Red should be CHECKED (at most one is true)"
    );
}

/// Regression: refinement domain predicates must be enforced in verify blocks.
/// `one y: Positive | y == 0` must be false because 0 is outside Positive.
#[test]
fn verify_refinement_domain_in_verify_block() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let file = dir.path().join("refine.ab");
    std::fs::write(
        &file,
        "module T\n\ntype Positive = Int { $ > 0 }\n\nsystem S {}\n\n\
         verify q for S[0..1] {\n  assert one y: Positive | y == 0\n}\n",
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
    std::fs::write(
        &file,
        "module T\n\nenum Shape = Circle { r: Int } | Square { s: Int }\n\nsystem S {}\n\n\
         verify q for S[0..1] {\n  assert lone sh: Shape | sh == @Circle { r: 1 } or sh == @Circle { r: 2 }\n}\n",
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
         entity E { x: Int = 0 }\n\
         system S { use E }\n\n\
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

    // Fair system: liveness should be CHECKED
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Checked { name, .. }
                if name == "fair_signal"
        )),
        "fair_signal should be CHECKED (lasso BMC with fair events)"
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

    // Safety property: should be PROVED by induction
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Proved { name, .. }
                if name == "safety_check"
        )),
        "safety_check should be PROVED (safety property, no liveness)"
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
         system S {\n  use Job\n  \
         event create_job() { create Job {} }\n  \
         fair event move_to_waiting() {\n    \
         choose j: Job where j.st == @Pending { j.postpone() }\n  }\n}\n\n\
         verify response for S[0..6] {\n  \
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
         system S {\n  use Job\n  \
         event create_job() { create Job {} }\n  \
         fair event choose_a() { choose j: Job where j.st == @Pending { j.go_a() } }\n  \
         fair event choose_b() { choose j: Job where j.st == @Pending { j.go_b() } }\n}\n\n\
         verify responses for S[0..6] {\n  \
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
         system S {\n  use Job\n  \
         event create_job() { create Job {} }\n  \
         fair event process() {\n    \
         choose j: Job where j.st == @Pending { j.poke() }\n  }\n}\n\n\
         verify test for S[0..4] {\n  \
         assert eventually exists j: Job | j.st == @Pending\n}\n",
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

    // Direct: Red until Green — without fair events, BMC finds
    // counterexample where toggle doesn't fire (stutter).
    // This is correct: until requires Q to hold, which is liveness.
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "direct_until"
        )),
        "direct_until should produce COUNTEREXAMPLE (toggle may not fire without fairness)"
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

    // StuckRed: Red until Green fails (Green never occurs)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "never_green"
        )),
        "never_green should produce COUNTEREXAMPLE (Q never holds)"
    );

    // Via prop: until inside prop definition (def expansion path)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "via_prop"
        )),
        "via_prop should produce COUNTEREXAMPLE (until expanded from prop)"
    );

    // Via pred: until inside pred definition (def expansion path)
    assert!(
        results.iter().any(|r| matches!(
            r,
            abide::verify::VerificationResult::Counterexample { name, .. }
                if name == "via_pred"
        )),
        "via_pred should produce COUNTEREXAMPLE (until expanded from pred)"
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
         system S {\n  use Order\n  \
         event create_order() { create Order {} }\n  \
         event cancel_order() {\n    \
         choose o: Order where o.status == @Pending { o.cancel() }\n  }\n}\n\n\
         verify no_cancel for S[0..4] {\n  \
         assert always all o: Order | o.status != @Cancelled\n}\n",
    )
    .unwrap();

    let prog = lower_file(file.to_str().unwrap());
    let results = abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());

    // Should find counterexample with event identification
    let ce = results.iter().find(|r| matches!(
        r,
        abide::verify::VerificationResult::Counterexample { name, .. }
            if name == "no_cancel"
    ));
    assert!(ce.is_some(), "should produce COUNTEREXAMPLE");

    if let Some(abide::verify::VerificationResult::Counterexample { trace, .. }) = ce {
        // At least one step should have an identified event
        let has_event = trace.iter().any(|s| s.event.is_some());
        assert!(has_event, "counterexample should identify at least one event");

        // Should contain cancel_order event
        let has_cancel = trace.iter().any(|s| {
            s.event.as_deref().map_or(false, |e| e.contains("cancel_order"))
        });
        assert!(has_cancel, "counterexample should identify cancel_order event");
    }
}

// ── Phase 7: Nested actions in Choose/ForAll ────────────────────────

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

// ── Phase 8: Match exhaustiveness checking ──────────────────────────

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
    let has_exhaustiveness_error = actual_errors.iter().any(|e| {
        matches!(
            e.kind,
            abide::elab::error::ErrorKind::NonExhaustiveMatch
        )
    });
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
    let has_exhaustiveness_error = actual_errors.iter().any(|e| {
        matches!(
            e.kind,
            abide::elab::error::ErrorKind::NonExhaustiveMatch
        )
    });
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
    let has_exhaustiveness_error = actual_errors.iter().any(|e| {
        matches!(
            e.kind,
            abide::elab::error::ErrorKind::NonExhaustiveMatch
        )
    });
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

// ── Phase 10: Scene composition operator semantics ──────────────────

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
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
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
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
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
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
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
        matches!(r.unwrap(), abide::verify::VerificationResult::SceneFail { .. }),
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
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
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
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "same_step_pair should PASS (& same-step composition), got: {r:?}"
    );
}

#[test]
fn scene_ordering_same_step_then_sequence() {
    let results = verify_file("tests/fixtures/scene_ordering.ab");
    // (confirm & create) -> ship: atomic pair then sequence
    let r = find_scene_result(&results, "same_step_then_sequence");
    assert!(r.is_some(), "same_step_then_sequence should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "same_step_then_sequence should PASS (& then ->), got: {r:?}"
    );
}

// ── Phase 11: QA query completeness ─────────────────────────────────

#[test]
fn qa_invariants_query() {
    let script = std::path::Path::new("tests/fixtures/test_qa_contracts.qa");
    let result = abide::qa::runner::run_qa_script(script, None, false);
    // Script should execute without errors
    assert!(
        !result.output.iter().any(|l| l.contains("not yet implemented")),
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
    // Test contract query directly via the exec module
    let prog = lower_file("tests/fixtures/commerce.ab");
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
            assert!(
                has_requires,
                "should include requires clause: {items:?}"
            );
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
    let src = r#"
module QATest
enum Shape = Circle { radius: Int } | Rectangle { width: Int, height: Int }
entity Canvas {
  shape: Shape = @Circle { radius: 0 }
  action set_circle(r: Int)
    requires r > 0
    ensures shape' == @Circle { radius: r }
  {
    shape' = @Circle { radius: r }
  }
}
"#;
    // Parse, elaborate, lower
    let tokens = abide::lex::lex(src).unwrap();
    let mut parser = abide::parse::Parser::new(tokens);
    let program = parser.parse_program().unwrap();
    let (result, _) = abide::elab::elaborate(&program);
    let ir = abide::ir::lower(&result);
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

// ── Phase 12: Scene event cardinality + ^| ──────────────────────────

#[test]
fn scene_cardinality_lone_fires() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_fires_once");
    assert!(r.is_some(), "lone_fires_once should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "lone_fires_once should PASS, got: {r:?}"
    );
}

#[test]
fn scene_cardinality_lone_skips() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_does_not_fire");
    assert!(r.is_some(), "lone_does_not_fire should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "lone_does_not_fire should PASS (optional event can skip), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_no() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "no_cancel");
    assert!(r.is_some(), "no_cancel should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "no_cancel should PASS ({{no}} event excluded), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_exact_n() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "exact_two_creates");
    assert!(r.is_some(), "exact_two_creates should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "exact_two_creates should PASS ({{2}} fires twice), got: {r:?}"
    );
}

#[test]
fn scene_cardinality_some() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "some_creates");
    assert!(r.is_some(), "some_creates should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "some_creates should PASS ({{some}} fires at least once), got: {r:?}"
    );
}

#[test]
fn scene_xor_exclusive_choice() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_confirm_or_cancel");
    assert!(r.is_some(), "xor_confirm_or_cancel should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "xor_confirm_or_cancel should PASS (exactly one fires), got: {r:?}"
    );
}

#[test]
fn scene_lone_in_same_step() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "lone_in_same_step");
    assert!(r.is_some(), "lone_in_same_step should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "lone_in_same_step should PASS ({{lone}} in & can skip), got: {r:?}"
    );
}

#[test]
fn scene_xor_exact_one() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_exact_one");
    assert!(r.is_some(), "xor_exact_one should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::ScenePass { .. }),
        "xor_exact_one should PASS ({{1}} in ^| infers {{lone}}), got: {r:?}"
    );
}

#[test]
fn scene_xor_both_impossible() {
    let results = verify_file("tests/fixtures/scene_cardinality.ab");
    let r = find_scene_result(&results, "xor_both_required");
    assert!(r.is_some(), "xor_both_required should produce a result");
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::SceneFail { .. }),
        "xor_both_required should FAIL (can't have both states), got: {r:?}"
    );
}

// ── Phase 13: Liveness-to-safety reduction ──────────────────────────

#[test]
fn liveness_reduction_or_checked() {
    // The reduction + IC3 should PROVE the liveness property unboundedly.
    // Accept PROVED (reduction) or CHECKED (lasso BMC fallback if IC3 times out).
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
    // Preferably PROVED via liveness-to-safety
    match r.unwrap() {
        abide::verify::VerificationResult::Proved { method, .. } => {
            assert!(
                method.contains("liveness"),
                "should be proved via liveness-to-safety, got method: {method}"
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
    // Safety should use regular induction, not the reduction
    assert!(
        matches!(r.unwrap(), abide::verify::VerificationResult::Proved { method, .. } if method.contains("induction") && !method.contains("liveness")),
        "safety_check should use regular induction, got: {r:?}"
    );
}

#[test]
fn liveness_bare_eventuality() {
    let results = verify_file("tests/fixtures/liveness_reduction.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. }
        | abide::verify::VerificationResult::Checked { name, .. } => name == "bare_eventuality",
        _ => false,
    });
    assert!(r.is_some(), "bare_eventuality should produce a result (got: {results:?})");
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
    assert!(r.is_some(), "persistence_check should produce a result (got: {results:?})");
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
    assert!(r.is_some(), "until_check should produce a result (got: {results:?})");
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
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "until_theorem"
    ));
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
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "until_painted"
    ));
    assert!(
        r.is_some(),
        "until_painted must be UNPROVABLE (IC3 BAS unsound for liveness), got: {results:?}"
    );
}

// ── Symmetry reduction (Phase 16) ───────────────────────────────────

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
        abide::verify::VerificationResult::Unprovable { name, .. } => {
            name == "asymmetric_liveness"
        }
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
    let r = results.iter().find(|r| matches!(
        r,
        abide::verify::VerificationResult::Checked { name, .. }
        | abide::verify::VerificationResult::Proved { name, .. }
            if name == "symmetric_verify"
    ));
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
    assert!(strong.is_some(), "strong_liveness should be UNPROVABLE (got: {results:?})");
    let weak = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "weak_liveness"
    ));
    assert!(weak.is_some(), "weak_liveness should be UNPROVABLE (got: {results:?})");
}

#[test]
fn strong_fairness_safety_unaffected() {
    let results = verify_file("tests/fixtures/strong_fairness.ab");
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Proved { name, .. } if name == "safety_check"
    ));
    assert!(r.is_some(), "safety_check should be PROVED (got: {results:?})");
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
    let r = results.iter().find(|r| matches!(
        r, abide::verify::VerificationResult::Unprovable { name, .. } if name == "deep_dead"
    ));
    assert!(
        r.is_some(),
        "deep_dead should be UNPROVABLE (got: {results:?})"
    );
}

// ── Nondeterministic initial values (Phase 14) ─────────────────────

#[test]
fn nondet_in_explores_all_values() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "in_explores_all",
        _ => false,
    });
    assert!(r.is_some(), "in_explores_all should be PROVED (got: {results:?})");
}

#[test]
fn nondet_where_constrains() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "where_constrains",
        _ => false,
    });
    assert!(r.is_some(), "where_constrains should be PROVED (got: {results:?})");
}

#[test]
fn nondet_deterministic_regression() {
    let results = verify_file("tests/fixtures/nondet_defaults.ab");
    let r = results.iter().find(|r| match r {
        abide::verify::VerificationResult::Proved { name, .. } => name == "deterministic_regression",
        _ => false,
    });
    assert!(r.is_some(), "deterministic_regression should be PROVED (got: {results:?})");
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
    // `b: Bool in {1}` must produce an elaboration error (Int for Bool field).
    let paths = [std::path::PathBuf::from(
        "tests/fixtures/nondet_defaults_invalid.ab",
    )];
    let (env, load_errors, _) = abide::loader::load_files(&paths);
    assert!(load_errors.is_empty());
    let (_, errors) = abide::elab::elaborate_env(env);
    assert!(
        errors.iter().any(|e| {
            let msg = format!("{e}");
            msg.contains("Int") && msg.contains("Bool")
        }),
        "should reject Int literal in `in` for Bool field (got: {errors:?})"
    );
}

// ── Collection operations (Phase 1) ────────────────────────────────

#[test]
fn collection_ops_all_proved() {
    let results = verify_file("tests/fixtures/collection_ops.ab");
    let expected = [
        // Set qualified calls
        "set_union_int", "set_intersect_int", "set_diff_int",
        "set_subset_int", "set_disjoint_int", "set_not_disjoint_int",
        "set_member_int", "set_not_member_int",
        // Set::member polymorphic
        "set_member_real",
        // Set operators (<>, !*)
        "set_union_op", "set_disjoint_op", "set_not_disjoint_op",
        // Type-directed operators (*, -, <=) — dispatched at IR level
        "set_intersect_star", "set_diff_minus", "set_subset_le",
        // Seq
        "seq_head_int", "seq_bool_eq",
    ];
    for name in &expected {
        let r = results.iter().find(|r| match r {
            abide::verify::VerificationResult::Proved { name: n, .. } => n == name,
            _ => false,
        });
        assert!(r.is_some(), "{name} should be PROVED (got: {results:?})");
    }
}
