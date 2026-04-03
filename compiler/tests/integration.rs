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
    assert!(
        result.systems.len() >= 1,
        "should have Logistics system"
    );
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
    let results =
        abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
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
    let results =
        abide::verify::verify_all(&prog, &abide::verify::VerifyConfig::default());
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
