//! QA script runner — executes `.qa` scripts against loaded specs.

use std::path::{Path, PathBuf};

use crate::ir;
use crate::loader;

use super::ast::QAStatement;
use super::exec::{self, QueryResult, Verb};
use super::extract;
use super::fmt;
use super::model::FlowModel;
use super::parse;

/// Result of running a QA script.
pub struct QARunResult {
    /// Number of assertions that passed.
    pub passed: usize,
    /// Number of assertions that failed.
    pub failed: usize,
    /// Total statements executed (excluding load).
    pub executed: usize,
    /// Output lines for display.
    pub output: Vec<String>,
}

/// Run a `.qa` script file.
///
/// If `spec_dir` is provided, it's loaded before the script's `load` statements.
/// Returns the run result with pass/fail counts and output.
#[allow(clippy::too_many_lines)]
pub fn run_qa_script(script_path: &Path, spec_dir: Option<&Path>, json_mode: bool) -> QARunResult {
    let script_content = match std::fs::read_to_string(script_path) {
        Ok(s) => s,
        Err(e) => {
            return QARunResult {
                passed: 0,
                failed: 0,
                executed: 0,
                output: vec![format!("error: cannot read {}: {e}", script_path.display())],
            };
        }
    };

    let statements = match parse::parse_qa(&script_content) {
        Ok(stmts) => stmts,
        Err(e) => {
            return QARunResult {
                passed: 0,
                failed: 0,
                executed: 0,
                output: vec![format!("error: {}: {e}", script_path.display())],
            };
        }
    };

    // Collect all load paths, then load specs
    let mut load_paths: Vec<PathBuf> = Vec::new();
    let script_dir = script_path.parent().unwrap_or(Path::new("."));

    // Pre-load from -f flag if provided
    if let Some(dir) = spec_dir {
        if dir.is_file() {
            load_paths.push(dir.to_owned());
        } else {
            collect_abide_files(dir, &mut load_paths);
        }
    }

    // Process load statements first
    for stmt in &statements {
        if let QAStatement::Load(path_str) = stmt {
            let load_path = resolve_load_path(script_dir, path_str);
            if load_path.is_dir() {
                collect_abide_files(&load_path, &mut load_paths);
            } else {
                load_paths.push(load_path);
            }
        }
    }

    // Load and elaborate all specs
    let (mut base_env, mut model) = match load_and_build_model(&load_paths) {
        Ok(pair) => pair,
        Err(errors) => {
            return QARunResult {
                passed: 0,
                failed: 0,
                executed: 0,
                output: errors,
            };
        }
    };

    // Execute non-load statements
    let mut passed = 0;
    let mut failed = 0;
    let mut executed = 0;
    let mut output = Vec::new();

    for stmt in &statements {
        if matches!(stmt, QAStatement::Load(_)) {
            continue;
        }

        // Handle abide blocks: parse, merge into base env overlay, rebuild model
        if let QAStatement::AbideBlock(code) = stmt {
            match crate::parse::parse_string(code) {
                Ok(program) => {
                    let overlay = crate::elab::collect::collect(&program);
                    merge_env_overlay(&mut base_env, &overlay);
                    // Rebuild model from merged env
                    match rebuild_model(&base_env) {
                        Ok(new_model) => {
                            model = new_model;
                            output.push("  OK: abide block applied (in-memory)".to_owned());
                        }
                        Err(errors) => {
                            for e in &errors {
                                output.push(format!("  ERROR: {e}"));
                            }
                            failed += 1;
                        }
                    }
                }
                Err(e) => {
                    output.push(format!("  ERROR: abide block parse error: {e}"));
                    failed += 1;
                }
            }
            continue;
        }
        executed += 1;
        let (verb, result) = exec::execute_statement(&model, stmt);

        if json_mode {
            output.push(fmt::format_result_json(verb, &result));
            if verb == Verb::Assert {
                if matches!(&result, QueryResult::Bool(false) | QueryResult::Error(_)) {
                    failed += 1;
                } else {
                    passed += 1;
                }
            }
        } else if verb == Verb::Assert {
            match &result {
                QueryResult::Bool(false) => {
                    failed += 1;
                    output.push(format!("  FAIL: {stmt}"));
                }
                QueryResult::Error(msg) => {
                    failed += 1;
                    output.push(format!("  ERROR: {stmt} — {msg}"));
                }
                _ => {
                    passed += 1;
                    output.push(format!("  PASS: {stmt}"));
                }
            }
        } else {
            output.push(fmt::format_result(verb, &result));
        }
    }

    QARunResult {
        passed,
        failed,
        executed,
        output,
    }
}

/// Load `.abide` files, elaborate, and build a `FlowModel`.
/// Returns the loaded `Env` (for hypothetical extension) and the `FlowModel`.
fn load_and_build_model(
    paths: &[PathBuf],
) -> Result<(crate::elab::env::Env, FlowModel), Vec<String>> {
    if paths.is_empty() {
        return Err(vec![
            "error: no spec files loaded — add 'load' statements to your .qa script".to_owned(),
        ]);
    }

    let (mut env, load_errors, _all_paths) = loader::load_files(paths);

    if !load_errors.is_empty() {
        let errors: Vec<String> = load_errors.iter().map(|e| format!("error: {e}")).collect();
        return Err(errors);
    }

    // Include-level load errors (lex/parse/IO in transitively included files)
    // are non-fatal for the loader but must block QA/REPL — a partial model
    // gives incorrect query results.
    if !env.include_load_errors.is_empty() {
        let errors: Vec<String> = env
            .include_load_errors
            .iter()
            .map(|e| format!("error: {e}"))
            .collect();
        return Err(errors);
    }

    // When multiple top-level files were loaded (e.g., directory load or
    // multiple load statements), don't privilege any single file's module
    // as root. Clear module_name so build_working_namespace includes all
    // modules — otherwise only the first file's module is visible.
    if paths.len() > 1 {
        env.module_name = None;
    }

    let base_env = env.clone();
    let (result, elab_errors) = crate::elab::elaborate_env(env);

    let has_errors = elab_errors
        .iter()
        .any(|e| !matches!(e.severity, crate::elab::error::Severity::Warning));
    if has_errors {
        let errors: Vec<String> = elab_errors
            .iter()
            .filter(|e| !matches!(e.severity, crate::elab::error::Severity::Warning))
            .map(|e| format!("error: {e}"))
            .collect();
        return Err(errors);
    }

    let ir_program = ir::lower(&result);
    Ok((base_env, extract::extract(&ir_program)))
}

/// Merge overlay declarations into an env. Entity actions are merged (added to
/// existing entities); other declarations are inserted (overwriting if duplicate).
/// This is the QA-specific overlay for hypothetical entity extension.
///
/// The overlay must declare `module X` so its entities get the correct
/// qualified key (e.g., `Commerce::Order`) matching the base env.
fn merge_env_overlay(dst: &mut crate::elab::env::Env, src: &crate::elab::env::Env) {
    // Module-level metadata: known_modules, use_decls, decls registry.
    // These feed build_working_namespace() and resolve_use_declarations().
    dst.known_modules.extend(src.known_modules.iter().cloned());
    dst.use_decls.extend(src.use_decls.iter().cloned());
    for (key, info) in &src.decls {
        dst.decls.insert(key.clone(), info.clone());
    }

    for (name, ty) in &src.types {
        dst.types.insert(name.clone(), ty.clone());
    }
    for (name, entity) in &src.entities {
        if let Some(existing) = dst.entities.get_mut(name) {
            // Merge: add new actions from the overlay
            for action in &entity.actions {
                if !existing.actions.iter().any(|a| a.name == action.name) {
                    existing.actions.push(action.clone());
                }
            }
            // Merge: add new fields from the overlay
            for field in &entity.fields {
                if !existing.fields.iter().any(|f| f.name == field.name) {
                    existing.fields.push(field.clone());
                }
            }
        } else {
            dst.entities.insert(name.clone(), entity.clone());
        }
    }
    for (name, system) in &src.systems {
        dst.systems.insert(name.clone(), system.clone());
    }
    for (name, pred) in &src.preds {
        dst.preds.insert(name.clone(), pred.clone());
    }
    for (name, prop) in &src.props {
        dst.props.insert(name.clone(), prop.clone());
    }
    for (name, f) in &src.fns {
        dst.fns.insert(name.clone(), f.clone());
    }
    for (name, c) in &src.consts {
        dst.consts.insert(name.clone(), c.clone());
    }
    // Verification/proof declarations (Vec-backed, not map-backed).
    // These are appended — multiple verify/scene/theorem blocks with different
    // names can coexist.
    dst.verifies.extend(src.verifies.iter().cloned());
    dst.scenes.extend(src.scenes.iter().cloned());
    dst.theorems.extend(src.theorems.iter().cloned());
    dst.axioms.extend(src.axioms.iter().cloned());
    dst.lemmas.extend(src.lemmas.iter().cloned());
}

/// Rebuild a `FlowModel` from an env (re-elaborate and lower).
fn rebuild_model(env: &crate::elab::env::Env) -> Result<FlowModel, Vec<String>> {
    let (result, elab_errors) = crate::elab::elaborate_env(env.clone());
    let has_errors = elab_errors
        .iter()
        .any(|e| !matches!(e.severity, crate::elab::error::Severity::Warning));
    if has_errors {
        return Err(elab_errors
            .iter()
            .filter(|e| !matches!(e.severity, crate::elab::error::Severity::Warning))
            .map(|e| format!("{e}"))
            .collect());
    }
    let ir_program = ir::lower(&result);
    Ok(extract::extract(&ir_program))
}

/// Resolve a load path relative to the script directory.
fn resolve_load_path(script_dir: &Path, path_str: &str) -> PathBuf {
    let path = Path::new(path_str);
    if path.is_absolute() {
        path.to_owned()
    } else {
        script_dir.join(path)
    }
}

/// Collect all `.abide` files from a directory recursively, sorted
/// alphabetically for deterministic load order.
fn collect_abide_files(dir: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok().map(|e| e.path())).collect(),
        Err(_) => return,
    };
    entries.sort();
    for path in entries {
        if path.extension().and_then(|e| e.to_str()) == Some("abide") {
            paths.push(path);
        } else if path.is_dir() {
            collect_abide_files(&path, paths);
        }
    }
}

// Display impls for QAStatement and Query are in ast.rs — used directly via {}.
