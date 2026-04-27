//! QA script runner — executes `.qa` scripts against loaded specs.

use std::path::{Path, PathBuf};

use crate::ir;
use crate::loader;
use abide_ir::ir::types::{
    IRAssumptionSet, IRExpr, IRStoreDecl, IRType, IRVerify, IRVerifySystem, LitVal,
};
use abide_verify::verify::{
    explore_verify_state_space, verify_all, ExplicitStateSpace, VerifyConfig,
};

use super::artifacts::{ArtifactStore, SimulationArtifact, StateSpaceArtifact};
use super::ast::{QAStatement, Query, SimulationRequest, StateSpaceRequest};
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

pub trait RunnerHooks {
    fn simulate(
        &mut self,
        _ir_program: &ir::types::IRProgram,
        _request: &SimulationRequest,
    ) -> Result<SimulationArtifact, String> {
        Err("simulation is not available in this QA runner".to_owned())
    }

    fn explore_state_space(
        &mut self,
        ir_program: &ir::types::IRProgram,
        request: &StateSpaceRequest,
    ) -> Result<StateSpaceArtifact, String> {
        explore_state_space(ir_program, request)
    }
}

#[derive(Default)]
struct NoopRunnerHooks;

impl RunnerHooks for NoopRunnerHooks {}

/// Run a `.qa` script file.
///
/// If `spec_dir` is provided, it's loaded before the script's `load` statements.
/// Returns the run result with pass/fail counts and output.
#[allow(clippy::too_many_lines)]
pub fn run_qa_script(script_path: &Path, spec_dir: Option<&Path>, json_mode: bool) -> QARunResult {
    let mut hooks = NoopRunnerHooks;
    run_qa_script_with_hooks(script_path, spec_dir, json_mode, &mut hooks)
}

pub fn run_qa_script_with_hooks<H: RunnerHooks>(
    script_path: &Path,
    spec_dir: Option<&Path>,
    json_mode: bool,
    hooks: &mut H,
) -> QARunResult {
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
    let mut artifacts = ArtifactStore::default();

    for stmt in &statements {
        if matches!(stmt, QAStatement::Load(_)) {
            continue;
        }

        // Handle abide blocks: parse, merge into base env overlay, rebuild model
        if let QAStatement::AbideBlock(code) = stmt {
            match crate::parse::parse_string_recovering(code) {
                Ok(parsed) => {
                    if !parsed.errors.is_empty() {
                        for err in &parsed.errors {
                            output.push(format!("  ERROR: abide block parse error: {err}"));
                        }
                        failed += 1;
                        continue;
                    }
                    let overlay = crate::elab::collect::collect(&parsed.program);
                    merge_env_overlay(&mut base_env, &overlay);
                    let cleared = artifacts.invalidate();
                    // Rebuild model from merged env
                    match rebuild_model(&base_env) {
                        Ok(new_model) => {
                            model = new_model;
                            output.push("  OK: abide block applied (in-memory)".to_owned());
                            if cleared > 0 {
                                output.push(format!(
                                    "  OK: invalidated {cleared} stored artifacts after model change"
                                ));
                            }
                        }
                        Err(errors) => {
                            for e in &errors {
                                output.push(format!("  ERROR: {e}"));
                            }
                            failed += 1;
                        }
                    }
                }
                Err(errors) => {
                    for err in errors {
                        output.push(format!("  ERROR: abide block lex error: {err}"));
                    }
                    failed += 1;
                }
            }
            continue;
        }
        if matches!(stmt, QAStatement::Verify) {
            executed += 1;
            match rebuild_ir_program(&base_env) {
                Ok(ir_program) => {
                    let results = verify_all(&ir_program, &VerifyConfig::default());
                    let stored = artifacts.record_verify_results(&results);
                    for result in &results {
                        output.push(result.to_string());
                    }
                    output.push(format!("stored {stored} artifact(s)"));
                }
                Err(errors) => {
                    failed += 1;
                    for e in errors {
                        output.push(format!("  ERROR: {e}"));
                    }
                }
            }
            continue;
        }
        if let QAStatement::Simulate(request) = stmt {
            executed += 1;
            match rebuild_ir_program(&base_env) {
                Ok(ir_program) => match hooks.simulate(&ir_program, request) {
                    Ok(simulation) => {
                        let name = request
                            .system
                            .clone()
                            .or_else(|| simulation.systems.first().cloned())
                            .unwrap_or_else(|| "simulation".to_owned());
                        let stored = artifacts.record_simulation_result(name, simulation.clone());
                        output.push(render_simulation_summary(&simulation));
                        output.push(format!("stored {stored} artifact(s)"));
                    }
                    Err(err) => {
                        failed += 1;
                        output.push(format!("error: {err}"));
                    }
                },
                Err(errors) => {
                    failed += 1;
                    for e in errors {
                        output.push(format!("  ERROR: {e}"));
                    }
                }
            }
            continue;
        }
        if let QAStatement::Explore(request) = stmt {
            executed += 1;
            match rebuild_ir_program(&base_env) {
                Ok(ir_program) => match hooks.explore_state_space(&ir_program, request) {
                    Ok(state_space) => {
                        let name = state_space_artifact_name(&state_space, request);
                        let stored = artifacts.record_state_space_result(name, state_space.clone());
                        output.push(render_state_space_summary(&state_space));
                        output.push(format!("stored {stored} artifact(s)"));
                    }
                    Err(err) => {
                        failed += 1;
                        output.push(format!("error: {err}"));
                    }
                },
                Err(errors) => {
                    failed += 1;
                    for e in errors {
                        output.push(format!("  ERROR: {e}"));
                    }
                }
            }
            continue;
        }
        if matches!(stmt, QAStatement::Artifacts) {
            executed += 1;
            if artifacts.is_empty() {
                output.push("No stored artifacts.".to_owned());
            } else {
                for artifact in artifacts.artifacts() {
                    output.push(artifact.summary_line());
                }
            }
            continue;
        }
        if let Some(rendered) = handle_artifact_statement(stmt, &artifacts) {
            executed += 1;
            match rendered {
                Ok(text) => output.push(text),
                Err(err) => {
                    failed += 1;
                    output.push(format!("error: {err}"));
                }
            }
            continue;
        }
        executed += 1;
        let outcome = exec::execute_statement_detailed_with_env(&model, Some(&base_env), stmt);
        let verb = outcome.verb;
        let result = outcome.result;
        let stored_temporal = if let Some(verification_result) = &outcome.semantic_artifact {
            temporal_artifact_name(stmt)
                .map(|name| artifacts.record_named_verification_result(name, verification_result))
                .unwrap_or(0)
        } else {
            0
        };

        if json_mode {
            output.push(fmt::format_result_json(verb, &result));
            if verb == Verb::Assert {
                if matches!(
                    &result,
                    QueryResult::Bool(false)
                        | QueryResult::BoolWithMode { value: false, .. }
                        | QueryResult::Error(_)
                ) {
                    failed += 1;
                } else {
                    passed += 1;
                }
            }
        } else if verb == Verb::Assert {
            match &result {
                QueryResult::Bool(false) | QueryResult::BoolWithMode { value: false, .. } => {
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
            if stored_temporal > 0 {
                output.push(format!(
                    "  OK: stored {stored_temporal} temporal artifact(s)"
                ));
            }
        } else {
            output.push(fmt::format_result(verb, &result));
            if stored_temporal > 0 {
                output.push(format!("stored {stored_temporal} artifact(s)"));
            }
        }
    }

    QARunResult {
        passed,
        failed,
        executed,
        output,
    }
}

fn temporal_artifact_name(stmt: &QAStatement) -> Option<String> {
    let query = match stmt {
        QAStatement::Ask(query) | QAStatement::Explain(query) | QAStatement::Assert(query) => query,
        _ => return None,
    };
    let Query::Temporal { .. } = query else {
        return None;
    };
    let mut out = String::from("qa_temporal_");
    let rendered = query.to_string();
    let mut last_was_sep = false;
    for ch in rendered.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            last_was_sep = false;
        } else if !last_was_sep {
            out.push('_');
            last_was_sep = true;
        }
    }
    while out.ends_with('_') {
        out.pop();
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn semantic_temporal_failures_are_stored_as_artifacts() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time")
            .as_nanos();
        let dir = std::env::temp_dir().join(format!("abide-qa-runner-{unique}"));
        fs::create_dir_all(&dir).expect("create temp dir");

        let spec_path = dir.join("spec.ab");
        let script_path = dir.join("script.qa");
        fs::write(
            &spec_path,
            r#"
enum OrderStatus = Pending | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
}

system Commerce(orders: Store<Order>) {
  command ship(order: Order)
  step ship(order: Order) requires order.status == @Pending {
    order.status' = @Shipped
  }
}
"#,
        )
        .expect("write spec");
        fs::write(
            &script_path,
            r#"
load "spec.ab"
ask always on Commerce true
artifacts
show artifact deadlock:qa_temporal_always_on_commerce_true
"#,
        )
        .expect("write script");

        let result = run_qa_script(&script_path, None, false);
        assert_eq!(result.failed, 0);
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("false [semantic:counterexample[slots=4]]")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("stored 1 artifact(s)")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("#1 deadlock qa_temporal_always_on_commerce_true")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("witness kind: deadlock")));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn explore_statements_store_state_space_artifacts() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time")
            .as_nanos();
        let dir = std::env::temp_dir().join(format!("abide-qa-explore-{unique}"));
        fs::create_dir_all(&dir).expect("create temp dir");

        let spec_path = dir.join("spec.ab");
        let script_path = dir.join("script.qa");
        fs::write(
            &spec_path,
            r#"
enum OrderStatus = Pending | Confirmed

entity Order {
  id: identity
  status: OrderStatus = @Pending
}

system Commerce(orders: Store<Order>) {
  command submit(order: Order)
  step submit(order: Order) requires order.status == @Pending {
    order.status' = @Confirmed
  }
}
"#,
        )
        .expect("write spec");
        fs::write(
            &script_path,
            r#"
load "spec.ab"
explore --system Commerce --slots 1
artifacts
show artifact state-space:state_space_commerce
draw artifact state-space:state_space_commerce
"#,
        )
        .expect("write script");

        let result = run_qa_script(&script_path, None, false);
        assert_eq!(result.failed, 0);
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("State space")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("stored 1 artifact(s)")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("#1 state-space state_space_commerce")));
        assert!(result
            .output
            .iter()
            .any(|line| line.contains("bounded state-space exploration")));
        assert!(result.output.iter().any(|line| line.contains("[state 0]")));

        let _ = fs::remove_dir_all(&dir);
    }
}

fn render_simulation_summary(simulation: &SimulationArtifact) -> String {
    let mut out = String::new();
    out.push_str("Simulation\n");
    out.push_str(&format!("  systems: {}\n", simulation.systems.join(", ")));
    out.push_str(&format!("  seed: {}\n", simulation.seed));
    out.push_str(&format!(
        "  steps: {}/{}\n",
        simulation.steps_executed, simulation.steps_requested
    ));
    match &simulation.termination {
        super::artifacts::SimulationTermination::StepLimit => {
            out.push_str("  termination: step limit reached\n");
        }
        super::artifacts::SimulationTermination::Deadlock { reasons } => {
            out.push_str("  termination: deadlock\n");
            for reason in reasons {
                out.push_str(&format!("    - {reason}\n"));
            }
        }
    }
    out.trim_end().to_owned()
}

pub fn explore_state_space(
    ir_program: &ir::types::IRProgram,
    request: &StateSpaceRequest,
) -> Result<StateSpaceArtifact, String> {
    let selected_systems = select_exploration_systems(ir_program, request.system.as_deref())?;
    let verify_block = build_state_space_verify(ir_program, &selected_systems, request);
    explore_verify_state_space(ir_program, &verify_block, &VerifyConfig::default())?
        .ok_or_else(|| {
            "state-space exploration is not supported for this program fragment by the explicit-state backend"
                .to_owned()
        })
}

fn select_exploration_systems<'a>(
    ir_program: &'a ir::types::IRProgram,
    system: Option<&str>,
) -> Result<Vec<&'a ir::types::IRSystem>, String> {
    if let Some(system_name) = system {
        let system = ir_program
            .systems
            .iter()
            .find(|candidate| candidate.name == system_name)
            .ok_or_else(|| format!("no system named `{system_name}`"))?;
        return Ok(vec![system]);
    }
    if ir_program.systems.is_empty() {
        return Err("program contains no systems to explore".to_owned());
    }
    Ok(ir_program.systems.iter().collect())
}

fn build_state_space_verify(
    ir_program: &ir::types::IRProgram,
    systems: &[&ir::types::IRSystem],
    request: &StateSpaceRequest,
) -> IRVerify {
    let systems_bound = systems
        .iter()
        .map(|system| IRVerifySystem {
            name: system.name.clone(),
            lo: request.slots as i64,
            hi: request.slots as i64,
        })
        .collect();
    let stores = systems
        .iter()
        .flat_map(|system| {
            system.store_params.iter().map(|store| IRStoreDecl {
                name: format!("__qa_explore_store_{}_{}", system.name, store.name),
                entity_type: store.entity_type.clone(),
                lo: slots_for_entity(request, &store.entity_type) as i64,
                hi: slots_for_entity(request, &store.entity_type) as i64,
            })
        })
        .collect();

    let _ = ir_program;
    IRVerify {
        name: "__qa_state_space".to_owned(),
        depth: None,
        systems: systems_bound,
        stores,
        assumption_set: IRAssumptionSet::default_for_verify(),
        asserts: vec![IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }],
        span: None,
        file: None,
    }
}

fn slots_for_entity(request: &StateSpaceRequest, entity_type: &str) -> usize {
    request
        .scopes
        .iter()
        .rev()
        .find_map(|(entity, slots)| (entity == entity_type).then_some(*slots))
        .unwrap_or(request.slots)
}

fn state_space_artifact_name(
    state_space: &ExplicitStateSpace,
    request: &StateSpaceRequest,
) -> String {
    if let Some(system) = &request.system {
        return format!("state_space_{}", sanitize_artifact_name(system));
    }
    if state_space.systems.is_empty() {
        return "state_space".to_owned();
    }
    format!(
        "state_space_{}",
        state_space
            .systems
            .iter()
            .map(|name| sanitize_artifact_name(name))
            .collect::<Vec<_>>()
            .join("_")
    )
}

fn sanitize_artifact_name(name: &str) -> String {
    let mut out = String::new();
    let mut last_was_sep = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            last_was_sep = false;
        } else if !last_was_sep {
            out.push('_');
            last_was_sep = true;
        }
    }
    while out.ends_with('_') {
        out.pop();
    }
    if out.is_empty() {
        "state_space".to_owned()
    } else {
        out
    }
}

pub fn render_state_space_summary(state_space: &StateSpaceArtifact) -> String {
    let mut out = String::new();
    out.push_str("State space\n");
    out.push_str(&format!("  systems: {}\n", state_space.systems.join(", ")));
    out.push_str(&format!("  stutter: {}\n", state_space.stutter));
    if state_space.store_bounds.is_empty() {
        out.push_str("  store bounds: (none)\n");
    } else {
        out.push_str("  store bounds:\n");
        for store in &state_space.store_bounds {
            out.push_str(&format!(
                "    - {}: Store<{}>[{}]\n",
                store.name, store.entity_type, store.slots
            ));
        }
    }
    out.push_str(&format!(
        "  states: {}  transitions: {}  initial: {}\n",
        state_space.states.len(),
        state_space.transitions.len(),
        state_space.initial_state
    ));
    out
}

fn handle_artifact_statement(
    stmt: &QAStatement,
    artifacts: &ArtifactStore,
) -> Option<Result<String, String>> {
    match stmt {
        QAStatement::ShowArtifact(selector) => Some(
            artifacts
                .resolve(selector)
                .map(|artifact| artifact.render_show())
                .ok_or_else(|| format!("unknown artifact selector `{selector}`")),
        ),
        QAStatement::DrawArtifact(selector) => Some(
            artifacts
                .resolve(selector)
                .ok_or_else(|| format!("unknown artifact selector `{selector}`"))
                .and_then(|artifact| artifact.render_draw()),
        ),
        QAStatement::StateArtifact { selector, index } => Some(
            artifacts
                .resolve(selector)
                .ok_or_else(|| format!("unknown artifact selector `{selector}`"))
                .and_then(|artifact| artifact.render_state(*index)),
        ),
        QAStatement::DiffArtifact { selector, from, to } => Some(
            artifacts
                .resolve(selector)
                .ok_or_else(|| format!("unknown artifact selector `{selector}`"))
                .and_then(|artifact| artifact.render_diff(*from, *to)),
        ),
        QAStatement::ExportArtifact { selector, format } => Some(
            artifacts
                .resolve(selector)
                .ok_or_else(|| format!("unknown artifact selector `{selector}`"))
                .and_then(|artifact| {
                    if format == "json" {
                        artifact.export_json()
                    } else {
                        Err(format!("unsupported export format `{format}`"))
                    }
                }),
        ),
        _ => None,
    }
}

/// Load `.ab` files, elaborate, and build a `FlowModel`.
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

    let (ir_program, _lower_diag) = ir::lower(&result);
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
    let ir_program = rebuild_ir_program(env)?;
    Ok(extract::extract(&ir_program))
}

fn rebuild_ir_program(env: &crate::elab::env::Env) -> Result<ir::types::IRProgram, Vec<String>> {
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
    let (ir_program, _lower_diag) = ir::lower(&result);
    Ok(ir_program)
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

/// Collect all `.ab` files from a directory recursively, sorted
/// alphabetically for deterministic load order.
fn collect_abide_files(dir: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok().map(|e| e.path())).collect(),
        Err(_) => return,
    };
    entries.sort();
    for path in entries {
        if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("ab" | "abi" | "abp")
        ) {
            paths.push(path);
        } else if path.is_dir() {
            collect_abide_files(&path, paths);
        }
    }
}

// Display impls for QAStatement and Query are in ast.rs — used directly via {}.
