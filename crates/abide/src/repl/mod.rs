//! `abide repl` — interactive evaluation environment.
//!
//! Two modes: Abide (default) for spec definitions, QA for structural queries.
//! Mode switching via `/qa` and `/abide` commands.

mod artifacts;
mod complete;

use std::path::{Path, PathBuf};

use reedline::{
    default_emacs_keybindings, ColumnarMenu, DefaultPrompt, DefaultPromptSegment, EditMode, Emacs,
    KeyCode, KeyModifiers, MenuBuilder, Reedline, ReedlineEvent, ReedlineMenu, Signal,
};

use crate::elab;
use crate::elab::env::Env;
use crate::ir;
use crate::loader;
use crate::qa::ast::StateSpaceRequest;
use crate::qa::model::FlowModel;
use crate::qa::{exec, extract, fmt, parse as qa_parse};
use crate::simulate::SimulateConfig;
use crate::verify::VerifyConfig;

use self::artifacts::{ArtifactStore, ReplArtifact};

use complete::AbideCompleter;

/// REPL mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Abide,
    QA,
}

/// Live REPL state: base env from disk + overlay from REPL input.
struct ReplState {
    /// Base file/directory targets currently loaded from disk.
    loaded_targets: Vec<PathBuf>,
    /// Base environment loaded from disk (restored on /reload).
    base_env: Option<Env>,
    /// Overlay definitions entered in the REPL.
    overlay_env: Env,
    /// Current `FlowModel` (rebuilt after changes).
    model: Option<FlowModel>,
    /// Lowered IR used for on-demand verification runs.
    ir_program: Option<crate::ir::types::IRProgram>,
    /// Session-local native evidence artifacts.
    artifacts: ArtifactStore,
    /// Names for tab completion.
    env_names: Vec<String>,
}

impl ReplState {
    fn new(loaded_targets: Vec<PathBuf>, base_env: Option<Env>) -> Self {
        let mut state = Self {
            loaded_targets,
            base_env,
            overlay_env: Env::new(),
            model: None,
            ir_program: None,
            artifacts: ArtifactStore::default(),
            env_names: Vec::new(),
        };
        state.rebuild();
        state
    }

    fn loaded_target_display(&self) -> String {
        if self.loaded_targets.is_empty() {
            "(none)".to_owned()
        } else {
            self.loaded_targets
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        }
    }

    /// Merge base + overlay, elaborate, lower, and rebuild the flow model.
    fn merged_env(&self) -> Env {
        match &self.base_env {
            Some(base) => {
                let mut merged = base.clone();
                merge_overlay(&mut merged, &self.overlay_env);
                merged
            }
            None => self.overlay_env.clone(),
        }
    }

    /// Merge base + overlay, elaborate, lower, and rebuild the flow model.
    fn rebuild(&mut self) {
        let env = self.merged_env();

        let (result, elab_errors) = elab::elaborate_env(env);

        // Print errors but don't block
        for e in &elab_errors {
            if !matches!(e.severity, elab::error::Severity::Warning) {
                eprintln!("  {e}");
            }
        }

        // Collect names for completion
        self.env_names.clear();
        self.env_names
            .extend(result.types.iter().map(|t| t.name.clone()));
        self.env_names
            .extend(result.entities.iter().map(|e| e.name.clone()));
        self.env_names
            .extend(result.systems.iter().map(|s| s.name.clone()));
        self.env_names
            .extend(result.fns.iter().map(|f| f.name.clone()));
        self.env_names
            .extend(result.preds.iter().map(|p| p.name.clone()));

        let (ir_program, _lower_diag) = ir::lower(&result);
        self.model = Some(extract::extract(&ir_program));
        self.ir_program = Some(ir_program);
    }

    /// Add a parsed program's declarations to the overlay and rebuild.
    fn add_overlay(&mut self, program: &crate::ast::Program) {
        let collected = elab::collect::collect(program);
        merge_overlay(&mut self.overlay_env, &collected);
        self.rebuild();
    }

    /// Discard overlay and rebuild from base only.
    fn reset_overlay(&mut self) {
        self.overlay_env = Env::new();
        self.rebuild();
    }

    fn invalidate_artifacts(&mut self) -> usize {
        self.artifacts.invalidate()
    }

    fn current_loaded_files(&self) -> Vec<PathBuf> {
        crate::targets::resolve_source_targets(&self.loaded_targets).unwrap_or_default()
    }

    fn add_loaded_target(&mut self, target: PathBuf) -> Result<LoadTargetOutcome, Vec<String>> {
        let candidate_files = resolve_single_source_target(&target)?;
        let current_files = self.current_loaded_files();
        let already_loaded = !candidate_files.is_empty()
            && candidate_files
                .iter()
                .all(|candidate| current_files.iter().any(|existing| existing == candidate));
        if already_loaded {
            return Ok(LoadTargetOutcome::AlreadyLoaded(target));
        }

        let mut next_targets = self.loaded_targets.clone();
        next_targets.push(target.clone());
        let base_env = load_base_envs(&next_targets)?;
        let entity_count = base_env.entities.len();
        let system_count = base_env.systems.len();
        self.loaded_targets = next_targets;
        self.base_env = Some(base_env);
        let cleared_artifacts = self.invalidate_artifacts();
        self.rebuild();
        Ok(LoadTargetOutcome::Loaded {
            target,
            entity_count,
            system_count,
            cleared_artifacts,
        })
    }

    fn reload_targets(&mut self, target: Option<&Path>) -> Result<ReloadOutcome, Vec<String>> {
        if self.loaded_targets.is_empty() {
            return Ok(ReloadOutcome::NothingLoaded);
        }

        if let Some(target) = target {
            let normalized = normalize_target(target).map_err(|err| vec![err])?;
            let candidate_files = resolve_single_source_target(&normalized)?;
            let current_files = self.current_loaded_files();
            let covered = !candidate_files.is_empty()
                && candidate_files
                    .iter()
                    .all(|candidate| current_files.iter().any(|existing| existing == candidate));
            if !covered {
                return Ok(ReloadOutcome::TargetNotLoaded(normalized));
            }
        }

        let base_env = load_base_envs(&self.loaded_targets)?;
        let entity_count = base_env.entities.len();
        let system_count = base_env.systems.len();
        self.base_env = Some(base_env);
        let cleared_artifacts = self.invalidate_artifacts();
        self.reset_overlay();
        Ok(ReloadOutcome::Reloaded {
            entity_count,
            system_count,
            cleared_artifacts,
        })
    }

    fn verify_current(
        &mut self,
        target: Option<crate::verify::VerifyTargetSelector>,
    ) -> Result<(Vec<crate::verify::VerificationResult>, usize), String> {
        let ir_program = self
            .ir_program
            .as_ref()
            .ok_or_else(|| "no elaborated program available for verification".to_owned())?;
        let results = crate::verify::verify_all(
            ir_program,
            &VerifyConfig {
                target,
                ..VerifyConfig::default()
            },
        );
        let stored = self.artifacts.record_verify_results(&results);
        Ok((results, stored))
    }

    fn simulate_current(
        &mut self,
        config: &SimulateConfig,
    ) -> Result<(crate::simulate::SimulationResult, usize), String> {
        let ir_program = self
            .ir_program
            .as_ref()
            .ok_or_else(|| "no elaborated program available for simulation".to_owned())?;
        let result = crate::simulate::simulate_program(ir_program, config)?;
        let name = config
            .system
            .clone()
            .or_else(|| result.systems.first().cloned())
            .unwrap_or_else(|| "simulation".to_owned());
        let stored = self
            .artifacts
            .record_simulation_result(name, result.clone());
        Ok((result, stored))
    }

    fn explore_current(
        &mut self,
        request: &StateSpaceRequest,
    ) -> Result<(crate::qa::artifacts::StateSpaceArtifact, usize), String> {
        let ir_program = self.ir_program.as_ref().ok_or_else(|| {
            "no elaborated program available for state-space exploration".to_owned()
        })?;
        let result = crate::qa::runner::explore_state_space(ir_program, request)?;
        let name = if let Some(system) = &request.system {
            format!("state_space_{}", system.to_ascii_lowercase())
        } else if result.systems.is_empty() {
            "state_space".to_owned()
        } else {
            format!(
                "state_space_{}",
                result
                    .systems
                    .iter()
                    .map(|system| system.to_ascii_lowercase())
                    .collect::<Vec<_>>()
                    .join("_")
            )
        };
        let stored = self
            .artifacts
            .record_state_space_result(name, result.clone());
        Ok((result, stored))
    }
}

enum LoadTargetOutcome {
    Loaded {
        target: PathBuf,
        entity_count: usize,
        system_count: usize,
        cleared_artifacts: usize,
    },
    AlreadyLoaded(PathBuf),
}

enum ReloadOutcome {
    Reloaded {
        entity_count: usize,
        system_count: usize,
        cleared_artifacts: usize,
    },
    NothingLoaded,
    TargetNotLoaded(PathBuf),
}

/// Merge declarations from `src` into `dst`, printing warnings for redefinitions.
fn merge_overlay(dst: &mut Env, src: &Env) {
    // Module-level metadata: known_modules, use_decls, decls registry.
    // These feed build_working_namespace() and resolve_use_declarations().
    dst.known_modules.extend(src.known_modules.iter().cloned());
    dst.use_decls.extend(src.use_decls.iter().cloned());
    for (key, info) in &src.decls {
        if dst.decls.contains_key(key) {
            let bare = key.rsplit("::").next().unwrap_or(key);
            println!("  warning: redefining '{bare}'");
        }
        dst.decls.insert(key.clone(), info.clone());
    }

    for (name, ty) in &src.types {
        if dst.types.contains_key(name) {
            println!("  warning: redefining type '{name}'");
        }
        dst.types.insert(name.clone(), ty.clone());
    }
    for (name, entity) in &src.entities {
        if let Some(existing) = dst.entities.get_mut(name) {
            // Merge entity actions — add new ones, warn on redefinition
            for action in &entity.actions {
                if existing.actions.iter().any(|a| a.name == action.name) {
                    println!("  warning: redefining action '{}.{}'", name, action.name);
                    existing.actions.retain(|a| a.name != action.name);
                }
                existing.actions.push(action.clone());
            }
        } else {
            dst.entities.insert(name.clone(), entity.clone());
        }
    }
    for (name, system) in &src.systems {
        if dst.systems.contains_key(name) {
            println!("  warning: redefining system '{name}'");
        }
        dst.systems.insert(name.clone(), system.clone());
    }
    for (name, pred) in &src.preds {
        if dst.preds.contains_key(name) {
            println!("  warning: redefining pred '{name}'");
        }
        dst.preds.insert(name.clone(), pred.clone());
    }
    for (name, prop) in &src.props {
        if dst.props.contains_key(name) {
            println!("  warning: redefining prop '{name}'");
        }
        dst.props.insert(name.clone(), prop.clone());
    }
    for (name, f) in &src.fns {
        if dst.fns.contains_key(name) {
            println!("  warning: redefining fn '{name}'");
        }
        dst.fns.insert(name.clone(), f.clone());
    }
    for (name, c) in &src.consts {
        if dst.consts.contains_key(name) {
            println!("  warning: redefining const '{name}'");
        }
        dst.consts.insert(name.clone(), c.clone());
    }
    // Verification/proof declarations (Vec-backed, not map-backed).
    for v in &src.verifies {
        if dst.verifies.iter().any(|existing| existing.name == v.name) {
            println!("  warning: redefining verify '{}'", v.name);
            dst.verifies.retain(|existing| existing.name != v.name);
        }
        dst.verifies.push(v.clone());
    }
    for s in &src.scenes {
        if dst.scenes.iter().any(|existing| existing.name == s.name) {
            println!("  warning: redefining scene '{}'", s.name);
            dst.scenes.retain(|existing| existing.name != s.name);
        }
        dst.scenes.push(s.clone());
    }
    for t in &src.theorems {
        if dst.theorems.iter().any(|existing| existing.name == t.name) {
            println!("  warning: redefining theorem '{}'", t.name);
            dst.theorems.retain(|existing| existing.name != t.name);
        }
        dst.theorems.push(t.clone());
    }
    for a in &src.axioms {
        if dst.axioms.iter().any(|existing| existing.name == a.name) {
            println!("  warning: redefining axiom '{}'", a.name);
            dst.axioms.retain(|existing| existing.name != a.name);
        }
        dst.axioms.push(a.clone());
    }
    for l in &src.lemmas {
        if dst.lemmas.iter().any(|existing| existing.name == l.name) {
            println!("  warning: redefining lemma '{}'", l.name);
            dst.lemmas.retain(|existing| existing.name != l.name);
        }
        dst.lemmas.push(l.clone());
    }
}

/// Run the interactive REPL.
#[allow(clippy::single_match_else)]
pub fn run_repl(load_path: Option<&Path>, scratch: bool, vi_mode: bool) {
    let (loaded_targets, base_env) = initialize_repl(load_path, scratch);
    let mut state = ReplState::new(loaded_targets, base_env);
    let mut mode = Mode::Abide;
    let mut line_editor = create_line_editor(mode, &state, vi_mode);
    line_editor = install_history(line_editor);
    println!("Abide REPL (type /help for commands, /quit to exit)");
    println!();
    run_repl_loop(line_editor, &mut mode, &mut state);
}

fn initialize_repl(load_path: Option<&Path>, scratch: bool) -> (Vec<PathBuf>, Option<Env>) {
    let startup_targets = determine_startup_targets(load_path, scratch);
    if let Some(targets) = startup_targets {
        match load_base_envs(&targets) {
            Ok(env) => {
                let entity_count = env.entities.len();
                let system_count = env.systems.len();
                println!("Loaded {entity_count} entities, {system_count} systems");
                (targets, Some(env))
            }
            Err(errors) => {
                for e in &errors {
                    eprintln!("{e}");
                }
                (Vec::new(), None)
            }
        }
    } else {
        println!("No specs loaded. Use /load <path> to load specifications.");
        (Vec::new(), None)
    }
}

fn create_line_editor(mode: Mode, state: &ReplState, vi_mode: bool) -> Reedline {
    let completer = Box::new(AbideCompleter::new(
        mode,
        state.model.as_ref(),
        &state.env_names,
    ));
    let completion_menu = Box::new(ColumnarMenu::default().with_name("completion_menu"));
    let mut keybindings = default_emacs_keybindings();
    keybindings.add_binding(
        KeyModifiers::NONE,
        KeyCode::Tab,
        ReedlineEvent::UntilFound(vec![
            ReedlineEvent::Menu("completion_menu".to_owned()),
            ReedlineEvent::MenuNext,
        ]),
    );

    let edit_mode: Box<dyn EditMode> = if vi_mode {
        Box::new(reedline::Vi::default())
    } else {
        Box::new(Emacs::new(keybindings))
    };
    Reedline::create()
        .with_completer(completer)
        .with_menu(ReedlineMenu::EngineCompleter(completion_menu))
        .with_edit_mode(edit_mode)
}

fn install_history(mut line_editor: Reedline) -> Reedline {
    if let Some(history_path) = history_file_path() {
        if let Some(parent) = history_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        if let Ok(history) = reedline::FileBackedHistory::with_file(1000, history_path) {
            line_editor = line_editor.with_history(Box::new(history));
        }
    }
    line_editor
}

fn run_repl_loop(mut line_editor: Reedline, mode: &mut Mode, state: &mut ReplState) {
    let mut input_buffer = String::new();
    loop {
        let prompt = if input_buffer.is_empty() {
            make_prompt(*mode)
        } else {
            make_continuation_prompt()
        };
        match line_editor.read_line(&prompt) {
            Ok(Signal::Success(line)) => {
                match handle_repl_success_line(mode, state, &mut input_buffer, &line) {
                    ReplLineAction::Continue => {}
                    ReplLineAction::Quit => break,
                    ReplLineAction::RefreshCompleter => {
                        line_editor = with_repl_completer(line_editor, *mode, state);
                    }
                }
            }
            Ok(Signal::CtrlD | Signal::CtrlC) => {
                if input_buffer.is_empty() {
                    println!("Goodbye.");
                    break;
                }
                input_buffer.clear();
                println!("(input cleared)");
            }
            Err(e) => {
                eprintln!("Error: {e}");
                break;
            }
        }
    }
}

enum ReplLineAction {
    Continue,
    Quit,
    RefreshCompleter,
}

fn handle_repl_success_line(
    mode: &mut Mode,
    state: &mut ReplState,
    input_buffer: &mut String,
    line: &str,
) -> ReplLineAction {
    let trimmed = line.trim();
    if trimmed.is_empty() && input_buffer.is_empty() {
        return ReplLineAction::Continue;
    }
    if input_buffer.is_empty() && trimmed.starts_with('/') {
        return handle_repl_tool_result(mode, state, trimmed);
    }
    if !input_buffer.is_empty() {
        input_buffer.push('\n');
    }
    input_buffer.push_str(line);
    if !is_balanced(input_buffer) {
        return ReplLineAction::Continue;
    }
    let full_input = input_buffer.trim().to_owned();
    input_buffer.clear();
    execute_repl_input(&full_input, *mode, state);
    ReplLineAction::Continue
}

fn handle_repl_tool_result(
    mode: &mut Mode,
    state: &mut ReplState,
    trimmed: &str,
) -> ReplLineAction {
    match handle_tool_command(trimmed, mode, state) {
        ToolResult::Continue => ReplLineAction::Continue,
        ToolResult::Quit => ReplLineAction::Quit,
        ToolResult::UpdateCompleter => ReplLineAction::RefreshCompleter,
    }
}

fn with_repl_completer(line_editor: Reedline, mode: Mode, state: &ReplState) -> Reedline {
    let new_completer = Box::new(AbideCompleter::new(
        mode,
        state.model.as_ref(),
        &state.env_names,
    ));
    line_editor.with_completer(new_completer)
}

fn execute_repl_input(full_input: &str, mode: Mode, state: &mut ReplState) {
    match mode {
        Mode::QA => handle_qa_input(full_input, state.model.as_ref(), Some(&state.merged_env())),
        Mode::Abide => handle_abide_input(full_input, state),
    }
}

enum ToolResult {
    Continue,
    Quit,
    UpdateCompleter,
}

fn handle_tool_command(cmd: &str, mode: &mut Mode, state: &mut ReplState) -> ToolResult {
    let trimmed = cmd.trim();
    if let Some(result) = handle_session_command(trimmed, mode) {
        return result;
    }
    if let Some(result) = handle_load_command(trimmed, state) {
        return result;
    }
    if let Some(result) = handle_execution_command(trimmed, state) {
        return result;
    }
    if let Some(result) = handle_artifact_command(trimmed, state) {
        return result;
    }
    if trimmed == "/schema" {
        print_schema(state);
        return ToolResult::Continue;
    }
    println!("Unknown command: {cmd}. Type /help for available commands.");
    ToolResult::Continue
}

fn handle_session_command(trimmed: &str, mode: &mut Mode) -> Option<ToolResult> {
    match trimmed {
        "/quit" | "/q" => Some(ToolResult::Quit),
        "/help" | "/h" => {
            print_help(*mode);
            Some(ToolResult::Continue)
        }
        "/qa" => {
            *mode = Mode::QA;
            println!("Switched to QA mode.");
            Some(ToolResult::UpdateCompleter)
        }
        "/abide" => {
            *mode = Mode::Abide;
            println!("Switched to Abide mode.");
            Some(ToolResult::UpdateCompleter)
        }
        _ => None,
    }
}

fn handle_load_command(trimmed: &str, state: &mut ReplState) -> Option<ToolResult> {
    if trimmed.starts_with("/load") {
        load_target(trimmed, state);
        return Some(ToolResult::UpdateCompleter);
    }
    if trimmed.starts_with("/reload") {
        reload_targets(trimmed, state);
        return Some(ToolResult::UpdateCompleter);
    }
    None
}

fn load_target(trimmed: &str, state: &mut ReplState) {
    match parse_target_command(trimmed, "/load") {
        Ok(target) => match state.add_loaded_target(target) {
            Ok(LoadTargetOutcome::Loaded {
                target,
                entity_count,
                system_count,
                cleared_artifacts,
            }) => {
                println!(
                    "Loaded {}. Current base set: {} ({entity_count} entities, {system_count} systems)",
                    target.display(),
                    state.loaded_target_display()
                );
                print_invalidated_artifacts(cleared_artifacts);
            }
            Ok(LoadTargetOutcome::AlreadyLoaded(target)) => {
                println!(
                    "Target `{}` is already loaded. Use `/reload` or `/reload {}`.",
                    target.display(),
                    target.display()
                );
            }
            Err(errors) => print_load_errors(&errors),
        },
        Err(err) => println!("{err}"),
    }
}

fn reload_targets(trimmed: &str, state: &mut ReplState) {
    let target = match parse_optional_target_command(trimmed, "/reload") {
        Ok(target) => target,
        Err(err) => {
            println!("{err}");
            return;
        }
    };
    match state.reload_targets(target.as_deref()) {
        Ok(ReloadOutcome::Reloaded {
            entity_count,
            system_count,
            cleared_artifacts,
        }) => {
            println!(
                "Reloaded: {} ({entity_count} entities, {system_count} systems; in-memory changes discarded)",
                state.loaded_target_display()
            );
            print_invalidated_artifacts(cleared_artifacts);
        }
        Ok(ReloadOutcome::NothingLoaded) => {
            println!("Nothing to reload — no specs are currently loaded.");
        }
        Ok(ReloadOutcome::TargetNotLoaded(target)) => {
            println!(
                "Target `{}` is not currently loaded. Use `/load {}` first.",
                target.display(),
                target.display()
            );
        }
        Err(errors) => print_load_errors(&errors),
    }
}

fn print_load_errors(errors: &[String]) {
    for error in errors {
        eprintln!("{error}");
    }
}

fn print_invalidated_artifacts(cleared_artifacts: usize) {
    if cleared_artifacts > 0 {
        println!("Invalidated {cleared_artifacts} stored artifacts.");
    }
}

fn handle_execution_command(trimmed: &str, state: &mut ReplState) -> Option<ToolResult> {
    if is_tool_command(trimmed, "/verify") {
        verify_current(trimmed, state);
        return Some(ToolResult::Continue);
    }
    if is_tool_command(trimmed, "/run") || is_tool_command(trimmed, "/simulate") {
        simulate_current(trimmed, state);
        return Some(ToolResult::Continue);
    }
    if trimmed.starts_with("/explore") {
        explore_current(trimmed, state);
        return Some(ToolResult::Continue);
    }
    None
}

fn verify_current(trimmed: &str, state: &mut ReplState) {
    let target_text = trimmed.strip_prefix("/verify").unwrap_or_default().trim();
    let target = if target_text.is_empty() {
        Ok(None)
    } else {
        target_text.parse().map(Some)
    };
    match target {
        Ok(target) => match state.verify_current(target) {
            Ok((results, stored)) => {
                for result in &results {
                    println!("{result}");
                }
                print_stored_evidence_count(stored);
            }
            Err(err) => println!("Cannot verify current REPL environment: {err}"),
        },
        Err(err) => println!("Invalid verification target: {err}"),
    }
}

fn print_stored_evidence_count(stored: usize) {
    if stored == 0 {
        println!("No native evidence artifacts were produced.");
    } else {
        println!("Stored {stored} native evidence artifact(s).");
    }
}

fn simulate_current(trimmed: &str, state: &mut ReplState) {
    match parse_run_command(trimmed) {
        Ok(config) => match state.simulate_current(&config) {
            Ok((result, stored)) => {
                print!("{}", result.render_text());
                println!("Stored {stored} simulation artifact(s).");
            }
            Err(err) => println!("Cannot simulate current REPL environment: {err}"),
        },
        Err(err) => println!("{err}"),
    }
}

fn explore_current(trimmed: &str, state: &mut ReplState) {
    match parse_explore_command(trimmed) {
        Ok(request) => match state.explore_current(&request) {
            Ok((result, stored)) => {
                print!("{}", crate::qa::runner::render_state_space_summary(&result));
                println!("Stored {stored} state-space artifact(s).");
            }
            Err(err) => println!("Cannot explore current REPL environment: {err}"),
        },
        Err(err) => println!("{err}"),
    }
}

fn handle_artifact_command(trimmed: &str, state: &ReplState) -> Option<ToolResult> {
    if trimmed == "/artifacts" {
        print_artifact_list(state);
    } else if trimmed.starts_with("/show artifact ") {
        show_artifact(trimmed, state);
    } else if trimmed.starts_with("/draw artifact ") {
        draw_artifact(trimmed, state);
    } else if trimmed.starts_with("/state artifact ") {
        show_artifact_state(trimmed, state);
    } else if trimmed.starts_with("/diff artifact ") {
        diff_artifact(trimmed, state);
    } else if trimmed.starts_with("/export artifact ") {
        export_artifact(trimmed, state);
    } else {
        return None;
    }
    Some(ToolResult::Continue)
}

fn print_artifact_list(state: &ReplState) {
    if state.artifacts.is_empty() {
        println!("No stored artifacts.");
    } else {
        for artifact in state.artifacts.artifacts() {
            println!("{}", artifact.summary_line());
        }
    }
}

fn show_artifact(trimmed: &str, state: &ReplState) {
    match parse_artifact_selector(trimmed, "/show artifact ") {
        Ok(selector) => match state.artifacts.resolve(&selector) {
            Some(artifact) => print!("{}", artifact.render_show()),
            None => println!("Unknown artifact selector `{selector}`."),
        },
        Err(err) => println!("{err}"),
    }
}

fn draw_artifact(trimmed: &str, state: &ReplState) {
    match parse_artifact_selector(trimmed, "/draw artifact ") {
        Ok(selector) => match state.artifacts.resolve(&selector) {
            Some(artifact) => match artifact.render_draw() {
                Ok(rendered) => print!("{rendered}"),
                Err(err) => println!("{err}"),
            },
            None => println!("Unknown artifact selector `{selector}`."),
        },
        Err(err) => println!("{err}"),
    }
}

fn show_artifact_state(trimmed: &str, state: &ReplState) {
    match parse_artifact_state_args(trimmed, "/state artifact ") {
        Ok((selector, index)) => match state.artifacts.resolve(&selector) {
            Some(artifact) => match artifact.render_state(index) {
                Ok(rendered) => print!("{rendered}"),
                Err(err) => println!("{err}"),
            },
            None => println!("Unknown artifact selector `{selector}`."),
        },
        Err(err) => println!("{err}"),
    }
}

fn diff_artifact(trimmed: &str, state: &ReplState) {
    match parse_artifact_diff_args(trimmed, "/diff artifact ") {
        Ok((selector, from, to)) => match state.artifacts.resolve(&selector) {
            Some(artifact) => match artifact.render_diff(from, to) {
                Ok(rendered) => print!("{rendered}"),
                Err(err) => println!("{err}"),
            },
            None => println!("Unknown artifact selector `{selector}`."),
        },
        Err(err) => println!("{err}"),
    }
}

fn export_artifact(trimmed: &str, state: &ReplState) {
    match parse_artifact_export_args(trimmed, "/export artifact ") {
        Ok((selector, format)) => match state.artifacts.resolve(&selector) {
            Some(artifact) => export_resolved_artifact(artifact, &format),
            None => println!("Unknown artifact selector `{selector}`."),
        },
        Err(err) => println!("{err}"),
    }
}

fn export_resolved_artifact(artifact: &ReplArtifact, format: &str) {
    if format == "json" {
        match artifact.export_json() {
            Ok(json) => println!("{json}"),
            Err(err) => println!("{err}"),
        }
    } else {
        println!("Unsupported export format `{format}`. Use `json`.");
    }
}

fn print_schema(state: &ReplState) {
    if let Some(m) = &state.model {
        println!("Entities: {}", m.entity_names.join(", "));
        println!(
            "Systems: {}",
            m.systems.keys().cloned().collect::<Vec<_>>().join(", ")
        );
        println!("Types: {}", m.type_names.join(", "));
        for ((entity, field), sg) in &m.state_graphs {
            println!(
                "  {entity}.{field}: {} (initial: {})",
                sg.states.join(" | "),
                sg.initial.as_deref().unwrap_or("?")
            );
        }
    } else {
        println!("No specs loaded.");
    }
}

fn handle_qa_input(input: &str, model: Option<&FlowModel>, env: Option<&Env>) {
    let Some(model) = model else {
        println!("No specs loaded. Use /load <path> or restart with a path argument.");
        return;
    };
    match qa_parse::parse_statement(input, 1) {
        Ok(stmt) => {
            let (verb, result) = exec::execute_statement_with_env(model, env, &stmt);
            println!("{}", fmt::format_result(verb, &result));
        }
        Err(e) => eprintln!("  {e}"),
    }
}

fn handle_abide_input(input: &str, state: &mut ReplState) {
    match crate::parse::parse_string_recovering(input) {
        Ok(parsed) => {
            if !parsed.errors.is_empty() {
                for err in &parsed.errors {
                    eprintln!("  parse error: {err}");
                }
                return;
            }
            if parsed.program.decls.is_empty() {
                println!("  (no declarations)");
                return;
            }
            for decl in &parsed.program.decls {
                println!("  OK: {decl:?}");
            }
            // Add to overlay and rebuild FlowModel
            let cleared = state.invalidate_artifacts();
            state.add_overlay(&parsed.program);
            println!("  (added to in-memory environment)");
            if cleared > 0 {
                println!("  (invalidated {cleared} stored artifacts)");
            }
        }
        Err(errors) => {
            for err in errors {
                eprintln!("  lex error: {err}");
            }
        }
    }
}

/// Check if braces `{}` and parens `()` are balanced in the input.
/// Handles string literals (with `\"` escapes) and `//` line comments.
/// Returns true if balanced (ready to execute), false if more input needed.
fn is_balanced(input: &str) -> bool {
    let mut brace_depth: i32 = 0;
    let mut paren_depth: i32 = 0;
    let mut in_string = false;
    let mut prev_char = '\0';
    let mut in_comment = false;

    for ch in input.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev_char = ch;
            continue;
        }
        if in_string {
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
            prev_char = ch;
            continue;
        }
        match ch {
            '/' if prev_char == '/' => {
                in_comment = true;
            }
            '"' => in_string = true,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }
    brace_depth <= 0 && paren_depth <= 0
}

fn make_continuation_prompt() -> DefaultPrompt {
    DefaultPrompt::new(
        DefaultPromptSegment::Basic(".....".to_owned()),
        DefaultPromptSegment::Empty,
    )
}

fn is_tool_command(input: &str, command: &str) -> bool {
    input == command
        || input
            .strip_prefix(command)
            .is_some_and(|rest| rest.starts_with(char::is_whitespace))
}

fn print_help(mode: Mode) {
    println!("Tool commands:");
    println!("  /help, /h     Show this help");
    println!("  /quit, /q     Exit the REPL");
    println!("  /qa           Switch to QA mode");
    println!("  /abide        Switch to Abide mode");
    println!("  /load <path>  Load a file or directory into the current base set");
    println!("  /reload       Reload specs from disk");
    println!("  /reload <path>  Reload a specific loaded target");
    println!("  /verify       Run verification on the current in-memory environment");
    println!("  /run [options]       Run one seeded forward simulation");
    println!("  /simulate [options]  Alias for /run");
    println!("  /explore [options]   Build a bounded composite state-space artifact");
    println!("  /artifacts    List stored native evidence, simulation, and state-space artifacts");
    println!("  /show artifact <selector>        Show artifact metadata and summary");
    println!("  /draw artifact <selector>        Draw artifact timeline when available");
    println!("  /state artifact <selector> <n>   Show a specific artifact state");
    println!("  /diff artifact <selector> <a> <b>  Diff two artifact states");
    println!("  /export artifact <selector> json   Print raw artifact JSON");
    println!("  /schema       Show loaded entities, systems, and state graphs");
    println!();
    match mode {
        Mode::QA => {
            println!("QA commands:");
            println!("  ask <query>       Query and print result");
            println!("  explain <query>   Query with reasoning");
            println!("  assert <query>    Query, print PASS/FAIL");
            println!();
            println!("Queries: reachable, path, terminal, initial, cycles,");
            println!("  transitions, entities, systems, types, invariants,");
            println!("  contracts, events, match-coverage, cross-calls,");
            println!("  updates, deadlock, always, eventually, not");
        }
        Mode::Abide => {
            println!("Abide mode: enter definitions or expressions to evaluate.");
            println!("Definitions are in-memory only — /reload discards them.");
        }
    }
}

fn make_prompt(mode: Mode) -> DefaultPrompt {
    let segment = match mode {
        Mode::Abide => DefaultPromptSegment::Basic("abide".to_owned()),
        Mode::QA => DefaultPromptSegment::Basic("qa".to_owned()),
    };
    DefaultPrompt::new(segment, DefaultPromptSegment::Empty)
}

fn parse_run_command(cmd: &str) -> Result<SimulateConfig, String> {
    let (command, rest) = if let Some(rest) = cmd.strip_prefix("/run") {
        ("/run", rest.trim())
    } else if let Some(rest) = cmd.strip_prefix("/simulate") {
        ("/simulate", rest.trim())
    } else {
        return Err("internal run command parse error".to_owned());
    };
    let mut config = SimulateConfig::default();
    if rest.is_empty() {
        return Ok(config);
    }

    let usage = format!(
        "Usage: {command} [--steps N] [--seed N] [--slots N] [--scope Entity=N]... [--system NAME]"
    );
    let tokens: Vec<&str> = rest.split_whitespace().collect();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index] {
            "--steps" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.clone())?;
                config.steps = value.parse::<usize>().map_err(|_| {
                    format!("invalid `{command} --steps {value}`; expected a non-negative integer")
                })?;
                index += 2;
            }
            "--seed" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.clone())?;
                config.seed = value.parse::<u64>().map_err(|_| {
                    format!("invalid `{command} --seed {value}`; expected a non-negative integer")
                })?;
                index += 2;
            }
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.clone())?;
                config.slots_per_entity = value.parse::<usize>().map_err(|_| {
                    format!("invalid `{command} --slots {value}`; expected a non-negative integer")
                })?;
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.clone())?;
                let (entity, slots_text) = value.split_once('=').ok_or_else(|| {
                    format!("invalid `{command} --scope {value}`; expected `Entity=N`")
                })?;
                if entity.trim().is_empty() {
                    return Err(format!(
                        "invalid `{command} --scope {value}`; entity name must not be empty"
                    ));
                }
                let slots = slots_text.parse::<usize>().map_err(|_| {
                    format!(
                        "invalid `{command} --scope {value}`; slot count must be a non-negative integer"
                    )
                })?;
                config
                    .entity_slot_overrides
                    .insert(entity.to_owned(), slots);
                index += 2;
            }
            "--system" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.clone())?;
                config.system = Some((*value).to_owned());
                index += 2;
            }
            other => {
                return Err(format!(
                    "unknown `{command}` option `{other}`; expected --steps, --seed, --slots, --scope, or --system"
                ));
            }
        }
    }
    Ok(config)
}

fn parse_explore_command(cmd: &str) -> Result<StateSpaceRequest, String> {
    let rest = cmd
        .strip_prefix("/explore")
        .ok_or_else(|| "internal explore command parse error".to_owned())?
        .trim();
    let mut request = StateSpaceRequest::default();
    if rest.is_empty() {
        return Ok(request);
    }

    let usage = "Usage: /explore [--depth N] [--slots N] [--scope Entity=N]... [--system NAME]";
    let tokens: Vec<&str> = rest.split_whitespace().collect();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index] {
            "--depth" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.to_owned())?;
                request.depth = Some(value.parse::<usize>().map_err(|_| {
                    format!("invalid `/explore --depth {value}`; expected a non-negative integer")
                })?);
                index += 2;
            }
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.to_owned())?;
                request.slots = value.parse::<usize>().map_err(|_| {
                    format!("invalid `/explore --slots {value}`; expected a non-negative integer")
                })?;
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.to_owned())?;
                let (entity, slots_text) = value.split_once('=').ok_or_else(|| {
                    format!("invalid `/explore --scope {value}`; expected `Entity=N`")
                })?;
                if entity.trim().is_empty() {
                    return Err(format!(
                        "invalid `/explore --scope {value}`; entity name must not be empty"
                    ));
                }
                let slots = slots_text.parse::<usize>().map_err(|_| {
                    format!(
                        "invalid `/explore --scope {value}`; slot count must be a non-negative integer"
                    )
                })?;
                request.scopes.push((entity.to_owned(), slots));
                index += 2;
            }
            "--system" => {
                let value = tokens.get(index + 1).ok_or_else(|| usage.to_owned())?;
                request.system = Some((*value).to_owned());
                index += 2;
            }
            other => {
                return Err(format!(
                    "unknown `/explore` option `{other}`; expected --depth, --slots, --scope, or --system"
                ));
            }
        }
    }
    Ok(request)
}

fn load_base_envs(targets: &[PathBuf]) -> Result<Env, Vec<String>> {
    let paths =
        crate::targets::resolve_source_targets(targets).map_err(|error| vec![error.to_string()])?;

    let (mut env, load_errors, _) = loader::load_files(&paths);
    if !load_errors.is_empty() {
        return Err(load_errors.iter().map(|e| format!("{e}")).collect());
    }

    // Include-level load errors (lex/parse/IO in transitively included files)
    // must block REPL startup — a partial environment gives wrong results.
    if !env.include_load_errors.is_empty() {
        return Err(env
            .include_load_errors
            .iter()
            .map(|e| format!("{e}"))
            .collect());
    }

    // When loading from a directory (multiple files), don't privilege any
    // single file's module as root. Clear module_name so
    // build_working_namespace includes all modules.
    if paths.len() > 1 {
        env.module_name = None;
    }

    Ok(env)
}

fn resolve_single_source_target(path: &Path) -> Result<Vec<PathBuf>, Vec<String>> {
    crate::targets::resolve_source_targets(&[path.to_path_buf()])
        .map_err(|error| vec![error.to_string()])
}

fn normalize_target(path: &Path) -> Result<PathBuf, String> {
    std::fs::canonicalize(path).map_err(|_| format!("path not found: {}", path.display()))
}

fn determine_startup_targets(load_path: Option<&Path>, scratch: bool) -> Option<Vec<PathBuf>> {
    if scratch {
        return None;
    }
    if let Some(path) = load_path {
        return normalize_target(path).ok().map(|path| vec![path]);
    }

    let cwd = std::env::current_dir().ok()?;
    determine_startup_targets_in_dir(&cwd)
}

fn determine_startup_targets_in_dir(dir: &Path) -> Option<Vec<PathBuf>> {
    if crate::targets::directory_contains_source_files(dir) {
        Some(vec![dir.to_path_buf()])
    } else {
        None
    }
}

fn parse_target_command(cmd: &str, prefix: &str) -> Result<PathBuf, String> {
    let rest = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?
        .trim();
    if rest.is_empty() {
        return Err(format!("Usage: {prefix} <path>"));
    }
    normalize_target(Path::new(rest))
}

fn parse_optional_target_command(cmd: &str, prefix: &str) -> Result<Option<PathBuf>, String> {
    let rest = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?
        .trim();
    if rest.is_empty() {
        Ok(None)
    } else {
        normalize_target(Path::new(rest)).map(Some)
    }
}

fn history_file_path() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME")
        .map(PathBuf::from)
        .map(|h| h.join(".abide").join("repl_history"))
}

fn parse_artifact_selector(cmd: &str, prefix: &str) -> Result<String, String> {
    let selector = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?
        .trim();
    if selector.is_empty() || selector.contains(char::is_whitespace) {
        return Err(format!(
            "Usage: {prefix}<selector>  (selector = id | name | kind:name)"
        ));
    }
    Ok(selector.to_owned())
}

fn parse_artifact_state_args(cmd: &str, prefix: &str) -> Result<(String, usize), String> {
    let rest = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?;
    let mut parts = rest.split_whitespace();
    let selector = parts
        .next()
        .ok_or_else(|| "Usage: /state artifact <selector> <index>".to_owned())?;
    let index = parts
        .next()
        .ok_or_else(|| "Usage: /state artifact <selector> <index>".to_owned())?;
    if parts.next().is_some() {
        return Err("Usage: /state artifact <selector> <index>".to_owned());
    }
    Ok((
        selector.to_owned(),
        index
            .parse::<usize>()
            .map_err(|_| format!("Invalid state index `{index}`."))?,
    ))
}

fn parse_artifact_diff_args(cmd: &str, prefix: &str) -> Result<(String, usize, usize), String> {
    let rest = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?;
    let mut parts = rest.split_whitespace();
    let selector = parts
        .next()
        .ok_or_else(|| "Usage: /diff artifact <selector> <from> <to>".to_owned())?;
    let from = parts
        .next()
        .ok_or_else(|| "Usage: /diff artifact <selector> <from> <to>".to_owned())?;
    let to = parts
        .next()
        .ok_or_else(|| "Usage: /diff artifact <selector> <from> <to>".to_owned())?;
    if parts.next().is_some() {
        return Err("Usage: /diff artifact <selector> <from> <to>".to_owned());
    }
    Ok((
        selector.to_owned(),
        from.parse::<usize>()
            .map_err(|_| format!("Invalid state index `{from}`."))?,
        to.parse::<usize>()
            .map_err(|_| format!("Invalid state index `{to}`."))?,
    ))
}

fn parse_artifact_export_args(cmd: &str, prefix: &str) -> Result<(String, String), String> {
    let rest = cmd
        .strip_prefix(prefix)
        .ok_or_else(|| "internal command parse error".to_owned())?;
    let mut parts = rest.split_whitespace();
    let selector = parts
        .next()
        .ok_or_else(|| "Usage: /export artifact <selector> <format>".to_owned())?;
    let format = parts
        .next()
        .ok_or_else(|| "Usage: /export artifact <selector> <format>".to_owned())?;
    if parts.next().is_some() {
        return Err("Usage: /export artifact <selector> <format>".to_owned());
    }
    Ok((selector.to_owned(), format.to_owned()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn write_file(path: &Path, contents: &str) {
        fs::write(path, contents).expect("write test file");
    }

    fn simple_spec() -> &'static str {
        "module Test\n\nenum Status = Pending | Done\n\nentity Order {\n  id: identity\n  status: Status = @Pending\n}\n"
    }

    #[test]
    fn startup_targets_respect_scratch() {
        let dir = TempDir::new().expect("tempdir");
        write_file(&dir.path().join("spec.ab"), simple_spec());
        let targets = determine_startup_targets(Some(dir.path()), true);
        assert!(targets.is_none());
    }

    #[test]
    fn startup_targets_use_current_directory_when_abide_files_exist() {
        let dir = TempDir::new().expect("tempdir");
        write_file(&dir.path().join("spec.ab"), simple_spec());
        let targets = determine_startup_targets_in_dir(dir.path()).expect("startup targets");
        assert_eq!(targets, vec![dir.path().to_path_buf()]);
    }

    #[test]
    fn parse_target_command_requires_path() {
        let err = parse_target_command("/load", "/load").expect_err("missing path");
        assert!(err.contains("Usage: /load <path>"));
    }

    #[test]
    fn parse_run_command_supports_run_and_simulate_aliases() {
        let run = parse_run_command(
            "/run --steps 5 --seed 7 --slots 2 --scope Order=3 --system Commerce",
        )
        .expect("parse run");
        assert_eq!(run.steps, 5);
        assert_eq!(run.seed, 7);
        assert_eq!(run.slots_per_entity, 2);
        assert_eq!(run.entity_slot_overrides.get("Order"), Some(&3));
        assert_eq!(run.system.as_deref(), Some("Commerce"));

        let simulate = parse_run_command("/simulate --steps 8").expect("parse simulate");
        assert_eq!(simulate.steps, 8);
    }

    #[test]
    fn tool_command_matching_requires_exact_command_boundary() {
        assert!(is_tool_command("/run", "/run"));
        assert!(is_tool_command("/run --steps 1", "/run"));
        assert!(!is_tool_command("/runner", "/run"));
    }

    #[test]
    fn add_loaded_target_is_noop_when_target_files_are_already_loaded() {
        let dir = TempDir::new().expect("tempdir");
        let subdir = dir.path().join("specs");
        fs::create_dir_all(&subdir).expect("create specs dir");
        let spec = subdir.join("spec.ab");
        write_file(&spec, simple_spec());

        let initial_target = normalize_target(&subdir).expect("normalize dir");
        let env = load_base_envs(std::slice::from_ref(&initial_target)).expect("load base env");
        let mut state = ReplState::new(vec![initial_target], Some(env));

        let file_target = normalize_target(&spec).expect("normalize file");
        match state
            .add_loaded_target(file_target.clone())
            .expect("load target outcome")
        {
            LoadTargetOutcome::AlreadyLoaded(path) => assert_eq!(path, file_target),
            LoadTargetOutcome::Loaded { .. } => panic!("expected already loaded outcome"),
        }
    }

    #[test]
    fn reload_specific_target_requires_it_to_be_loaded() {
        let dir = TempDir::new().expect("tempdir");
        let spec = dir.path().join("spec.ab");
        write_file(&spec, simple_spec());
        let normalized_spec = normalize_target(&spec).expect("normalize spec");
        let env = load_base_envs(std::slice::from_ref(&normalized_spec)).expect("load base env");
        let mut state = ReplState::new(vec![normalized_spec], Some(env));

        let other = dir.path().join("other.ab");
        write_file(&other, simple_spec());
        match state.reload_targets(Some(&other)).expect("reload outcome") {
            ReloadOutcome::TargetNotLoaded(path) => {
                assert_eq!(path, normalize_target(&other).expect("normalize other"));
            }
            ReloadOutcome::Reloaded { .. } | ReloadOutcome::NothingLoaded => {
                panic!("expected target-not-loaded outcome")
            }
        }
    }

    #[test]
    fn parse_explore_command_supports_bounds() {
        let request =
            parse_explore_command("/explore --depth 5 --slots 2 --scope Order=3 --system Commerce")
                .expect("parse explore");
        assert_eq!(request.depth, Some(5));
        assert_eq!(request.slots, 2);
        assert_eq!(request.scopes, vec![("Order".to_owned(), 3)]);
        assert_eq!(request.system.as_deref(), Some("Commerce"));
    }
}
