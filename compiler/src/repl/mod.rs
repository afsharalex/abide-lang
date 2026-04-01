//! `abide repl` — interactive evaluation environment.
//!
//! Two modes: Abide (default) for spec definitions, QA for structural queries.
//! Mode switching via `/qa` and `/abide` commands.

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
use crate::qa::model::FlowModel;
use crate::qa::{exec, extract, fmt, parse as qa_parse};

use complete::AbideCompleter;

/// REPL mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Abide,
    QA,
}

/// Live REPL state: base env from disk + overlay from REPL input.
struct ReplState {
    /// Base environment loaded from disk (restored on /reload).
    base_env: Option<Env>,
    /// Overlay definitions entered in the REPL.
    overlay_env: Env,
    /// Current `FlowModel` (rebuilt after changes).
    model: Option<FlowModel>,
    /// Names for tab completion.
    env_names: Vec<String>,
}

impl ReplState {
    fn new(base_env: Option<Env>) -> Self {
        let mut state = Self {
            base_env,
            overlay_env: Env::new(),
            model: None,
            env_names: Vec::new(),
        };
        state.rebuild();
        state
    }

    /// Merge base + overlay, elaborate, lower, and rebuild the flow model.
    fn rebuild(&mut self) {
        let env = match &self.base_env {
            Some(base) => {
                let mut merged = base.clone();
                merge_overlay(&mut merged, &self.overlay_env);
                merged
            }
            None => self.overlay_env.clone(),
        };

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

        let ir_program = ir::lower(&result);
        self.model = Some(extract::extract(&ir_program));
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
}

/// Merge declarations from `src` into `dst`, printing warnings for redefinitions.
fn merge_overlay(dst: &mut Env, src: &Env) {
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
}

/// Run the interactive REPL.
#[allow(clippy::too_many_lines)]
pub fn run_repl(load_path: Option<&Path>, vi_mode: bool) {
    // Load specs if a path was provided
    let base_env = if let Some(path) = load_path {
        match load_base_env(path) {
            Ok(env) => {
                let entity_count = env.entities.len();
                let system_count = env.systems.len();
                println!("Loaded {entity_count} entities, {system_count} systems");
                Some(env)
            }
            Err(errors) => {
                for e in &errors {
                    eprintln!("{e}");
                }
                None
            }
        }
    } else {
        println!("No specs loaded. Use /load <path> to load specifications.");
        None
    };

    let mut state = ReplState::new(base_env);
    let mut mode = Mode::Abide;

    // Set up completer
    let completer = Box::new(AbideCompleter::new(
        mode,
        state.model.as_ref(),
        &state.env_names,
    ));

    // Set up reedline
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

    let mut line_editor = Reedline::create()
        .with_completer(completer)
        .with_menu(ReedlineMenu::EngineCompleter(completion_menu))
        .with_edit_mode(edit_mode);

    // Set up history (create directory if needed)
    if let Some(history_path) = history_file_path() {
        if let Some(parent) = history_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        if let Ok(history) = reedline::FileBackedHistory::with_file(1000, history_path) {
            line_editor = line_editor.with_history(Box::new(history));
        }
    }

    println!("Abide REPL (type /help for commands, /quit to exit)");
    println!();

    let mut input_buffer = String::new();

    loop {
        let prompt = if input_buffer.is_empty() {
            make_prompt(mode)
        } else {
            make_continuation_prompt()
        };

        match line_editor.read_line(&prompt) {
            Ok(Signal::Success(line)) => {
                let trimmed = line.trim();

                // Empty line on fresh prompt: skip. On continuation: submit buffer.
                if trimmed.is_empty() && input_buffer.is_empty() {
                    continue;
                }

                // Handle tool commands (only on fresh prompt)
                if input_buffer.is_empty() && trimmed.starts_with('/') {
                    match handle_tool_command(trimmed, &mut mode, &mut state, load_path) {
                        ToolResult::Continue => continue,
                        ToolResult::Quit => break,
                        ToolResult::UpdateCompleter => {
                            let new_completer = Box::new(AbideCompleter::new(
                                mode,
                                state.model.as_ref(),
                                &state.env_names,
                            ));
                            line_editor = line_editor.with_completer(new_completer);
                            continue;
                        }
                    }
                }

                // Accumulate multi-line input
                if !input_buffer.is_empty() {
                    input_buffer.push('\n');
                }
                input_buffer.push_str(&line);

                // Check if braces/parens are balanced
                if !is_balanced(&input_buffer) {
                    continue;
                }

                let full_input = input_buffer.trim().to_owned();
                input_buffer.clear();

                // Execute based on mode
                match mode {
                    Mode::QA => handle_qa_input(&full_input, state.model.as_ref()),
                    Mode::Abide => handle_abide_input(&full_input, &mut state),
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

enum ToolResult {
    Continue,
    Quit,
    UpdateCompleter,
}

fn handle_tool_command(
    cmd: &str,
    mode: &mut Mode,
    state: &mut ReplState,
    load_path: Option<&Path>,
) -> ToolResult {
    match cmd {
        "/quit" | "/q" => ToolResult::Quit,
        "/help" | "/h" => {
            print_help(*mode);
            ToolResult::Continue
        }
        "/qa" => {
            *mode = Mode::QA;
            println!("Switched to QA mode.");
            ToolResult::UpdateCompleter
        }
        "/abide" => {
            *mode = Mode::Abide;
            println!("Switched to Abide mode.");
            ToolResult::UpdateCompleter
        }
        "/reload" => {
            if let Some(path) = load_path {
                match load_base_env(path) {
                    Ok(env) => {
                        let entity_count = env.entities.len();
                        let system_count = env.systems.len();
                        state.base_env = Some(env);
                        state.reset_overlay();
                        println!("Reloaded: {entity_count} entities, {system_count} systems (in-memory changes discarded)");
                    }
                    Err(errors) => {
                        for e in &errors {
                            eprintln!("{e}");
                        }
                    }
                }
            } else {
                println!("Nothing to reload — no specs were loaded at startup.");
            }
            ToolResult::UpdateCompleter
        }
        "/schema" => {
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
            ToolResult::Continue
        }
        _ => {
            println!("Unknown command: {cmd}. Type /help for available commands.");
            ToolResult::Continue
        }
    }
}

fn handle_qa_input(input: &str, model: Option<&FlowModel>) {
    let Some(model) = model else {
        println!("No specs loaded. Use /load <path> or restart with a path argument.");
        return;
    };
    match qa_parse::parse_statement(input, 1) {
        Ok(stmt) => {
            let (verb, result) = exec::execute_statement(model, &stmt);
            println!("{}", fmt::format_result(verb, &result));
        }
        Err(e) => eprintln!("  {e}"),
    }
}

fn handle_abide_input(input: &str, state: &mut ReplState) {
    match crate::parse::parse_string(input) {
        Ok(program) => {
            if program.decls.is_empty() {
                println!("  (no declarations)");
                return;
            }
            for decl in &program.decls {
                println!("  OK: {decl:?}");
            }
            // Add to overlay and rebuild FlowModel
            state.add_overlay(&program);
            println!("  (added to in-memory environment)");
        }
        Err(e) => eprintln!("  parse error: {e}"),
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

fn print_help(mode: Mode) {
    println!("Tool commands:");
    println!("  /help, /h     Show this help");
    println!("  /quit, /q     Exit the REPL");
    println!("  /qa           Switch to QA mode");
    println!("  /abide        Switch to Abide mode");
    println!("  /reload       Reload specs from disk");
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

/// Load `.abide` files into a raw `Env` (pre-elaboration).
/// The `Env` is used as the base layer for the REPL state.
fn load_base_env(path: &Path) -> Result<Env, Vec<String>> {
    let mut paths = Vec::new();
    if path.is_file() {
        paths.push(path.to_owned());
    } else if path.is_dir() {
        collect_abide_files(path, &mut paths);
    } else {
        return Err(vec![format!("path not found: {}", path.display())]);
    }

    if paths.is_empty() {
        return Err(vec!["no .abide files found".to_owned()]);
    }

    let (env, load_errors, _) = loader::load_files(&paths);
    if !load_errors.is_empty() {
        return Err(load_errors.iter().map(|e| format!("{e}")).collect());
    }

    Ok(env)
}

fn collect_abide_files(dir: &Path, paths: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("abide") {
                paths.push(path);
            } else if path.is_dir() {
                collect_abide_files(&path, paths);
            }
        }
    }
}

fn history_file_path() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME")
        .map(PathBuf::from)
        .map(|h| h.join(".abide").join("repl_history"))
}
