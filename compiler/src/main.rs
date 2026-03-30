use clap::{Parser as ClapParser, Subcommand};
use miette::{IntoDiagnostic, NamedSource, WrapErr};
use std::path::PathBuf;

#[derive(ClapParser)]
#[command(name = "abide", about = "Abide specification language compiler")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Lex a source file and print tokens
    Lex { file: PathBuf },

    /// Parse a source file and print AST
    Parse { file: PathBuf },

    /// Elaborate source file(s) and print result
    Elaborate {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },

    /// Emit IR as JSON
    #[command(name = "emit-ir")]
    EmitIr {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },

    /// Verify a specification: bounded model checking, scene checking, theorem proving
    Verify {
        #[arg(required = true)]
        files: Vec<PathBuf>,

        /// Skip induction (Tier 1), only run bounded model checking
        #[arg(long, conflicts_with = "unbounded_only")]
        bounded_only: bool,

        /// Skip bounded model checking, only try induction
        #[arg(long, conflicts_with = "bounded_only")]
        unbounded_only: bool,

        /// Induction timeout in seconds (default: 5)
        #[arg(long, default_value_t = DEFAULT_INDUCTION_TIMEOUT_SECS)]
        induction_timeout: u64,

        /// BMC timeout in seconds (default: 0 = no timeout)
        #[arg(long, default_value_t = 0)]
        bmc_timeout: u64,

        /// IC3/PDR timeout in seconds (default: 10)
        #[arg(long, default_value_t = DEFAULT_IC3_TIMEOUT_SECS)]
        ic3_timeout: u64,

        /// Skip IC3/PDR verification (for speed)
        #[arg(long)]
        no_ic3: bool,

        /// Skip automatic prop verification
        #[arg(long)]
        no_prop_verify: bool,

        /// Show progress messages during verification
        #[arg(long)]
        progress: bool,
    },
}

/// Default timeout for Tier 1 induction attempts, in seconds.
///
/// Induction is a fixed-size problem (1 transition step). If the solver
/// can't prove the property inductively within this time, it's unlikely
/// to succeed — fall back to bounded model checking.
///
/// Note: this timeout is applied separately to the base case and step case
/// solvers, so the worst-case wall-clock time is approximately 2x this value.
///
/// Configurable via `--induction-timeout` flag. The default of 5 seconds is
/// generous — most inductive invariants solve in under 1 second.
const DEFAULT_INDUCTION_TIMEOUT_SECS: u64 = 5;

/// Default bounded model checking depth for auto-verified props.
///
/// Props don't have an explicit `[0..N]` scope like verify blocks.
/// When induction fails for a prop, the BMC fallback uses this depth.
/// Not yet wired to a CLI flag — will be exposed when prop auto-verification
/// is implemented (Phase 6 deferred item).
const DEFAULT_PROP_BMC_DEPTH: usize = 10;

/// Default timeout for IC3/PDR attempts, in seconds.
///
/// IC3 can take longer than induction because it iteratively discovers
/// strengthening invariants. The default of 10 seconds balances proof
/// power against responsiveness.
const DEFAULT_IC3_TIMEOUT_SECS: u64 = 10;

#[allow(clippy::too_many_lines)]
fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Lex { file } => {
            let src = read_file(&file)?;
            let tokens =
                abide::lex::lex(&src).map_err(|errors| errors.into_iter().next().unwrap())?;
            for (token, span) in &tokens {
                println!("{span:?}  {token}");
            }
        }
        Command::Parse { file } => {
            let src = read_file(&file)?;
            let tokens =
                abide::lex::lex(&src).map_err(|errors| errors.into_iter().next().unwrap())?;
            let mut parser = abide::parse::Parser::new(tokens);
            let (program, parse_errors) = parser.parse_program_recovering();
            if !parse_errors.is_empty() {
                let named = NamedSource::new(file.display().to_string(), src);
                for err in &parse_errors {
                    let report = miette::Report::new(err.clone()).with_source_code(named.clone());
                    eprintln!("{report:?}");
                }
                std::process::exit(1);
            }
            println!("{program:#?}");
        }
        Command::Elaborate { files } => {
            let mut sources = read_sources_for_diagnostics(&files);
            let Some((result, errors)) = load_and_elaborate(&files, &mut sources) else {
                std::process::exit(1);
            };
            report_elab_errors(&errors, &sources);
            if has_errors(&errors) {
                std::process::exit(1);
            }
            println!("{result:#?}");
        }
        Command::EmitIr { files } => {
            let mut sources = read_sources_for_diagnostics(&files);
            let Some((result, errors)) = load_and_elaborate(&files, &mut sources) else {
                std::process::exit(1);
            };
            report_elab_errors(&errors, &sources);
            if has_errors(&errors) {
                std::process::exit(1);
            }
            let ir_program = abide::ir::lower(&result);
            let json = abide::ir::emit_json(&ir_program)
                .into_diagnostic()
                .wrap_err("failed to serialize IR to JSON")?;
            println!("{json}");
        }
        Command::Verify {
            files,
            bounded_only,
            unbounded_only,
            induction_timeout,
            bmc_timeout,
            ic3_timeout,
            no_ic3,
            no_prop_verify,
            progress,
        } => {
            let mut sources = read_sources_for_diagnostics(&files);
            let Some((result, errors)) = load_and_elaborate(&files, &mut sources) else {
                std::process::exit(1);
            };
            report_elab_errors(&errors, &sources);
            if has_errors(&errors) {
                std::process::exit(1);
            }
            let ir_program = abide::ir::lower(&result);

            let config = abide::verify::VerifyConfig {
                bounded_only,
                unbounded_only,
                induction_timeout_ms: induction_timeout.saturating_mul(1000),
                bmc_timeout_ms: bmc_timeout.saturating_mul(1000),
                prop_bmc_depth: DEFAULT_PROP_BMC_DEPTH,
                ic3_timeout_ms: ic3_timeout.saturating_mul(1000),
                no_ic3,
                no_prop_verify,
                progress,
            };

            let results = abide::verify::verify_all(&ir_program, &config);
            if results.is_empty() {
                println!("No verification targets found.");
            } else {
                let mut all_passed = true;
                for r in &results {
                    report_verification_result(r, &sources);
                    if r.is_failure() {
                        all_passed = false;
                    }
                }
                if !all_passed {
                    std::process::exit(1);
                }
            }
        }
    }

    Ok(())
}

fn read_file(path: &PathBuf) -> miette::Result<String> {
    std::fs::read_to_string(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to read {}", path.display()))
}

/// Read source text from all input files for diagnostic rendering.
/// Returns `(filename, source_text)` pairs for matching against error file tags.
fn read_sources_for_diagnostics(paths: &[PathBuf]) -> Vec<(String, String)> {
    paths
        .iter()
        .filter_map(|p| {
            let src = std::fs::read_to_string(p).ok()?;
            // Use canonical path to match loader's canonicalized file tags.
            let key = std::fs::canonicalize(p)
                .map_or_else(|_| p.display().to_string(), |c| c.display().to_string());
            Some((key, src))
        })
        .collect()
}

/// Render elaboration errors with miette source snippets when spans are available.
///
/// Only renders source snippets when the error's file matches the loaded source.
/// Errors from other files (in multi-file mode) fall back to plain text to avoid
/// rendering spans against the wrong source.
/// Returns true if any diagnostics are errors (not warnings).
fn has_errors(errors: &[abide::elab::error::ElabError]) -> bool {
    errors
        .iter()
        .any(|e| e.severity == abide::elab::error::Severity::Error)
}

fn report_elab_errors(errors: &[abide::elab::error::ElabError], sources: &[(String, String)]) {
    let single_file = sources.len() <= 1;
    for err in errors {
        if let Some(span) = err.span {
            // Find the matching source for this error's file
            let matching_source = if let Some(ref file) = err.file {
                sources.iter().find(|(name, _)| name == file)
            } else if single_file {
                sources.first()
            } else {
                None
            };

            if let Some((name, src)) = matching_source {
                if span.end <= src.len() {
                    // For cross-file secondary spans, augment help text with location info
                    let mut render_err = err.clone();
                    if let (Some(sec_span), Some(ref sec_label), Some(ref sec_file)) = (
                        err.secondary_span,
                        &err.secondary_label,
                        &err.secondary_file,
                    ) {
                        if err.file.as_ref() != Some(sec_file) {
                            // Cross-file: compute line number and append to help
                            let line =
                                sources
                                    .iter()
                                    .find(|(n, _)| n == sec_file)
                                    .map_or(0, |(_, s)| {
                                        s[..sec_span.start.min(s.len())]
                                            .chars()
                                            .filter(|&c| c == '\n')
                                            .count()
                                            + 1
                                    });
                            let loc_note = if line > 0 {
                                format!("\n  note: {sec_label} ({sec_file}:{line})")
                            } else {
                                format!("\n  note: {sec_label} ({sec_file})")
                            };
                            let combined = match &render_err.help {
                                Some(h) => format!("{h}{loc_note}"),
                                None => loc_note.trim_start().to_owned(),
                            };
                            render_err.help = Some(combined);
                        }
                    }
                    let named = NamedSource::new(name.clone(), src.clone());
                    let report = miette::Report::new(render_err).with_source_code(named);
                    eprintln!("{report:?}");
                    continue;
                }
            }
        }
        // Fallback: plain text, but still include cross-file secondary info if present
        if let (Some(sec_span), Some(ref sec_label), Some(ref sec_file)) = (
            err.secondary_span,
            &err.secondary_label,
            &err.secondary_file,
        ) {
            let line = sources
                .iter()
                .find(|(n, _)| n == sec_file)
                .map_or(0, |(_, s)| {
                    s[..sec_span.start.min(s.len())]
                        .chars()
                        .filter(|&c| c == '\n')
                        .count()
                        + 1
                });
            if line > 0 {
                eprintln!("{err}\n  note: {sec_label} ({sec_file}:{line})");
            } else {
                eprintln!("{err}\n  note: {sec_label} ({sec_file})");
            }
        } else {
            eprintln!("{err}");
        }
    }
}

/// Render a verification result, using miette source snippets for failures.
fn report_verification_result(
    result: &abide::verify::VerificationResult,
    sources: &[(String, String)],
) {
    use abide::verify::VerificationResult;

    // For failures with source location, render with miette
    if result.is_failure() {
        if let Some(span) = result.span() {
            let matching_source = if let Some(file) = result.file() {
                sources.iter().find(|(name, _)| name == file)
            } else if sources.len() == 1 {
                sources.first()
            } else {
                None
            };

            if let Some((name, src)) = matching_source {
                if span.end <= src.len() {
                    let label = match result {
                        VerificationResult::Counterexample { name, .. } => {
                            format!("counterexample found for '{name}'")
                        }
                        VerificationResult::SceneFail { name, reason, .. } => {
                            format!("scene '{name}' failed: {reason}")
                        }
                        VerificationResult::Unprovable { name, hint, .. } => {
                            format!("could not prove '{name}': {hint}")
                        }
                        _ => String::new(),
                    };
                    let named = NamedSource::new(name.clone(), src.clone());
                    let diag = miette::miette!(
                        labels = vec![miette::LabeledSpan::at(span.start..span.end, &label)],
                        "{}",
                        result
                    )
                    .with_source_code(named);
                    eprintln!("{diag:?}");
                    return;
                }
            }
        }
        // Fallback: plain text for failures without source info
        eprintln!("{result}");
    } else {
        // Success results: plain text
        println!("{result}");
    }
}

fn load_and_elaborate(
    paths: &[PathBuf],
    sources: &mut Vec<(String, String)>,
) -> Option<(
    abide::elab::types::ElabResult,
    Vec<abide::elab::error::ElabError>,
)> {
    let (env, load_errors, all_paths) = abide::loader::load_files(paths);

    // Extend source map with any included files not already present
    for loaded_path in &all_paths {
        let key = loaded_path.display().to_string();
        if !sources.iter().any(|(name, _)| name == &key) {
            if let Ok(src) = std::fs::read_to_string(loaded_path) {
                sources.push((key, src));
            }
        }
    }

    // Always render include load errors — even if top-level files also failed,
    // so the user sees the full picture in mixed-failure runs.
    for inc_err in &env.include_load_errors {
        render_load_error(inc_err, sources);
    }

    if !load_errors.is_empty() {
        for err in &load_errors {
            render_load_error(err, sources);
        }
        return None;
    }

    // Include errors are non-fatal for elaboration (the successfully-loaded
    // declarations are still available), but we track whether any occurred
    // so the caller can decide on exit status.
    let had_include_errors = !env.include_load_errors.is_empty();
    let (result, mut elab_errors) = abide::elab::elaborate_env(env);
    if had_include_errors {
        // Ensure the caller sees a non-empty error list so it exits with failure
        // even if elaboration itself produced no errors.
        if elab_errors.is_empty() {
            elab_errors.push(abide::elab::error::ElabError::new(
                abide::elab::error::ErrorKind::UndefinedRef,
                "one or more included files failed to load (see above)",
                String::new(),
            ));
        }
    }
    Some((result, elab_errors))
}

/// Render a single `LoadError` with miette formatting.
fn render_load_error(err: &abide::loader::LoadError, sources: &[(String, String)]) {
    match err {
        abide::loader::LoadError::ParseErrors { path, errors } => {
            let src = sources
                .iter()
                .find(|(name, _)| name == &path.display().to_string())
                .or_else(|| {
                    let canonical = std::fs::canonicalize(path).ok()?;
                    sources
                        .iter()
                        .find(|(name, _)| name == &canonical.display().to_string())
                });
            for pe in errors {
                if let Some((name, text)) = src {
                    let named = NamedSource::new(name.clone(), text.clone());
                    let report = miette::Report::new(pe.clone()).with_source_code(named);
                    eprintln!("{report:?}");
                } else {
                    eprintln!("{pe}");
                }
            }
        }
        abide::loader::LoadError::Lex { errors, .. } => {
            for le in errors {
                let report = miette::Report::new(le.clone());
                eprintln!("{report:?}");
            }
        }
        abide::loader::LoadError::Io { path, error } => {
            let report = miette::miette!("failed to read {}: {error}", path.display());
            eprintln!("{report:?}");
        }
    }
}
