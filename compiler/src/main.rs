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
            if !errors.is_empty() {
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
            if !errors.is_empty() {
                std::process::exit(1);
            }
            let ir_program = abide::ir::lower(&result);
            let json = abide::ir::emit_json(&ir_program);
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
            if !errors.is_empty() {
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
                    println!("{r}");
                    if matches!(
                        r,
                        abide::verify::VerificationResult::Counterexample { .. }
                            | abide::verify::VerificationResult::SceneFail { .. }
                            | abide::verify::VerificationResult::Unprovable { .. }
                    ) {
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
fn report_elab_errors(errors: &[abide::elab::error::ElabError], sources: &[(String, String)]) {
    let single_file = sources.len() <= 1;
    for err in errors {
        if let Some(span) = err.span {
            // Find the matching source for this error's file
            let matching_source = if let Some(ref file) = err.file {
                sources.iter().find(|(name, _)| name == file)
            } else if single_file {
                // Single-file mode: safe to use the only source
                sources.first()
            } else {
                // Multi-file with untagged error: don't guess — fall back to plain text
                None
            };

            if let Some((name, src)) = matching_source {
                // Verify the span is within the source's range
                if span.end <= src.len() {
                    let named = NamedSource::new(name.clone(), src.clone());
                    let report = miette::Report::new(err.clone()).with_source_code(named);
                    eprintln!("{report:?}");
                    continue;
                }
            }
        }
        // Fallback: plain text for errors without spans, without matching source,
        // or with out-of-range spans
        eprintln!("{err}");
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

    if !load_errors.is_empty() {
        for err in &load_errors {
            match err {
                abide::loader::LoadError::ParseErrors { path, errors } => {
                    // Render each parse error with source snippet
                    let src = sources
                        .iter()
                        .find(|(name, _)| name == &path.display().to_string())
                        .or_else(|| {
                            // Try canonical path match
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
                other => eprintln!("{other}"),
            }
        }
        return None;
    }

    Some(abide::elab::elaborate_env(env))
}
