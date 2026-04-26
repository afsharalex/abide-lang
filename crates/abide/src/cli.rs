use clap::{Parser as ClapParser, Subcommand, ValueEnum};
use miette::{IntoDiagnostic, NamedSource, WrapErr};
use std::collections::BTreeMap;
use std::path::PathBuf;

use crate::diagnostic::Diagnostic;
use crate::driver;
use crate::render;

struct QaRunnerHooks;

impl crate::qa::runner::RunnerHooks for QaRunnerHooks {
    fn simulate(
        &mut self,
        ir_program: &crate::ir::types::IRProgram,
        request: &crate::qa::ast::SimulationRequest,
    ) -> Result<crate::qa::artifacts::SimulationArtifact, String> {
        let config = crate::simulate::SimulateConfig {
            steps: request.steps,
            seed: request.seed,
            slots_per_entity: request.slots,
            entity_slot_overrides: request.scopes.iter().cloned().collect(),
            system: request.system.clone(),
        };
        let result = crate::simulate::simulate_program(ir_program, &config)?;
        Ok(crate::qa::artifacts::SimulationArtifact {
            systems: result.systems,
            seed: result.seed,
            steps_requested: result.steps_requested,
            steps_executed: result.steps_executed,
            termination: match result.termination {
                crate::simulate::SimulationTermination::StepLimit => {
                    crate::qa::artifacts::SimulationTermination::StepLimit
                }
                crate::simulate::SimulationTermination::Deadlock { reasons } => {
                    crate::qa::artifacts::SimulationTermination::Deadlock { reasons }
                }
            },
            behavior: result.behavior,
        })
    }
}

#[derive(ClapParser)]
#[command(name = "abide", about = "Abide specification language compiler")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum VerifySolver {
    Z3,
    Cvc5,
    Auto,
    Both,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum VerifyChcSolver {
    Z3,
    Cvc5,
    Auto,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum VerifyWitnessSemantics {
    Operational,
    Relational,
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

    /// Export compiled temporal formulas for verify blocks as JSON
    #[command(name = "export-temporal")]
    ExportTemporal {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },

    /// Verify a specification: bounded model checking, scene checking, theorem proving
    Verify {
        #[arg(required = true)]
        files: Vec<PathBuf>,

        /// SMT backend for SAT/BMC/property/theorem/scene paths
        #[arg(long, value_enum, default_value_t = VerifySolver::Z3)]
        solver: VerifySolver,

        /// CHC backend for IC3/PDR paths
        #[arg(long = "chc-solver", value_enum, default_value_t = VerifyChcSolver::Z3)]
        chc_solver: VerifyChcSolver,

        /// Skip induction (Tier 1), only run bounded model checking
        #[arg(long, conflicts_with = "unbounded_only")]
        bounded_only: bool,

        /// Skip bounded model checking, only try induction
        #[arg(long, conflicts_with = "bounded_only")]
        unbounded_only: bool,

        /// End-to-end verify timeout in seconds (default: 1200, 0 = no timeout)
        #[arg(long, default_value_t = DEFAULT_VERIFY_TIMEOUT_SECS)]
        timeout: u64,

        /// Induction timeout in seconds (default: 1200, 0 = no timeout)
        #[arg(long, default_value_t = DEFAULT_INDUCTION_TIMEOUT_SECS)]
        induction_timeout: u64,

        /// BMC timeout in seconds (default: 1200, 0 = no timeout)
        #[arg(long, default_value_t = DEFAULT_BMC_TIMEOUT_SECS)]
        bmc_timeout: u64,

        /// IC3/PDR timeout in seconds (default: 1200, 0 = no timeout)
        #[arg(long, default_value_t = DEFAULT_IC3_TIMEOUT_SECS)]
        ic3_timeout: u64,

        /// Skip IC3/PDR verification (for speed)
        #[arg(long)]
        no_ic3: bool,

        /// Skip automatic prop verification
        #[arg(long)]
        no_prop_verify: bool,

        /// Skip function contract verification
        #[arg(long)]
        no_fn_verify: bool,

        /// Show progress messages during verification
        #[arg(long)]
        progress: bool,

        /// Native witness family for failing verification results
        #[arg(long = "witness-semantics", value_enum, default_value_t = VerifyWitnessSemantics::Operational)]
        witness_semantics: VerifyWitnessSemantics,

        /// Print expanded human-readable verification details, including native evidence
        #[arg(long)]
        verbose: bool,

        /// Dump raw native evidence as JSON to the terminal for debugging
        #[arg(long)]
        debug_evidence: bool,

        /// Write a verification report as `<format> [output_dir]`; defaults to `reports/`
        #[arg(long, value_names = ["FORMAT", "OUTPUT_DIR"], num_args = 1..=2)]
        report: Option<Vec<String>>,
    },

    /// Forward-simulate event sequences without the solver
    Simulate {
        #[arg(required = true)]
        files: Vec<PathBuf>,

        /// Number of atomic steps to execute before stopping
        #[arg(long, default_value_t = 25)]
        steps: usize,

        /// Seed for deterministic pseudo-random step selection
        #[arg(long, default_value_t = 0)]
        seed: u64,

        /// Preallocated slot count per entity type
        #[arg(long, default_value_t = 4)]
        slots: usize,

        /// Override a specific entity pool size as `Entity=N`
        #[arg(long = "scope", value_name = "ENTITY=SLOTS")]
        scope: Vec<String>,

        /// Restrict simulation to a single system name
        #[arg(long)]
        system: Option<String>,
    },

    /// Run QA structural analysis scripts
    #[command(name = "qa")]
    Qa {
        /// QA script file (.qa)
        script: PathBuf,

        /// Load specs from this directory before running the script
        #[arg(short = 'f', long = "from")]
        spec_dir: Option<PathBuf>,

        /// Output format: human (default) or json
        #[arg(long, default_value = "human")]
        format: String,
    },

    /// Start interactive REPL
    Repl {
        /// Path to load specs from (file or directory)
        path: Option<PathBuf>,

        /// Use Vi keybindings instead of Emacs
        #[arg(long)]
        vi: bool,
    },
}

/// Default timeout for verifier phases, in seconds.
///
/// The default user-facing verify path should terminate on its own even when
/// backends hit hard cases. Individual phases remain overrideable with the
/// existing per-flag controls.
const DEFAULT_VERIFY_TIMEOUT_SECS: u64 = 20 * 60;

/// Default timeout for Tier 1 induction attempts, in seconds.
const DEFAULT_INDUCTION_TIMEOUT_SECS: u64 = DEFAULT_VERIFY_TIMEOUT_SECS;

/// Default bounded model checking depth for auto-verified props.
///
/// Props don't have an explicit `[0..N]` scope like verify blocks.
/// When induction fails for a prop, the BMC fallback uses this depth.
/// Not yet wired to a CLI flag — will be exposed when prop auto-verification
/// is implemented ( deferred item).
const DEFAULT_PROP_BMC_DEPTH: usize = 10;

/// Default timeout for IC3/PDR attempts, in seconds.
const DEFAULT_BMC_TIMEOUT_SECS: u64 = DEFAULT_VERIFY_TIMEOUT_SECS;

/// Default timeout for IC3/PDR attempts, in seconds.
const DEFAULT_IC3_TIMEOUT_SECS: u64 = DEFAULT_VERIFY_TIMEOUT_SECS;

#[allow(clippy::too_many_lines)]
pub fn run() -> miette::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Lex { file } => {
            let src = driver::read_file(&file)?;
            let tokens =
                driver::lex_source(&src).map_err(|errors| errors.into_iter().next().unwrap())?;
            for (token, span) in &tokens {
                println!("{span:?}  {token}");
            }
        }
        Command::Parse { file } => {
            let parsed = driver::parse_file(&file)?;
            let program = parsed.program;
            let diagnostics = parsed.diagnostics;
            if !diagnostics.is_empty() {
                report_diagnostics(&diagnostics, &[(file.display().to_string(), parsed.source)]);
                std::process::exit(1);
            }
            println!("{program:#?}");
        }
        Command::Elaborate { files } => {
            let elaborated = match driver::load_and_elaborate(&files) {
                Ok(elaborated) => elaborated,
                Err(diagnostics) => {
                    report_diagnostics(&diagnostics, &driver::read_sources_for_diagnostics(&files));
                    std::process::exit(1);
                }
            };
            report_diagnostics(&elaborated.diagnostics, &elaborated.sources);
            if has_error_diagnostics(&elaborated.diagnostics) {
                std::process::exit(1);
            }
            println!("{:#?}", elaborated.result);
        }
        Command::EmitIr { files } => {
            let lowered = match driver::lower_files(&files) {
                Ok(lowered) => lowered,
                Err(diagnostics) => {
                    report_diagnostics(&diagnostics, &driver::read_sources_for_diagnostics(&files));
                    std::process::exit(1);
                }
            };
            report_diagnostics(&lowered.diagnostics, &lowered.sources);
            if has_error_diagnostics(&lowered.diagnostics) {
                std::process::exit(1);
            }
            let json = crate::ir::emit_json(&lowered.ir_program)
                .into_diagnostic()
                .wrap_err("failed to serialize IR to JSON")?;
            println!("{json}");
        }
        Command::ExportTemporal { files } => {
            let exported = match driver::export_temporal_files(&files) {
                Ok(exported) => exported,
                Err(diagnostics) => {
                    report_diagnostics(&diagnostics, &driver::read_sources_for_diagnostics(&files));
                    std::process::exit(1);
                }
            };
            report_diagnostics(&exported.lowered.diagnostics, &exported.lowered.sources);
            if has_error_diagnostics(&exported.lowered.diagnostics) {
                std::process::exit(1);
            }
            let json = serde_json::to_string_pretty(&exported.verifies)
                .into_diagnostic()
                .wrap_err("failed to serialize compiled temporal formulas")?;
            println!("{json}");
        }
        Command::Verify {
            files,
            solver,
            chc_solver,
            bounded_only,
            unbounded_only,
            timeout,
            induction_timeout,
            bmc_timeout,
            ic3_timeout,
            no_ic3,
            no_prop_verify,
            no_fn_verify,
            progress,
            witness_semantics,
            verbose,
            debug_evidence,
            report,
        } => {
            let solver_selection = match solver {
                VerifySolver::Z3 => crate::verify::SolverSelection::Z3,
                VerifySolver::Cvc5 => crate::verify::SolverSelection::Cvc5,
                VerifySolver::Auto => crate::verify::SolverSelection::Auto,
                VerifySolver::Both => crate::verify::SolverSelection::Both,
            };
            let chc_selection = match chc_solver {
                VerifyChcSolver::Z3 => crate::verify::ChcSelection::Z3,
                VerifyChcSolver::Cvc5 => crate::verify::ChcSelection::Cvc5,
                VerifyChcSolver::Auto => crate::verify::ChcSelection::Auto,
            };
            match solver {
                VerifySolver::Cvc5 | VerifySolver::Both
                    if !crate::verify::solver::is_solver_family_available(
                        crate::verify::solver::SolverFamily::Cvc5,
                    ) =>
                {
                    return Err(miette::miette!(
                        "requested solver `{}` is not available in this build",
                        match solver {
                            VerifySolver::Cvc5 => "cvc5",
                            VerifySolver::Both => "both",
                            VerifySolver::Z3 | VerifySolver::Auto => unreachable!(),
                        }
                    ));
                }
                _ => {}
            }
            match chc_solver {
                VerifyChcSolver::Cvc5
                    if !crate::verify::solver::is_solver_family_available(
                        crate::verify::solver::SolverFamily::Cvc5,
                    ) =>
                {
                    return Err(miette::miette!(
                        "requested CHC solver `cvc5` is not available in this build"
                    ));
                }
                _ => {}
            }

            let witness_semantics = match witness_semantics {
                VerifyWitnessSemantics::Operational => crate::verify::WitnessSemantics::Operational,
                VerifyWitnessSemantics::Relational => crate::verify::WitnessSemantics::Relational,
            };
            let solver_name = format!("{solver:?}").to_lowercase();
            let chc_solver_name = format!("{chc_solver:?}").to_lowercase();
            let witness_semantics_name = format!("{witness_semantics:?}").to_lowercase();
            let report_request = render::parse_verify_report_request(report)?;

            let config = crate::verify::VerifyConfig {
                solver_selection,
                chc_selection,
                bounded_only,
                unbounded_only,
                overall_timeout_ms: timeout.saturating_mul(1000),
                induction_timeout_ms: induction_timeout.saturating_mul(1000),
                bmc_timeout_ms: bmc_timeout.saturating_mul(1000),
                prop_bmc_depth: DEFAULT_PROP_BMC_DEPTH,
                ic3_timeout_ms: ic3_timeout.saturating_mul(1000),
                no_ic3,
                no_prop_verify,
                no_fn_verify,
                progress,
                witness_semantics,
            };

            let verified = match driver::verify_files(&files, &config) {
                Ok(verified) => verified,
                Err(diagnostics) => {
                    if !contains_load_io_diagnostics(&diagnostics) {
                        if let Some(request) = report_request.as_ref() {
                            render::write_verification_report(
                                request,
                                &files,
                                &solver_name,
                                &chc_solver_name,
                                bounded_only,
                                unbounded_only,
                                induction_timeout,
                                bmc_timeout,
                                ic3_timeout,
                                no_ic3,
                                no_prop_verify,
                                no_fn_verify,
                                progress,
                                &witness_semantics_name,
                                &diagnostics,
                                &[],
                            )?;
                        }
                    }
                    report_diagnostics(&diagnostics, &driver::read_sources_for_diagnostics(&files));
                    std::process::exit(1);
                }
            };
            report_diagnostics(&verified.lowered.diagnostics, &verified.lowered.sources);
            let diagnostics = verified.lowered.diagnostics.clone();
            if has_error_diagnostics(&verified.lowered.diagnostics) {
                if let Some(request) = report_request.as_ref() {
                    render::write_verification_report(
                        request,
                        &files,
                        &solver_name,
                        &chc_solver_name,
                        bounded_only,
                        unbounded_only,
                        induction_timeout,
                        bmc_timeout,
                        ic3_timeout,
                        no_ic3,
                        no_prop_verify,
                        no_fn_verify,
                        progress,
                        &witness_semantics_name,
                        &diagnostics,
                        &[],
                    )?;
                }
                std::process::exit(1);
            }
            let results = verified.results;
            if let Some(request) = report_request.as_ref() {
                let report_path = render::write_verification_report(
                    request,
                    &files,
                    &solver_name,
                    &chc_solver_name,
                    bounded_only,
                    unbounded_only,
                    induction_timeout,
                    bmc_timeout,
                    ic3_timeout,
                    no_ic3,
                    no_prop_verify,
                    no_fn_verify,
                    progress,
                    &witness_semantics_name,
                    &diagnostics,
                    &results,
                )?;
                println!("Report written to {}", report_path.display());
            }
            if results.is_empty() {
                println!("No verification targets found.");
            } else {
                let mut all_passed = true;
                for r in &results {
                    render::report_verification_result(
                        r,
                        &verified.lowered.sources,
                        verbose,
                        debug_evidence,
                    );
                    if r.is_failure() {
                        all_passed = false;
                    }
                }
                if !all_passed {
                    std::process::exit(1);
                }
            }
        }
        Command::Simulate {
            files,
            steps,
            seed,
            slots,
            scope,
            system,
        } => {
            let entity_slot_overrides = parse_simulation_scope_overrides(&scope)?;
            let config = crate::simulate::SimulateConfig {
                steps,
                seed,
                slots_per_entity: slots,
                entity_slot_overrides,
                system,
            };
            let simulated = match driver::simulate_files(&files, &config) {
                Ok(simulated) => simulated,
                Err(diagnostics) => {
                    report_diagnostics(&diagnostics, &driver::read_sources_for_diagnostics(&files));
                    std::process::exit(1);
                }
            };
            report_diagnostics(&simulated.lowered.diagnostics, &simulated.lowered.sources);
            if has_error_diagnostics(&simulated.lowered.diagnostics) {
                std::process::exit(1);
            }
            print!("{}", simulated.result.render_text());
            if matches!(
                simulated.result.termination,
                crate::simulate::SimulationTermination::Deadlock { .. }
            ) {
                std::process::exit(1);
            }
        }
        Command::Qa {
            script,
            spec_dir,
            format,
        } => {
            let json_mode = format == "json";
            let mut hooks = QaRunnerHooks;
            let result = crate::qa::runner::run_qa_script_with_hooks(
                &script,
                spec_dir.as_deref(),
                json_mode,
                &mut hooks,
            );
            for line in &result.output {
                println!("{line}");
            }
            if result.failed > 0 || result.executed == 0 {
                if !json_mode {
                    println!(
                        "\n=== QA: {} passed, {} failed ({} executed) ===",
                        result.passed, result.failed, result.executed
                    );
                }
                std::process::exit(1);
            }
            if !json_mode {
                println!(
                    "\n=== QA: {} passed, {} failed ({} executed) ===",
                    result.passed, result.failed, result.executed
                );
            }
        }
        Command::Repl { path, vi } => {
            crate::repl::run_repl(path.as_deref(), vi);
        }
    }

    Ok(())
}

fn parse_simulation_scope_overrides(entries: &[String]) -> miette::Result<BTreeMap<String, usize>> {
    let mut overrides = BTreeMap::new();
    for entry in entries {
        let (entity, slots_text) = entry
            .split_once('=')
            .ok_or_else(|| miette::miette!("invalid `--scope {entry}`; expected `Entity=N`"))?;
        if entity.trim().is_empty() {
            return Err(miette::miette!(
                "invalid `--scope {entry}`; entity name must not be empty"
            ));
        }
        let slots = slots_text.parse::<usize>().map_err(|_| {
            miette::miette!("invalid `--scope {entry}`; slot count must be a non-negative integer")
        })?;
        overrides.insert(entity.trim().to_owned(), slots);
    }
    Ok(overrides)
}

/// Render elaboration errors with miette source snippets when spans are available.
///
/// Only renders source snippets when the error's file matches the loaded source.
/// Errors from other files (in multi-file mode) fall back to plain text to avoid
/// rendering spans against the wrong source.
/// Returns true if any diagnostics are errors (not warnings).
fn has_error_diagnostics(diagnostics: &[Diagnostic]) -> bool {
    diagnostics.iter().any(Diagnostic::is_error)
}

fn contains_load_io_diagnostics(diagnostics: &[Diagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code.as_deref() == Some("abide::load::io"))
}

fn report_diagnostics(diagnostics: &[Diagnostic], sources: &[(String, String)]) {
    let single_file = sources.len() <= 1;
    for diagnostic in diagnostics {
        if let Some(span) = diagnostic.span {
            let matching_source = if let Some(ref file) = diagnostic.file {
                sources.iter().find(|(name, _)| name == file)
            } else if single_file {
                sources.first()
            } else {
                None
            };

            if let Some((name, src)) = matching_source {
                if span.end <= src.len() {
                    let mut render_diag = diagnostic.clone();
                    for related in &mut render_diag.related {
                        if let (Some(file), Some(sec_span)) = (&related.file, related.span) {
                            if diagnostic.file.as_ref() != Some(file) {
                                let line =
                                    sources.iter().find(|(n, _)| n == file).map_or(0, |(_, s)| {
                                        s[..sec_span.start.min(s.len())]
                                            .chars()
                                            .filter(|&c| c == '\n')
                                            .count()
                                            + 1
                                    });
                                let loc_note = if line > 0 {
                                    format!("{} ({}:{line})", related.message, file)
                                } else {
                                    format!("{} ({file})", related.message)
                                };
                                render_diag.help = Some(match &render_diag.help {
                                    Some(help) => format!("{help}\n  note: {loc_note}"),
                                    None => format!("note: {loc_note}"),
                                });
                            }
                        }
                    }
                    let named = NamedSource::new(name.clone(), src.clone());
                    let report = miette::Report::new(render_diag).with_source_code(named);
                    eprintln!("{report:?}");
                    continue;
                }
            }
        }
        eprintln!("{diagnostic}");
        for related in &diagnostic.related {
            match (&related.file, related.span) {
                (Some(file), Some(span)) => {
                    let line = sources.iter().find(|(n, _)| n == file).map_or(0, |(_, s)| {
                        s[..span.start.min(s.len())]
                            .chars()
                            .filter(|&c| c == '\n')
                            .count()
                            + 1
                    });
                    if line > 0 {
                        eprintln!("  note: {} ({}:{line})", related.message, file);
                    } else {
                        eprintln!("  note: {} ({file})", related.message);
                    }
                }
                _ => eprintln!("  note: {}", related.message),
            }
        }
    }
}
