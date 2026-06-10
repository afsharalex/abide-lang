//! Command-line entry point for the `abide` CLI.
//!
//! The clap-derived `Cli` type at the bottom of the file dispatches
//! subcommands (`parse`, `elaborate`, `lower`, `verify`, `simulate`,
//! `qa`, `repl`, …) to the [`driver`] module. Most types here are
//! private — they exist only to give clap stable parsing surfaces.
//!
//! The single public entry point is [`run`] (declared further down),
//! which the `abide-bin` `main` invokes.

use clap::{Args, Parser as ClapParser, Subcommand, ValueEnum};
use miette::{IntoDiagnostic, NamedSource, WrapErr};
use std::collections::BTreeMap;
use std::path::PathBuf;

use crate::diagnostic::Diagnostic;
use crate::driver;
use crate::render;

/// CLI-side host that wires the QA runner's `simulate` and
/// `explore_state_space` hooks to the in-tree simulator and verifier
/// backends.
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

    fn explore_state_space(
        &mut self,
        ir_program: &crate::ir::types::IRProgram,
        request: &crate::qa::ast::StateSpaceRequest,
    ) -> Result<crate::qa::artifacts::StateSpaceArtifact, String> {
        crate::qa::runner::explore_state_space(ir_program, request)
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
    /// Lex a source file or directory and print tokens
    Lex {
        #[arg(value_name = "FILE_OR_DIR")]
        file: PathBuf,
    },

    /// Parse a source file or directory and print AST
    Parse {
        #[arg(value_name = "FILE_OR_DIR")]
        file: PathBuf,
    },

    /// Elaborate source file(s) or directories and print result
    Elaborate {
        #[arg(required = true, value_name = "FILES_OR_DIRS")]
        files: Vec<PathBuf>,
    },

    /// Emit IR as JSON
    #[command(name = "emit-ir")]
    EmitIr {
        #[arg(required = true, value_name = "FILES_OR_DIRS")]
        files: Vec<PathBuf>,
    },

    /// Export compiled temporal formulas for verify blocks as JSON
    #[command(name = "export-temporal")]
    ExportTemporal {
        #[arg(required = true, value_name = "FILES_OR_DIRS")]
        files: Vec<PathBuf>,
    },

    /// Verify a specification: bounded model checking, scene checking, theorem proving
    Verify {
        #[arg(required = true, value_name = "FILES_OR_DIRS")]
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

        /// Generic verify timeout in seconds (0 = no timeout)
        #[arg(long)]
        timeout: Option<u64>,

        /// Bounded workflow timeout in seconds (verify/scene/BMC fallback; 0 = no timeout; default: 30)
        #[arg(long = "bounded-timeout")]
        bounded_timeout: Option<u64>,

        /// Proof workflow timeout in seconds (theorem/lemma/contracts/IC3; 0 = no timeout; default: 120)
        #[arg(long = "proof-timeout")]
        proof_timeout: Option<u64>,

        /// Induction timeout in seconds (overrides --proof-timeout; 0 = no timeout)
        #[arg(long)]
        induction_timeout: Option<u64>,

        /// BMC timeout in seconds (overrides --bounded-timeout; 0 = no timeout)
        #[arg(long)]
        bmc_timeout: Option<u64>,

        /// BMC fallback depth for auto-verified props
        #[arg(long = "prop-bmc-depth", default_value_t = DEFAULT_PROP_BMC_DEPTH)]
        prop_bmc_depth: usize,

        /// Disable iterative BMC depth search for shortest counterexamples
        #[arg(long = "no-bmc-iterative-deepening")]
        no_bmc_iterative_deepening: bool,

        /// IC3/PDR timeout in seconds (overrides --proof-timeout; 0 = no timeout)
        #[arg(long)]
        ic3_timeout: Option<u64>,

        /// Opt ordinary verify blocks into IC3/PDR proof search
        #[arg(long)]
        ic3: bool,

        /// Opt cvc5 solver runs into in-process SyGuS invariant synthesis
        #[arg(long = "cvc5-sygus", requires = "solver")]
        cvc5_sygus: bool,

        /// Skip automatic prop verification
        #[arg(long)]
        no_prop_verify: bool,

        /// Skip function contract verification
        #[arg(long)]
        no_fn_verify: bool,

        /// Stream verification results as targets finish
        #[arg(long)]
        stream: bool,

        /// Native witness family for failing verification results
        #[arg(long = "witness-semantics", value_enum, default_value_t = VerifyWitnessSemantics::Operational)]
        witness_semantics: VerifyWitnessSemantics,

        /// Disable relational SAT active-slot symmetry breaking
        #[arg(long)]
        no_relational_symmetry_breaking: bool,

        /// Run a single target, optionally typed as verify:NAME, scene:NAME, theorem:NAME, lemma:NAME, prop:NAME, or fn:NAME
        #[arg(long, value_name = "TARGET")]
        target: Option<String>,

        /// Print expanded human-readable verification details, including native evidence
        #[arg(long)]
        verbose: bool,

        /// Dump raw native evidence as JSON to the terminal for debugging
        #[arg(long)]
        debug_evidence: bool,

        /// Write a verification report as `<format> [output_dir]`; defaults to `reports/`
        #[arg(long, value_names = ["FORMAT", "OUTPUT_DIR"], num_args = 1..=2)]
        report: Option<Vec<String>>,

        /// Write structured trace/evidence artifacts as JSON
        #[arg(long = "trace-artifact", value_name = "PATH")]
        trace_artifact: Option<PathBuf>,
    },

    /// Run one seeded model execution without the solver
    Run(SimulateArgs),

    /// Forward-simulate event sequences without the solver
    Simulate(SimulateArgs),

    /// Inspect structured trace artifacts emitted by verify/run
    Trace(TraceArgs),

    /// Run QA structural analysis scripts
    #[command(name = "qa")]
    Qa {
        /// QA script file or directory of .qa scripts
        #[arg(value_name = "SCRIPT_OR_DIR")]
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

        /// Start with no specs loaded, even if the current directory contains Abide files
        #[arg(long)]
        scratch: bool,

        /// Use Vi keybindings instead of Emacs
        #[arg(long)]
        vi: bool,
    },
}

#[derive(Args)]
struct SimulateArgs {
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

    /// Write structured simulation trace artifact as JSON
    #[arg(long = "trace-artifact", value_name = "PATH")]
    trace_artifact: Option<PathBuf>,
}

#[derive(Args)]
struct TraceArgs {
    /// Trace artifact JSON file produced by --trace-artifact
    file: PathBuf,

    /// Artifact id to inspect
    #[arg(long, default_value_t = 1)]
    artifact: usize,

    #[command(subcommand)]
    command: Option<TraceCommand>,
}

#[derive(Subcommand)]
enum TraceCommand {
    /// List artifacts in the bundle
    List,

    /// Render the selected artifact as a frame-by-frame trace
    Draw,

    /// Show one frame from the selected artifact
    State { index: usize },

    /// Show state changes between two frames
    Diff { from: usize, to: usize },

    /// Print the selected artifact as JSON
    Json,
}

/// Default generic timeout for verifier passes, in seconds.
///
/// When users pass `--timeout`, it applies to every timeout class that does
/// not have a more granular override.
const DEFAULT_VERIFY_TIMEOUT_SECS: u64 = 30;

/// Default timeout for bounded workflows, in seconds.
const DEFAULT_BOUNDED_TIMEOUT_SECS: u64 = DEFAULT_VERIFY_TIMEOUT_SECS;

/// Default timeout for proof workflows, in seconds.
const DEFAULT_PROOF_TIMEOUT_SECS: u64 = 120;

/// Default bounded model checking depth for auto-verified props.
///
/// Props don't have an explicit `[0..N]` scope like verify blocks.
/// When induction fails for a prop, the BMC fallback uses this depth.
const DEFAULT_PROP_BMC_DEPTH: usize = 10;

/// Parses CLI arguments from the process environment and dispatches
/// the chosen subcommand. The `main` binary calls this directly.
///
/// # Errors
///
/// Returns any `miette` diagnostic raised during argument parsing or
/// subcommand execution. The process exits non-zero on `Err`.
pub fn run() -> miette::Result<()> {
    let cli = Cli::parse();
    run_command(cli.command)
}

fn run_command(command: Command) -> miette::Result<()> {
    match command {
        Command::Lex { file } => {
            run_lex_command(file)?;
        }
        Command::Parse { file } => {
            run_parse_command(file)?;
        }
        Command::Elaborate { files } => {
            run_elaborate_command(files)?;
        }
        Command::EmitIr { files } => {
            run_emit_ir_command(files)?;
        }
        Command::ExportTemporal { files } => {
            run_export_temporal_command(files)?;
        }
        Command::Verify {
            files,
            solver,
            chc_solver,
            bounded_only,
            unbounded_only,
            timeout,
            bounded_timeout,
            proof_timeout,
            induction_timeout,
            bmc_timeout,
            prop_bmc_depth,
            no_bmc_iterative_deepening,
            ic3_timeout,
            ic3,
            cvc5_sygus,
            no_prop_verify,
            no_fn_verify,
            stream,
            witness_semantics,
            no_relational_symmetry_breaking,
            target,
            verbose,
            debug_evidence,
            report,
            trace_artifact,
        } => {
            run_verify_command(VerifyCommand {
                files,
                solver,
                chc_solver,
                timeouts: VerifyTimeouts {
                    generic: timeout,
                    bounded: bounded_timeout,
                    proof: proof_timeout,
                    induction: induction_timeout,
                    bmc: bmc_timeout,
                    ic3: ic3_timeout,
                    prop_bmc_depth,
                },
                mode: VerifyModeOptions {
                    bounded_only,
                    unbounded_only,
                    bmc_iterative_deepening: !no_bmc_iterative_deepening,
                },
                solver_flags: VerifySolverFlags {
                    cvc5_sygus,
                    relational_symmetry_breaking: !no_relational_symmetry_breaking,
                },
                disabled_checks: VerifyDisabledChecks {
                    no_ic3: !ic3,
                    no_prop_verify,
                    no_fn_verify,
                },
                output: VerifyOutputOptions {
                    stream,
                    verbose,
                    debug_evidence,
                    report,
                    trace_artifact,
                },
                witness_semantics,
                target,
            })?;
        }
        Command::Run(args) | Command::Simulate(args) => {
            run_simulate_command(args)?;
        }
        Command::Trace(args) => {
            run_trace_command(args)?;
        }
        Command::Qa {
            script,
            spec_dir,
            format,
        } => {
            run_qa_command(script, spec_dir, &format);
        }
        Command::Repl { path, scratch, vi } => {
            crate::repl::run_repl(path.as_deref(), scratch, vi);
        }
    }

    Ok(())
}

fn run_lex_command(file: PathBuf) -> miette::Result<()> {
    let group_by_file = file.is_dir();
    let files = resolve_file_by_file_source_targets(file)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    let group_by_file = group_by_file || files.len() > 1;
    let mut sources = Vec::new();
    let mut diagnostics = Vec::new();
    let mut lexed_files = Vec::new();

    for file in &files {
        let src = driver::read_file(file)?;
        sources.push((file.display().to_string(), src.clone()));
        match driver::lex_source(&src) {
            Ok(tokens) => lexed_files.push((file.clone(), tokens)),
            Err(errors) => {
                diagnostics.extend(
                    errors
                        .into_iter()
                        .map(|error| error.to_diagnostic().in_file(file.display().to_string())),
                );
            }
        }
    }

    if !diagnostics.is_empty() {
        report_diagnostics(&diagnostics, &sources);
        std::process::exit(1);
    }

    for (file, tokens) in &lexed_files {
        if group_by_file {
            println!("== {} ==", file.display());
        }
        for (token, span) in tokens {
            println!("{span:?}  {token}");
        }
    }
    Ok(())
}

fn run_parse_command(file: PathBuf) -> miette::Result<()> {
    let group_by_file = file.is_dir();
    let files = resolve_file_by_file_source_targets(file)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    let group_by_file = group_by_file || files.len() > 1;
    let mut sources = Vec::new();
    let mut diagnostics = Vec::new();
    let mut parsed_files = Vec::new();

    for file in &files {
        let parsed = driver::parse_file(file)?;
        sources.push((file.display().to_string(), parsed.source));
        diagnostics.extend(parsed.diagnostics);
        parsed_files.push((file.clone(), parsed.program));
    }

    if !diagnostics.is_empty() {
        report_diagnostics(&diagnostics, &sources);
        std::process::exit(1);
    }

    for (file, program) in &parsed_files {
        if group_by_file {
            println!("== {} ==", file.display());
        }
        println!("{program:#?}");
    }
    Ok(())
}

fn resolve_file_by_file_source_targets(
    file: PathBuf,
) -> Result<Vec<PathBuf>, crate::targets::TargetDiscoveryError> {
    crate::targets::resolve_source_targets(&[file])
}

fn resolve_whole_spec_source_targets(
    files: Vec<PathBuf>,
) -> Result<Vec<PathBuf>, crate::targets::TargetDiscoveryError> {
    crate::targets::resolve_source_targets(&files)
}

fn run_elaborate_command(files: Vec<PathBuf>) -> miette::Result<()> {
    let files = resolve_whole_spec_source_targets(files)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    let elaborated = match driver::load_and_elaborate(&files) {
        Ok(elaborated) => elaborated,
        Err(diagnostics) => exit_with_diagnostics(&diagnostics, &files),
    };
    report_diagnostics(&elaborated.diagnostics, &elaborated.sources);
    if has_error_diagnostics(&elaborated.diagnostics) {
        std::process::exit(1);
    }
    println!("{:#?}", elaborated.result);
    Ok(())
}

fn run_emit_ir_command(files: Vec<PathBuf>) -> miette::Result<()> {
    let files = resolve_whole_spec_source_targets(files)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    let lowered = match driver::lower_files(&files) {
        Ok(lowered) => lowered,
        Err(diagnostics) => exit_with_diagnostics(&diagnostics, &files),
    };
    report_diagnostics(&lowered.diagnostics, &lowered.sources);
    if has_error_diagnostics(&lowered.diagnostics) {
        std::process::exit(1);
    }
    let json = crate::ir::emit_json(&lowered.ir_program)
        .into_diagnostic()
        .wrap_err("failed to serialize IR to JSON")?;
    println!("{json}");
    Ok(())
}

fn run_export_temporal_command(files: Vec<PathBuf>) -> miette::Result<()> {
    let files = resolve_whole_spec_source_targets(files)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    let exported = match driver::export_temporal_files(&files) {
        Ok(exported) => exported,
        Err(diagnostics) => exit_with_diagnostics(&diagnostics, &files),
    };
    report_diagnostics(&exported.lowered.diagnostics, &exported.lowered.sources);
    if has_error_diagnostics(&exported.lowered.diagnostics) {
        std::process::exit(1);
    }
    let json = serde_json::to_string_pretty(&exported.verifies)
        .into_diagnostic()
        .wrap_err("failed to serialize compiled temporal formulas")?;
    println!("{json}");
    Ok(())
}

fn exit_with_diagnostics<T>(diagnostics: &[Diagnostic], files: &[PathBuf]) -> T {
    report_diagnostics(diagnostics, &driver::read_sources_for_diagnostics(files));
    std::process::exit(1);
}

struct VerifyCommand {
    files: Vec<PathBuf>,
    solver: VerifySolver,
    chc_solver: VerifyChcSolver,
    timeouts: VerifyTimeouts,
    mode: VerifyModeOptions,
    solver_flags: VerifySolverFlags,
    disabled_checks: VerifyDisabledChecks,
    output: VerifyOutputOptions,
    witness_semantics: VerifyWitnessSemantics,
    target: Option<String>,
}

struct VerifyTimeouts {
    generic: Option<u64>,
    bounded: Option<u64>,
    proof: Option<u64>,
    induction: Option<u64>,
    bmc: Option<u64>,
    ic3: Option<u64>,
    prop_bmc_depth: usize,
}

#[derive(Debug, Clone, Copy)]
struct EffectiveVerifyTimeouts {
    overall: u64,
    bounded: u64,
    proof: u64,
    induction: u64,
    bmc: u64,
    ic3: u64,
    prop_bmc_depth: usize,
}

impl VerifyTimeouts {
    fn effective(&self) -> EffectiveVerifyTimeouts {
        let bounded = self
            .bounded
            .or(self.generic)
            .unwrap_or(DEFAULT_BOUNDED_TIMEOUT_SECS);
        let proof = self
            .proof
            .or(self.generic)
            .unwrap_or(DEFAULT_PROOF_TIMEOUT_SECS);
        let induction = self.induction.unwrap_or(proof);
        let bmc = self.bmc.unwrap_or(bounded);
        let ic3 = self.ic3.unwrap_or(proof);
        let overall = effective_overall_timeout([induction, bmc, ic3]);

        EffectiveVerifyTimeouts {
            overall,
            bounded,
            proof,
            induction,
            bmc,
            ic3,
            prop_bmc_depth: self.prop_bmc_depth,
        }
    }
}

fn effective_overall_timeout(timeouts: [u64; 3]) -> u64 {
    if timeouts.contains(&0) {
        0
    } else {
        timeouts
            .into_iter()
            .max()
            .unwrap_or(DEFAULT_PROOF_TIMEOUT_SECS)
    }
}

struct VerifyModeOptions {
    bounded_only: bool,
    unbounded_only: bool,
    bmc_iterative_deepening: bool,
}

struct VerifySolverFlags {
    cvc5_sygus: bool,
    relational_symmetry_breaking: bool,
}

struct VerifyDisabledChecks {
    no_ic3: bool,
    no_prop_verify: bool,
    no_fn_verify: bool,
}

struct VerifyOutputOptions {
    stream: bool,
    verbose: bool,
    debug_evidence: bool,
    report: Option<Vec<String>>,
    trace_artifact: Option<PathBuf>,
}

struct VerifyNames {
    solver: String,
    chc_solver: String,
    witness_semantics: String,
}

fn run_verify_command(mut args: VerifyCommand) -> miette::Result<()> {
    args.files = resolve_whole_spec_source_targets(args.files)
        .into_diagnostic()
        .wrap_err("failed to resolve source targets")?;
    validate_verify_solver_options(&args)?;
    let names = verify_names(&args);
    let report_request = render::parse_verify_report_request(args.output.report.clone())?;
    let config = build_verify_config(&args)?;
    let verified = match verify_files_for_cli(&args, &config) {
        Ok(verified) => verified,
        Err(diagnostics) => {
            write_failed_verify_report(&args, &names, report_request.as_ref(), &diagnostics)?;
            exit_with_diagnostics(&diagnostics, &args.files)
        }
    };
    report_diagnostics(&verified.lowered.diagnostics, &verified.lowered.sources);
    let diagnostics = verified.lowered.diagnostics.clone();
    if has_error_diagnostics(&diagnostics) {
        write_verify_report(&args, &names, report_request.as_ref(), &diagnostics, &[])?;
        std::process::exit(1);
    }
    let results = verified.results;
    write_success_verify_report(
        &args,
        &names,
        report_request.as_ref(),
        &diagnostics,
        &results,
    )?;
    write_verify_trace_artifact(&args, &names, &results)?;
    if args.output.stream {
        finish_streamed_verify_results(&results);
    } else {
        report_verify_results(
            &results,
            &verified.lowered.sources,
            args.output.verbose,
            args.output.debug_evidence,
        );
    }
    Ok(())
}

fn verify_files_for_cli(
    args: &VerifyCommand,
    config: &crate::verify::VerifyConfig,
) -> Result<driver::VerifiedFiles, Vec<Diagnostic>> {
    if !args.output.stream {
        return driver::verify_files(&args.files, config);
    }
    let lowered = driver::lower_files(&args.files)?;
    if has_error_diagnostics(&lowered.diagnostics) {
        return Err(lowered.diagnostics);
    }
    let results = {
        let sources = &lowered.sources;
        crate::verify::verify_all_with_events(&lowered.ir_program, config, |event| {
            report_verification_stream_event(
                event,
                sources,
                args.output.verbose,
                args.output.debug_evidence,
            );
        })
    };
    Ok(driver::VerifiedFiles { lowered, results })
}

fn validate_verify_solver_options(args: &VerifyCommand) -> miette::Result<()> {
    if args.solver_flags.cvc5_sygus
        && !matches!(args.solver, VerifySolver::Cvc5 | VerifySolver::Both)
    {
        return Err(miette::miette!(
            "--cvc5-sygus requires `--solver cvc5` or `--solver both`"
        ));
    }
    if matches!(args.solver, VerifySolver::Cvc5 | VerifySolver::Both) && !cvc5_available() {
        return Err(miette::miette!(
            "requested solver `{}` is not available in this build",
            match args.solver {
                VerifySolver::Cvc5 => "cvc5",
                VerifySolver::Both => "both",
                VerifySolver::Z3 | VerifySolver::Auto => unreachable!(),
            }
        ));
    }
    if matches!(args.chc_solver, VerifyChcSolver::Cvc5) && !cvc5_available() {
        return Err(miette::miette!(
            "requested CHC solver `cvc5` is not available in this build"
        ));
    }
    Ok(())
}

fn cvc5_available() -> bool {
    crate::verify::solver::is_solver_family_available(crate::verify::solver::SolverFamily::Cvc5)
}

fn verify_names(args: &VerifyCommand) -> VerifyNames {
    VerifyNames {
        solver: format!("{:?}", args.solver).to_lowercase(),
        chc_solver: format!("{:?}", args.chc_solver).to_lowercase(),
        witness_semantics: format!("{:?}", args.witness_semantics).to_lowercase(),
    }
}

fn build_verify_config(args: &VerifyCommand) -> miette::Result<crate::verify::VerifyConfig> {
    let target = args
        .target
        .as_deref()
        .map(str::parse)
        .transpose()
        .map_err(|err| miette::miette!("{err}"))?;
    let timeouts = args.timeouts.effective();
    Ok(crate::verify::VerifyConfig {
        solver_selection: solver_selection(args.solver),
        chc_selection: chc_selection(args.chc_solver),
        bounded_only: args.mode.bounded_only,
        unbounded_only: args.mode.unbounded_only,
        overall_timeout_ms: timeouts.overall.saturating_mul(1000),
        induction_timeout_ms: timeouts.induction.saturating_mul(1000),
        bmc_timeout_ms: timeouts.bmc.saturating_mul(1000),
        bmc_iterative_deepening: args.mode.bmc_iterative_deepening,
        prop_bmc_depth: timeouts.prop_bmc_depth,
        cvc5_sygus: args.solver_flags.cvc5_sygus,
        ic3_timeout_ms: timeouts.ic3.saturating_mul(1000),
        no_ic3: args.disabled_checks.no_ic3,
        no_prop_verify: args.disabled_checks.no_prop_verify,
        no_fn_verify: args.disabled_checks.no_fn_verify,
        witness_semantics: witness_semantics(args.witness_semantics),
        relational_symmetry_breaking: args.solver_flags.relational_symmetry_breaking,
        target,
    })
}

fn solver_selection(solver: VerifySolver) -> crate::verify::SolverSelection {
    match solver {
        VerifySolver::Z3 => crate::verify::SolverSelection::Z3,
        VerifySolver::Cvc5 => crate::verify::SolverSelection::Cvc5,
        VerifySolver::Auto => crate::verify::SolverSelection::Auto,
        VerifySolver::Both => crate::verify::SolverSelection::Both,
    }
}

fn chc_selection(chc_solver: VerifyChcSolver) -> crate::verify::ChcSelection {
    match chc_solver {
        VerifyChcSolver::Z3 => crate::verify::ChcSelection::Z3,
        VerifyChcSolver::Cvc5 => crate::verify::ChcSelection::Cvc5,
        VerifyChcSolver::Auto => crate::verify::ChcSelection::Auto,
    }
}

fn witness_semantics(witness_semantics: VerifyWitnessSemantics) -> crate::verify::WitnessSemantics {
    match witness_semantics {
        VerifyWitnessSemantics::Operational => crate::verify::WitnessSemantics::Operational,
        VerifyWitnessSemantics::Relational => crate::verify::WitnessSemantics::Relational,
    }
}

fn verify_report_config<'a>(
    args: &'a VerifyCommand,
    names: &'a VerifyNames,
) -> render::VerificationReportConfig<'a> {
    let timeouts = args.timeouts.effective();
    render::VerificationReportConfig {
        solver: render::VerificationSolverConfig {
            solver_name: &names.solver,
            chc_solver_name: &names.chc_solver,
        },
        mode: render::VerificationModeConfig {
            bounded_only: args.mode.bounded_only,
            unbounded_only: args.mode.unbounded_only,
            bmc_iterative_deepening: args.mode.bmc_iterative_deepening,
        },
        timeouts: render::VerificationTimeoutConfig {
            overall_secs: timeouts.overall,
            bounded_secs: timeouts.bounded,
            proof_secs: timeouts.proof,
            induction_secs: timeouts.induction,
            bmc_secs: timeouts.bmc,
            prop_bmc_depth: timeouts.prop_bmc_depth,
            ic3_secs: timeouts.ic3,
        },
        disabled_checks: render::VerificationDisabledChecks {
            no_ic3: args.disabled_checks.no_ic3,
            no_prop_verify: args.disabled_checks.no_prop_verify,
            no_fn_verify: args.disabled_checks.no_fn_verify,
        },
        witness_semantics: &names.witness_semantics,
        target: args.target.as_deref(),
    }
}

fn write_failed_verify_report(
    args: &VerifyCommand,
    names: &VerifyNames,
    request: Option<&render::VerifyReportRequest>,
    diagnostics: &[Diagnostic],
) -> miette::Result<()> {
    if !contains_load_io_diagnostics(diagnostics) {
        write_verify_report(args, names, request, diagnostics, &[])?;
    }
    Ok(())
}

fn write_verify_report(
    args: &VerifyCommand,
    names: &VerifyNames,
    request: Option<&render::VerifyReportRequest>,
    diagnostics: &[Diagnostic],
    results: &[crate::verify::VerificationResult],
) -> miette::Result<Option<PathBuf>> {
    let Some(request) = request else {
        return Ok(None);
    };
    let path = render::write_verification_report(render::VerificationReportInput {
        request,
        files: &args.files,
        config: verify_report_config(args, names),
        diagnostics,
        results,
    })?;
    Ok(Some(path))
}

fn write_success_verify_report(
    args: &VerifyCommand,
    names: &VerifyNames,
    request: Option<&render::VerifyReportRequest>,
    diagnostics: &[Diagnostic],
    results: &[crate::verify::VerificationResult],
) -> miette::Result<()> {
    if let Some(report_path) = write_verify_report(args, names, request, diagnostics, results)? {
        println!("Report written to {}", report_path.display());
    }
    Ok(())
}

fn write_verify_trace_artifact(
    args: &VerifyCommand,
    names: &VerifyNames,
    results: &[crate::verify::VerificationResult],
) -> miette::Result<()> {
    let Some(path) = args.output.trace_artifact.as_ref() else {
        return Ok(());
    };
    let timeouts = args.timeouts.effective();
    let artifact_config = crate::artifact::VerifyArtifactConfig {
        solver: &names.solver,
        chc_solver: &names.chc_solver,
        bounded_only: args.mode.bounded_only,
        unbounded_only: args.mode.unbounded_only,
        overall_timeout_ms: timeouts.overall.saturating_mul(1000),
        bounded_timeout_ms: timeouts.bounded.saturating_mul(1000),
        proof_timeout_ms: timeouts.proof.saturating_mul(1000),
        induction_timeout_ms: timeouts.induction.saturating_mul(1000),
        bmc_timeout_ms: timeouts.bmc.saturating_mul(1000),
        bmc_iterative_deepening: args.mode.bmc_iterative_deepening,
        ic3_timeout_ms: timeouts.ic3.saturating_mul(1000),
        no_ic3: args.disabled_checks.no_ic3,
        no_prop_verify: args.disabled_checks.no_prop_verify,
        no_fn_verify: args.disabled_checks.no_fn_verify,
        witness_semantics: &names.witness_semantics,
        target: args.target.as_deref(),
    };
    let artifacts = crate::artifact::verification_trace_artifacts(results, &artifact_config);
    let bundle = crate::artifact::TraceArtifactBundle::new(
        &args.files,
        crate::artifact::ReplayInfo::from_current_process(),
        artifacts,
    );
    crate::artifact::write_trace_artifact_bundle(path, &bundle)?;
    println!(
        "Trace artifact written to {} ({} artifact{})",
        path.display(),
        bundle.artifacts().len(),
        if bundle.artifacts().len() == 1 {
            ""
        } else {
            "s"
        }
    );
    Ok(())
}

fn report_verify_results(
    results: &[crate::verify::VerificationResult],
    sources: &[(String, String)],
    verbose: bool,
    debug_evidence: bool,
) {
    if results.is_empty() {
        println!("No verification targets found.");
        return;
    }
    let mut all_passed = true;
    for result in results {
        render::report_verification_result(result, sources, verbose, debug_evidence);
        if result.is_failure() {
            all_passed = false;
        }
    }
    if !all_passed {
        std::process::exit(1);
    }
}

fn report_verification_stream_event(
    event: &crate::verify::VerificationStreamEvent,
    sources: &[(String, String)],
    verbose: bool,
    debug_evidence: bool,
) {
    if let crate::verify::VerificationStreamEvent::ResultReady { result } = event {
        render::report_verification_result(result, sources, verbose, debug_evidence);
    }
}

fn finish_streamed_verify_results(results: &[crate::verify::VerificationResult]) {
    if results.is_empty() {
        println!("No verification targets found.");
    }
    if results
        .iter()
        .any(crate::verify::VerificationResult::is_failure)
    {
        std::process::exit(1);
    }
}

fn run_simulate_command(args: SimulateArgs) -> miette::Result<()> {
    let SimulateArgs {
        files,
        steps,
        seed,
        slots,
        scope,
        system,
        trace_artifact,
    } = args;
    let config = crate::simulate::SimulateConfig {
        steps,
        seed,
        slots_per_entity: slots,
        entity_slot_overrides: parse_simulation_scope_overrides(&scope)?,
        system,
    };
    let simulated = match driver::simulate_files(&files, &config) {
        Ok(simulated) => simulated,
        Err(diagnostics) => exit_with_diagnostics(&diagnostics, &files),
    };
    report_diagnostics(&simulated.lowered.diagnostics, &simulated.lowered.sources);
    if has_error_diagnostics(&simulated.lowered.diagnostics) {
        std::process::exit(1);
    }
    write_simulation_trace_artifact(trace_artifact.as_ref(), &files, slots, &config, &simulated)?;
    print!("{}", simulated.result.render_text());
    if matches!(
        simulated.result.termination,
        crate::simulate::SimulationTermination::Deadlock { .. }
    ) {
        std::process::exit(1);
    }
    Ok(())
}

fn write_simulation_trace_artifact(
    path: Option<&PathBuf>,
    files: &[PathBuf],
    slots: usize,
    config: &crate::simulate::SimulateConfig,
    simulated: &driver::SimulatedFiles,
) -> miette::Result<()> {
    let Some(path) = path else {
        return Ok(());
    };
    let artifact = crate::artifact::simulation_trace_artifact(
        simulated.result.clone(),
        &crate::artifact::SimulationArtifactConfig {
            slots_per_entity: slots,
            system: config.system.clone(),
        },
    );
    let bundle = crate::artifact::TraceArtifactBundle::new(
        files,
        crate::artifact::ReplayInfo::from_current_process(),
        vec![artifact],
    );
    crate::artifact::write_trace_artifact_bundle(path, &bundle)?;
    println!("Trace artifact written to {}", path.display());
    Ok(())
}

fn run_trace_command(args: TraceArgs) -> miette::Result<()> {
    let TraceArgs {
        file,
        artifact,
        command,
    } = args;
    let bundle = crate::artifact::read_trace_artifact_bundle(&file)?;
    match command.unwrap_or(TraceCommand::List) {
        TraceCommand::List => print!("{}", crate::artifact::render_trace_artifact_list(&bundle)),
        TraceCommand::Draw => print_selected_trace_artifact(&bundle, artifact, TraceRender::Draw)?,
        TraceCommand::State { index } => {
            print_selected_trace_artifact(&bundle, artifact, TraceRender::State(index))?;
        }
        TraceCommand::Diff { from, to } => {
            print_selected_trace_artifact(&bundle, artifact, TraceRender::Diff(from, to))?;
        }
        TraceCommand::Json => print_selected_trace_artifact(&bundle, artifact, TraceRender::Json)?,
    }
    Ok(())
}

enum TraceRender {
    Draw,
    State(usize),
    Diff(usize, usize),
    Json,
}

fn print_selected_trace_artifact(
    bundle: &crate::artifact::TraceArtifactBundle,
    artifact: usize,
    render: TraceRender,
) -> miette::Result<()> {
    let selected = crate::artifact::select_trace_artifact(bundle, artifact)
        .map_err(|err| miette::miette!("{err}"))?;
    match render {
        TraceRender::Draw => print!(
            "{}",
            crate::artifact::render_trace_artifact_draw(selected)
                .map_err(|err| miette::miette!("{err}"))?
        ),
        TraceRender::State(index) => print!(
            "{}",
            crate::artifact::render_trace_artifact_state(selected, index)
                .map_err(|err| miette::miette!("{err}"))?
        ),
        TraceRender::Diff(from, to) => print!(
            "{}",
            crate::artifact::render_trace_artifact_diff(selected, from, to)
                .map_err(|err| miette::miette!("{err}"))?
        ),
        TraceRender::Json => println!(
            "{}",
            crate::artifact::render_trace_artifact_json(selected)
                .map_err(|err| miette::miette!("{err}"))?
        ),
    }
    Ok(())
}

fn run_qa_command(script: PathBuf, spec_dir: Option<PathBuf>, format: &str) {
    let json_mode = format == "json";
    let mut hooks = QaRunnerHooks;
    let scripts = match resolve_qa_script_targets(script) {
        Ok(scripts) => scripts,
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    };
    let group_by_script = scripts.len() > 1 && !json_mode;
    let mut aggregate = crate::qa::runner::QARunResult {
        passed: 0,
        failed: 0,
        executed: 0,
        output: Vec::new(),
        diagnostics: Vec::new(),
    };
    let mut any_script_failed = false;

    for script in &scripts {
        if group_by_script {
            println!("== {} ==", script.display());
        }
        let result = crate::qa::runner::run_qa_script_with_hooks(
            script,
            spec_dir.as_deref(),
            json_mode,
            &mut hooks,
        );
        for line in &result.output {
            println!("{line}");
        }
        if !result.diagnostics.is_empty() {
            let sources = std::fs::read_to_string(script)
                .map(|source| vec![(script.display().to_string(), source)])
                .unwrap_or_default();
            report_diagnostics(&result.diagnostics, &sources);
        }
        if result.failed > 0 || result.executed == 0 {
            any_script_failed = true;
        }
        aggregate.passed += result.passed;
        aggregate.failed += result.failed;
        aggregate.executed += result.executed;
        aggregate.output.extend(result.output);
        aggregate.diagnostics.extend(result.diagnostics);
    }

    if any_script_failed {
        print_qa_summary(&aggregate, json_mode);
        std::process::exit(1);
    }
    print_qa_summary(&aggregate, json_mode);
}

fn resolve_qa_script_targets(script: PathBuf) -> miette::Result<Vec<PathBuf>> {
    if script.is_dir() {
        let mut scripts = Vec::new();
        collect_qa_scripts_in_directory(&script, &mut scripts)?;
        if scripts.is_empty() {
            return Err(miette::miette!(
                "no QA scripts found in {}",
                script.display()
            ));
        }
        scripts.sort();
        scripts.dedup();
        Ok(scripts)
    } else {
        Ok(vec![script])
    }
}

fn collect_qa_scripts_in_directory(
    dir: &PathBuf,
    scripts: &mut Vec<PathBuf>,
) -> miette::Result<()> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to read QA directory {}", dir.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    entries.sort();

    for path in entries {
        if path.is_dir() {
            collect_qa_scripts_in_directory(&path, scripts)?;
        } else if matches!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("qa")
        ) {
            scripts.push(
                std::fs::canonicalize(&path)
                    .into_diagnostic()
                    .wrap_err_with(|| {
                        format!("failed to canonicalize QA script {}", path.display())
                    })?,
            );
        }
    }
    Ok(())
}

fn print_qa_summary(result: &crate::qa::runner::QARunResult, json_mode: bool) {
    if let Some(message) = qa_summary_message(result, json_mode) {
        println!("{message}");
    }
}

fn qa_summary_message(result: &crate::qa::runner::QARunResult, json_mode: bool) -> Option<String> {
    (!json_mode).then(|| {
        format!(
            "\n=== QA: {} passed, {} failed ({} executed) ===",
            result.passed, result.failed, result.executed
        )
    })
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

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    fn verify_command_for_config_tests() -> VerifyCommand {
        VerifyCommand {
            files: vec![PathBuf::from("spec.ab")],
            solver: VerifySolver::Z3,
            chc_solver: VerifyChcSolver::Z3,
            timeouts: VerifyTimeouts {
                generic: None,
                bounded: None,
                proof: None,
                induction: None,
                bmc: None,
                ic3: None,
                prop_bmc_depth: 10,
            },
            mode: VerifyModeOptions {
                bounded_only: false,
                unbounded_only: false,
                bmc_iterative_deepening: true,
            },
            solver_flags: VerifySolverFlags {
                cvc5_sygus: false,
                relational_symmetry_breaking: true,
            },
            disabled_checks: VerifyDisabledChecks {
                no_ic3: true,
                no_prop_verify: false,
                no_fn_verify: false,
            },
            output: VerifyOutputOptions {
                stream: true,
                verbose: false,
                debug_evidence: false,
                report: None,
                trace_artifact: None,
            },
            witness_semantics: VerifyWitnessSemantics::Operational,
            target: None,
        }
    }

    #[test]
    fn help_documents_directory_capable_targets() {
        let mut command = Cli::command();
        for (subcommand, expected_arg) in [
            ("lex", "<FILE_OR_DIR>"),
            ("parse", "<FILE_OR_DIR>"),
            ("elaborate", "<FILES_OR_DIRS>..."),
            ("emit-ir", "<FILES_OR_DIRS>..."),
            ("export-temporal", "<FILES_OR_DIRS>..."),
            ("verify", "<FILES_OR_DIRS>..."),
            ("qa", "<SCRIPT_OR_DIR>"),
        ] {
            let subcommand = command
                .find_subcommand_mut(subcommand)
                .unwrap_or_else(|| panic!("subcommand {subcommand}"));
            let help = subcommand.render_long_help().to_string();
            assert!(
                help.contains(expected_arg),
                "help should document {expected_arg}: {help}"
            );
        }
    }

    #[test]
    fn whole_spec_source_targets_expand_directories_deterministically() {
        let dir = tempfile::tempdir().expect("tempdir");
        let nested = dir.path().join("nested");
        std::fs::create_dir(&nested).expect("create nested dir");
        let root = dir.path().join("a_root.ab");
        let nested_source = nested.join("z_nested.ab");
        std::fs::write(&nested_source, "module Nested\n").expect("write nested source");
        std::fs::write(&root, "module Root\n").expect("write root source");
        std::fs::write(dir.path().join("ignored.qa"), "ask entities\n").expect("write qa");

        let resolved = resolve_whole_spec_source_targets(vec![dir.path().to_path_buf()])
            .expect("resolve source directory");

        assert_eq!(
            resolved,
            vec![
                std::fs::canonicalize(&root).expect("canonicalize root"),
                std::fs::canonicalize(&nested_source).expect("canonicalize nested source"),
            ]
        );
    }

    #[test]
    fn file_by_file_source_targets_expand_directories_deterministically() {
        let dir = tempfile::tempdir().expect("tempdir");
        let nested = dir.path().join("nested");
        std::fs::create_dir(&nested).expect("create nested dir");
        let root = dir.path().join("a_root.ab");
        let nested_source = nested.join("z_nested.ab");
        std::fs::write(&nested_source, "module Nested\n").expect("write nested source");
        std::fs::write(&root, "module Root\n").expect("write root source");
        std::fs::write(dir.path().join("ignored.qa"), "ask entities\n").expect("write qa");

        let resolved = resolve_file_by_file_source_targets(dir.path().to_path_buf())
            .expect("resolve source directory");

        assert_eq!(
            resolved,
            vec![
                std::fs::canonicalize(&root).expect("canonicalize root"),
                std::fs::canonicalize(&nested_source).expect("canonicalize nested source"),
            ]
        );
    }

    #[test]
    fn qa_script_targets_expand_directories_deterministically() {
        let dir = tempfile::tempdir().expect("tempdir");
        let nested = dir.path().join("nested");
        std::fs::create_dir(&nested).expect("create nested dir");
        let first = dir.path().join("a.qa");
        let second = nested.join("b.qa");
        std::fs::write(&second, "ask systems\n").expect("write nested qa");
        std::fs::write(&first, "ask entities\n").expect("write first qa");
        std::fs::write(nested.join("ignored.txt"), "ask types\n").expect("write ignored");

        let resolved =
            resolve_qa_script_targets(dir.path().to_path_buf()).expect("resolve qa directory");

        assert_eq!(
            resolved,
            vec![
                std::fs::canonicalize(&first).expect("canonicalize first"),
                std::fs::canonicalize(&second).expect("canonicalize second"),
            ]
        );
    }

    #[test]
    fn qa_script_targets_reject_empty_directories() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("ignored.txt"), "ask entities\n").expect("write ignored");

        let error =
            resolve_qa_script_targets(dir.path().to_path_buf()).expect_err("empty qa dir errors");

        assert!(
            error.to_string().contains("no QA scripts found"),
            "expected empty QA directory error, got: {error}"
        );
    }

    #[test]
    fn verify_stream_flag_does_not_change_solver_config() {
        let args = verify_command_for_config_tests();

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.solver_selection, crate::verify::SolverSelection::Z3);
        assert_eq!(config.chc_selection, crate::verify::ChcSelection::Z3);
        assert_eq!(config.target, None);
    }

    #[test]
    fn verify_names_normalize_solver_and_witness_display_names() {
        let mut args = verify_command_for_config_tests();
        args.solver = VerifySolver::Auto;
        args.chc_solver = VerifyChcSolver::Auto;
        args.witness_semantics = VerifyWitnessSemantics::Relational;

        let names = verify_names(&args);

        assert_eq!(names.solver, "auto");
        assert_eq!(names.chc_solver, "auto");
        assert_eq!(names.witness_semantics, "relational");
    }

    #[test]
    fn verify_solver_options_reject_cvc5_sygus_without_cvc5_solver_selection() {
        let mut args = verify_command_for_config_tests();
        args.solver = VerifySolver::Z3;
        args.solver_flags.cvc5_sygus = true;

        let error = validate_verify_solver_options(&args)
            .expect_err("cvc5 SyGuS requires a cvc5-capable solver");

        assert!(
            error
                .to_string()
                .contains("--cvc5-sygus requires `--solver cvc5` or `--solver both`"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn verify_solver_options_accept_default_z3_without_cvc5_sygus() {
        let mut args = verify_command_for_config_tests();
        args.solver = VerifySolver::Z3;
        args.solver_flags.cvc5_sygus = false;

        validate_verify_solver_options(&args).expect("plain z3 solver options should be valid");
    }

    #[test]
    fn verify_solver_options_accept_cvc5_solver_when_available() {
        if !cvc5_available() {
            return;
        }
        let mut args = verify_command_for_config_tests();
        args.solver = VerifySolver::Cvc5;

        validate_verify_solver_options(&args).expect("available cvc5 solver should be valid");
    }

    #[test]
    fn verify_solver_options_accept_cvc5_chc_solver_when_available() {
        if !cvc5_available() {
            return;
        }
        let mut args = verify_command_for_config_tests();
        args.chc_solver = VerifyChcSolver::Cvc5;

        validate_verify_solver_options(&args).expect("available cvc5 CHC solver should be valid");
    }

    #[test]
    fn verify_timeout_policy_uses_generic_timeout_without_granular_overrides() {
        let mut args = verify_command_for_config_tests();
        args.timeouts.generic = Some(7);

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.overall_timeout_ms, 7_000);
        assert_eq!(config.induction_timeout_ms, 7_000);
        assert_eq!(config.bmc_timeout_ms, 7_000);
        assert_eq!(config.ic3_timeout_ms, 7_000);
    }

    #[test]
    fn verify_timeout_policy_prefers_class_timeout_over_generic_timeout() {
        let mut args = verify_command_for_config_tests();
        args.timeouts.generic = Some(7);
        args.timeouts.bounded = Some(3);
        args.timeouts.proof = Some(11);

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.overall_timeout_ms, 11_000);
        assert_eq!(config.induction_timeout_ms, 11_000);
        assert_eq!(config.bmc_timeout_ms, 3_000);
        assert_eq!(config.ic3_timeout_ms, 11_000);
    }

    #[test]
    fn verify_timeout_policy_prefers_backend_specific_timeout_over_class_timeout() {
        let mut args = verify_command_for_config_tests();
        args.timeouts.generic = Some(7);
        args.timeouts.bounded = Some(3);
        args.timeouts.proof = Some(11);
        args.timeouts.induction = Some(13);
        args.timeouts.bmc = Some(5);
        args.timeouts.ic3 = Some(17);

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.overall_timeout_ms, 17_000);
        assert_eq!(config.induction_timeout_ms, 13_000);
        assert_eq!(config.bmc_timeout_ms, 5_000);
        assert_eq!(config.ic3_timeout_ms, 17_000);
    }

    #[test]
    fn verify_timeout_policy_defaults_to_short_bounded_and_longer_proof_timeouts() {
        let args = verify_command_for_config_tests();

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.overall_timeout_ms, 120_000);
        assert_eq!(config.induction_timeout_ms, 120_000);
        assert_eq!(config.bmc_timeout_ms, 30_000);
        assert_eq!(config.ic3_timeout_ms, 120_000);
    }

    #[test]
    fn verify_timeout_policy_zero_backend_timeout_disables_overall_timeout() {
        let mut args = verify_command_for_config_tests();
        args.timeouts.induction = Some(0);
        args.timeouts.bmc = Some(5);
        args.timeouts.ic3 = Some(7);

        let config = build_verify_config(&args).expect("verify config");

        assert_eq!(config.overall_timeout_ms, 0);
        assert_eq!(config.induction_timeout_ms, 0);
        assert_eq!(config.bmc_timeout_ms, 5_000);
        assert_eq!(config.ic3_timeout_ms, 7_000);
    }

    #[test]
    fn parse_simulation_scope_overrides_trims_names_and_overwrites_duplicates() {
        let overrides = parse_simulation_scope_overrides(&[
            " Account =2".to_owned(),
            "Session=10".to_owned(),
            "Account=3".to_owned(),
        ])
        .expect("scope overrides");

        assert_eq!(overrides.get("Account"), Some(&3));
        assert_eq!(overrides.get("Session"), Some(&10));
        assert_eq!(overrides.len(), 2);
    }

    #[test]
    fn parse_simulation_scope_overrides_rejects_malformed_entries() {
        for entry in ["Account", "=2", "Account=-1", "Account=abc"] {
            let error = parse_simulation_scope_overrides(&[entry.to_owned()])
                .expect_err("malformed scope override should fail");
            assert!(
                error.to_string().contains("invalid `--scope"),
                "unexpected error for {entry}: {error}"
            );
        }
    }

    #[test]
    fn qa_summary_message_renders_text_summary_and_suppresses_json_mode() {
        let result = crate::qa::runner::QARunResult {
            passed: 2,
            failed: 1,
            executed: 3,
            output: Vec::new(),
            diagnostics: Vec::new(),
        };

        assert_eq!(
            qa_summary_message(&result, false).as_deref(),
            Some("\n=== QA: 2 passed, 1 failed (3 executed) ===")
        );
        assert_eq!(qa_summary_message(&result, true), None);
    }
}
