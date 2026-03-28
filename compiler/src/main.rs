use clap::{Parser as ClapParser, Subcommand};
use miette::{IntoDiagnostic, WrapErr};
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

    /// Elaborate a source file and print result
    Elaborate { file: PathBuf },

    /// Emit IR as JSON
    #[command(name = "emit-ir")]
    EmitIr { file: PathBuf },

    /// Verify a specification: bounded model checking, scene checking, theorem proving
    Verify {
        file: PathBuf,

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
            let program = parser.parse_program()?;
            println!("{program:#?}");
        }
        Command::Elaborate { file } => {
            let (result, errors) = parse_and_elaborate(&file)?;
            for err in &errors {
                eprintln!("{err}");
            }
            println!("{result:#?}");
        }
        Command::EmitIr { file } => {
            let (result, errors) = parse_and_elaborate(&file)?;
            for err in &errors {
                eprintln!("{err}");
            }
            let ir_program = abide::ir::lower(&result);
            let json = abide::ir::emit_json(&ir_program);
            println!("{json}");
        }
        Command::Verify {
            file,
            bounded_only,
            unbounded_only,
            induction_timeout,
            bmc_timeout,
            progress,
        } => {
            let (result, errors) = parse_and_elaborate(&file)?;
            for err in &errors {
                eprintln!("{err}");
            }
            let ir_program = abide::ir::lower(&result);

            let config = abide::verify::VerifyConfig {
                bounded_only,
                unbounded_only,
                induction_timeout_ms: induction_timeout.saturating_mul(1000),
                bmc_timeout_ms: bmc_timeout.saturating_mul(1000),
                prop_bmc_depth: DEFAULT_PROP_BMC_DEPTH,
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

fn parse_and_elaborate(
    path: &PathBuf,
) -> miette::Result<(
    abide::elab::types::ElabResult,
    Vec<abide::elab::error::ElabError>,
)> {
    let src = read_file(path)?;
    let tokens = abide::lex::lex(&src).map_err(|errors| errors.into_iter().next().unwrap())?;
    let mut parser = abide::parse::Parser::new(tokens);
    let program = parser.parse_program()?;
    Ok(abide::elab::elaborate(&program))
}
