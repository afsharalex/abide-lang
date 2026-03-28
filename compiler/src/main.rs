use clap::Parser as ClapParser;
use miette::{IntoDiagnostic, WrapErr};
use std::path::PathBuf;

#[derive(ClapParser)]
#[command(name = "abide", about = "Abide specification language compiler")]
#[allow(clippy::struct_excessive_bools)]
struct Cli {
    /// Source file to compile
    file: PathBuf,

    /// Only run the lexer and print tokens
    #[arg(long)]
    lex_only: bool,

    /// Only run the parser and print AST
    #[arg(long)]
    parse_only: bool,

    /// Run elaboration only
    #[arg(long)]
    elaborate_only: bool,

    /// Emit IR as JSON
    #[arg(long)]
    emit_ir: bool,

    /// Run bounded model checking on verify blocks
    // TODO: Planned — migrate to subcommand-based CLI (`abide verify spec.abide`)
    #[arg(long)]
    verify: bool,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let src = std::fs::read_to_string(&cli.file)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to read {}", cli.file.display()))?;

    let tokens = abide::lex::lex(&src).map_err(|errors| {
        // Report the first lex error
        errors.into_iter().next().unwrap()
    })?;

    if cli.lex_only {
        for (token, span) in &tokens {
            println!("{span:?}  {token}");
        }
        return Ok(());
    }

    let mut parser = abide::parse::Parser::new(tokens);
    let program = parser.parse_program()?;

    if cli.parse_only {
        println!("{program:#?}");
        return Ok(());
    }

    if cli.elaborate_only {
        let (result, errors) = abide::elab::elaborate(&program);
        for err in &errors {
            eprintln!("{err}");
        }
        println!("{result:#?}");
        return Ok(());
    }

    if cli.emit_ir {
        let (result, errors) = abide::elab::elaborate(&program);
        for err in &errors {
            eprintln!("{err}");
        }
        let ir_program = abide::ir::lower(&result);
        let json = abide::ir::emit_json(&ir_program);
        println!("{json}");
        return Ok(());
    }

    // Default: run full pipeline with verification
    let (result, errors) = abide::elab::elaborate(&program);
    for err in &errors {
        eprintln!("{err}");
    }
    let ir_program = abide::ir::lower(&result);

    if cli.verify || !cli.lex_only && !cli.parse_only && !cli.elaborate_only && !cli.emit_ir {
        let results = abide::verify::verify_all(&ir_program);
        if results.is_empty() {
            println!("No verify blocks found.");
        } else {
            let mut all_passed = true;
            for result in &results {
                println!("{result}");
                if matches!(
                    result,
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

    Ok(())
}
