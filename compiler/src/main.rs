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
        eprintln!("elaboration not yet implemented");
        std::process::exit(1);
    }

    if cli.emit_ir {
        eprintln!("IR emission not yet implemented");
        std::process::exit(1);
    }

    // Default: full pipeline (not yet implemented)
    eprintln!("full pipeline not yet implemented — use --lex-only or --parse-only");
    std::process::exit(1);
}
