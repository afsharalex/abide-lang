use std::path::{Path, PathBuf};

use crate::diagnostic::{Diagnostic, DiagnosticSink};
use miette::{IntoDiagnostic, WrapErr};
use serde::Serialize;

use crate::diagnostic::LexError;
use crate::elab;
use crate::ir::types::IRProgram;
use crate::ir::{self, LowerDiagnostics};
use crate::loader::{self};
use crate::parse::{ParseOutput, Parser};
use crate::simulate::{self, SimulateConfig, SimulationResult};
use crate::verify::{self, VerificationResult, VerifyConfig};

pub type SourceMap = Vec<(String, String)>;

pub struct ParseFileResult {
    pub source: String,
    pub program: crate::ast::Program,
    pub diagnostics: Vec<Diagnostic>,
}

pub struct ElaboratedFiles {
    pub result: elab::types::ElabResult,
    pub sources: SourceMap,
    pub diagnostics: Vec<Diagnostic>,
}

pub struct LoweredFiles {
    pub result: elab::types::ElabResult,
    pub sources: SourceMap,
    pub ir_program: IRProgram,
    pub lower_diagnostics: LowerDiagnostics,
    pub diagnostics: Vec<Diagnostic>,
}

pub struct VerifiedFiles {
    pub lowered: LoweredFiles,
    pub results: Vec<VerificationResult>,
}

pub struct SimulatedFiles {
    pub lowered: LoweredFiles,
    pub result: SimulationResult,
}

#[derive(Debug, Clone, Serialize)]
pub struct VerifyTemporalExportBlock {
    pub name: String,
    pub systems: Vec<String>,
    pub asserts: Vec<crate::verify::VerifyTemporalExport>,
}

pub struct TemporalExportedFiles {
    pub lowered: LoweredFiles,
    pub verifies: Vec<VerifyTemporalExportBlock>,
}

pub fn read_file(path: &Path) -> miette::Result<String> {
    std::fs::read_to_string(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to read {}", path.display()))
}

pub fn lex_source(src: &str) -> Result<Vec<(crate::lex::Token, crate::span::Span)>, Vec<LexError>> {
    crate::lex::lex(src)
}

pub fn parse_source(src: &str) -> Result<ParseOutput, Vec<LexError>> {
    crate::parse::parse_string_recovering(src)
}

pub fn parse_file(path: &Path) -> miette::Result<ParseFileResult> {
    let source = read_file(path)?;
    let tokens = lex_source(&source).map_err(|errors| {
        miette::miette!(
            "failed to lex {}: {}",
            path.display(),
            errors
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ")
        )
    })?;
    let mut parser = Parser::new(tokens);
    let (program, parse_errors) = parser.parse_program_recovering();
    let diagnostics = parse_errors
        .into_iter()
        .map(|error| error.to_diagnostic().in_file(path.display().to_string()))
        .collect();
    Ok(ParseFileResult {
        source,
        program,
        diagnostics,
    })
}

pub fn read_sources_for_diagnostics(paths: &[PathBuf]) -> SourceMap {
    paths
        .iter()
        .filter_map(|p| {
            let src = std::fs::read_to_string(p).ok()?;
            let key = std::fs::canonicalize(p)
                .map_or_else(|_| p.display().to_string(), |c| c.display().to_string());
            Some((key, src))
        })
        .collect()
}

pub fn load_and_elaborate(paths: &[PathBuf]) -> Result<ElaboratedFiles, Vec<Diagnostic>> {
    let mut sources = read_sources_for_diagnostics(paths);
    let (env, load_errors, all_paths) = loader::load_files(paths);

    for loaded_path in &all_paths {
        let key = loaded_path.display().to_string();
        if !sources.iter().any(|(name, _)| name == &key) {
            if let Ok(src) = std::fs::read_to_string(loaded_path) {
                sources.push((key, src));
            }
        }
    }

    if !load_errors.is_empty() {
        return Err(flatten_load_diagnostics(&load_errors));
    }

    let include_load_errors = env.include_load_errors.clone();
    let had_include_errors = !include_load_errors.is_empty();
    let (result, mut errors) = elab::elaborate_env(env);
    if had_include_errors {
        errors.push(crate::elab::error::ElabError::new(
            crate::elab::error::ErrorKind::UndefinedRef,
            "one or more included files failed to load (see above)",
            String::new(),
        ));
    }

    let mut diagnostics = DiagnosticSink::new();
    diagnostics.extend(flatten_load_diagnostics(&include_load_errors));
    diagnostics.extend(
        errors
            .iter()
            .map(crate::elab::error::ElabError::to_diagnostic),
    );

    Ok(ElaboratedFiles {
        result,
        sources,
        diagnostics: diagnostics.into_sorted_deduped(),
    })
}

pub fn lower_files(paths: &[PathBuf]) -> Result<LoweredFiles, Vec<Diagnostic>> {
    let elaborated = load_and_elaborate(paths)?;
    let (ir_program, lower_diagnostics) = ir::lower(&elaborated.result);
    let mut diagnostics = DiagnosticSink::new();
    diagnostics.extend(elaborated.diagnostics.iter().cloned());
    diagnostics.extend(lower_diagnostics.diagnostics.iter().cloned());
    Ok(LoweredFiles {
        result: elaborated.result,
        sources: elaborated.sources,
        ir_program,
        lower_diagnostics,
        diagnostics: diagnostics.into_sorted_deduped(),
    })
}

pub fn verify_files(
    paths: &[PathBuf],
    config: &VerifyConfig,
) -> Result<VerifiedFiles, Vec<Diagnostic>> {
    let lowered = lower_files(paths)?;
    let results = verify::verify_all(&lowered.ir_program, config);
    Ok(VerifiedFiles { lowered, results })
}

pub fn simulate_files(
    paths: &[PathBuf],
    config: &SimulateConfig,
) -> Result<SimulatedFiles, Vec<Diagnostic>> {
    let lowered = lower_files(paths)?;
    let result = simulate::simulate_program(&lowered.ir_program, config)
        .map_err(|message| vec![Diagnostic::error(message)])?;
    Ok(SimulatedFiles { lowered, result })
}

pub fn export_temporal_files(paths: &[PathBuf]) -> Result<TemporalExportedFiles, Vec<Diagnostic>> {
    let lowered = lower_files(paths)?;
    let defs = crate::verify::defenv::DefEnv::from_ir(&lowered.ir_program);
    let verifies = lowered
        .ir_program
        .verifies
        .iter()
        .map(|verify| VerifyTemporalExportBlock {
            name: verify.name.clone(),
            systems: verify
                .systems
                .iter()
                .map(|system| system.name.clone())
                .collect(),
            asserts: crate::verify::export_verify_temporal_formulas(verify, &defs),
        })
        .collect();
    Ok(TemporalExportedFiles { lowered, verifies })
}

fn flatten_load_diagnostics(errors: &[crate::loader::LoadError]) -> Vec<Diagnostic> {
    let mut sink = DiagnosticSink::new();
    for error in errors {
        sink.extend(error.diagnostics());
    }
    sink.into_sorted_deduped()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn parse_file_exposes_shared_diagnostics_with_file_tag() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("broken.ab");
        let mut file = std::fs::File::create(&path).expect("create file");
        writeln!(file, "entity Broken {{ field: }}").expect("write file");
        let path_text = path.display().to_string();

        let parsed = parse_file(&path).expect("parse file");
        assert!(
            !parsed.diagnostics.is_empty(),
            "expected shared diagnostics for broken file"
        );
        assert!(
            parsed
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.file.as_deref() == Some(path_text.as_str())),
            "expected file tag on all diagnostics: {:?}",
            parsed.diagnostics
        );
    }

    #[test]
    fn load_and_elaborate_surfaces_nonfatal_include_diagnostics() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("root.ab");
        let mut file = std::fs::File::create(&root).expect("create file");
        writeln!(file, "include \"missing.ab\"").expect("write file");

        let elaborated =
            load_and_elaborate(std::slice::from_ref(&root)).expect("include errors are nonfatal");
        let diagnostics = elaborated.diagnostics;

        assert!(
            diagnostics
                .iter()
                .any(
                    |diagnostic| diagnostic.code.as_deref() == Some("abide::load::io")
                        && diagnostic.message.contains("missing.ab")
                ),
            "expected shared load diagnostic for missing include, got: {diagnostics:?}"
        );
    }

    #[test]
    fn export_temporal_files_emits_compiled_verify_temporal_formulas() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("temporal.ab");
        let mut file = std::fs::File::create(&path).expect("create file");
        writeln!(
            file,
            "verify liveness {{\n\
               assert always (false implies eventually true)\n\
             }}"
        )
        .expect("write file");

        let exported = export_temporal_files(std::slice::from_ref(&path)).expect("export temporal");
        assert_eq!(exported.verifies.len(), 1);
        let verify = &exported.verifies[0];
        assert_eq!(verify.name, "liveness");
        assert_eq!(verify.asserts.len(), 1);
        let assert0 = &verify.asserts[0];
        assert!(assert0.contains_temporal);
        assert!(assert0.contains_liveness);
        assert!(assert0.spot.is_some(), "expected Spot-style export payload");
        let spot = assert0.spot.as_ref().expect("spot export");
        assert!(
            spot.spot_formula.contains("G("),
            "expected always to render in exported formula: {}",
            spot.spot_formula
        );
        assert!(
            spot.spot_formula.contains("F("),
            "expected eventually to render in exported formula: {}",
            spot.spot_formula
        );
    }
}
