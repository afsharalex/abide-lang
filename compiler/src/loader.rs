//! Multi-file loader for the Abide compiler.
//!
//! Loads one or more source files, resolves `include` declarations
//! transitively, and collects all declarations into a single `Env`.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::elab::collect;
use crate::elab::env::Env;
use crate::elab::error::{ElabError, ErrorKind};

/// Load one or more source files into a single elaboration environment.
///
/// Parses each file independently, collects declarations into a shared `Env`,
/// and resolves `include` directives transitively with cycle detection.
/// Each top-level file gets its own module scope. Included files inherit
/// the including file's module (per DDR-028).
/// Load one or more source files, collecting all errors.
///
/// Always returns a partial Env (with whatever declarations parsed
/// successfully) plus any load/parse errors. The caller decides
/// whether to proceed based on the error list.
/// Returns `(env, errors, all_loaded_paths)`.
/// `all_loaded_paths` includes both CLI inputs and transitively included files,
/// for building a complete source map for diagnostics.
pub fn load_files(paths: &[PathBuf]) -> (Env, Vec<LoadError>, Vec<PathBuf>) {
    let mut env = Env::new();
    let mut visited = HashSet::new();
    let mut errors = Vec::new();

    for path in paths {
        match canonicalize(path) {
            Ok(canonical) => {
                if let Err(e) = load_file_into(&mut env, &canonical, &mut visited, None) {
                    errors.push(e);
                }
            }
            Err(e) => errors.push(e),
        }
    }

    let all_paths: Vec<PathBuf> = visited.into_iter().collect();
    (env, errors, all_paths)
}

/// Load a single file into an existing Env, resolving includes transitively.
///
/// `parent_module`: if Some, this file was included by a file declaring that module.
/// Included files without their own `module` declaration inherit the parent's module.
#[allow(clippy::too_many_lines)]
fn load_file_into(
    env: &mut Env,
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    parent_module: Option<&str>,
) -> Result<(), LoadError> {
    if !visited.insert(path.to_owned()) {
        return Ok(());
    }

    let src = std::fs::read_to_string(path).map_err(|e| LoadError::Io {
        path: path.to_owned(),
        error: e.to_string(),
    })?;

    let tokens = crate::lex::lex(&src).map_err(|errors| LoadError::Lex {
        path: path.to_owned(),
        errors,
    })?;

    let mut parser = crate::parse::Parser::new(tokens);
    let (program, parse_errors) = parser.parse_program_recovering();
    if !parse_errors.is_empty() {
        return Err(LoadError::ParseErrors {
            path: path.to_owned(),
            errors: parse_errors,
        });
    }

    // Scope module context per-file: each file gets its own module context
    // so declarations are tagged correctly.
    let saved_module = env.module_name.take();

    // If this file is included and the parent has a module, pre-set it
    // so declarations without their own `module` decl inherit the parent's.
    if let Some(pm) = parent_module {
        env.module_name = Some(pm.to_string());
    }

    let errors_before = env.errors.len();
    collect::collect_into(env, &program);

    // Tag any new errors from this file's collection with the file path.
    let file_str = path.display().to_string();
    for err in &mut env.errors[errors_before..] {
        if err.file.is_none() {
            err.file = Some(file_str.clone());
        }
    }

    // This file's effective module (either from its own `module` decl or inherited)
    let file_module = env.module_name.clone();

    // Restore the previous module context if it existed.
    // For the first file (saved=None), keep the file's module as the root.
    // For subsequent files, restore so each file gets its own scope.
    if saved_module.is_some() {
        env.module_name = saved_module;
    }
    // else: keep file_module (first file sets the root module)

    // Process include directives: resolve paths relative to this file's directory.
    // Included files inherit this file's module (DDR-028: "contents become part
    // of current module").
    let base_dir = path.parent().unwrap_or(Path::new("."));
    let include_paths: Vec<String> = program
        .decls
        .iter()
        .filter_map(|d| {
            if let crate::ast::TopDecl::Include(inc) = d {
                Some(inc.path.clone())
            } else {
                None
            }
        })
        .collect();

    for inc_path in &include_paths {
        let resolved = base_dir.join(inc_path);
        match canonicalize(&resolved) {
            Ok(canonical) => {
                if visited.contains(&canonical) {
                    continue;
                }
                // Included files inherit this file's module.
                // Don't short-circuit on error — continue processing sibling includes.
                if let Err(e) = load_file_into(env, &canonical, visited, file_module.as_deref()) {
                    match e {
                        LoadError::ParseErrors {
                            path: err_path,
                            errors,
                        } => {
                            // Preserve each parse error with its span for diagnostic rendering
                            let file_tag = err_path.display().to_string();
                            for pe in &errors {
                                let (msg, pe_span) = match pe {
                                    crate::diagnostic::ParseError::Expected {
                                        expected,
                                        found,
                                        span,
                                        ..
                                    } => {
                                        (format!("expected {expected}, found {found}"), Some(*span))
                                    }
                                    crate::diagnostic::ParseError::UnexpectedEof { span } => {
                                        ("unexpected end of input".to_string(), Some(*span))
                                    }
                                    crate::diagnostic::ParseError::General {
                                        msg, span, ..
                                    } => (msg.clone(), Some(*span)),
                                };
                                let err = if let Some(s) = pe_span {
                                    let abide_span = crate::span::Span {
                                        start: s.offset(),
                                        end: s.offset() + s.len(),
                                    };
                                    ElabError::with_span(
                                        ErrorKind::UndefinedRef,
                                        format!("in included file '{inc_path}': {msg}"),
                                        String::new(),
                                        abide_span,
                                    )
                                    .in_file(file_tag.clone())
                                } else {
                                    ElabError::new(
                                        ErrorKind::UndefinedRef,
                                        format!("in included file '{inc_path}': {msg}"),
                                        String::new(),
                                    )
                                };
                                env.errors.push(err);
                            }
                        }
                        other => {
                            env.errors.push(ElabError::new(
                                ErrorKind::UndefinedRef,
                                format!("error loading included file '{inc_path}': {other}"),
                                String::new(),
                            ));
                        }
                    }
                }
            }
            Err(e) => {
                env.errors.push(ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!(
                        "include file not found: '{}' (resolved to '{}')",
                        inc_path,
                        resolved.display()
                    ),
                    e.to_string(),
                ));
            }
        }
    }

    Ok(())
}

fn canonicalize(path: &Path) -> Result<PathBuf, LoadError> {
    std::fs::canonicalize(path).map_err(|e| LoadError::Io {
        path: path.to_owned(),
        error: e.to_string(),
    })
}

/// Errors that can occur during file loading (before elaboration).
#[derive(Debug)]
pub enum LoadError {
    Io {
        path: PathBuf,
        error: String,
    },
    Lex {
        path: PathBuf,
        errors: Vec<crate::diagnostic::LexError>,
    },
    ParseErrors {
        path: PathBuf,
        errors: Vec<crate::diagnostic::ParseError>,
    },
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io { path, error } => {
                write!(f, "failed to read {}: {error}", path.display())
            }
            LoadError::Lex { path, errors } => {
                write!(f, "lex error in {}: {:?}", path.display(), errors)
            }
            LoadError::ParseErrors { path, errors } => {
                write!(f, "{} parse error(s) in {}", errors.len(), path.display())
            }
        }
    }
}

impl std::error::Error for LoadError {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn bad_include_does_not_block_good_sibling() {
        // Create a temp directory with three files:
        // - main.abide: includes both bad.abide and good.abide
        // - bad.abide: has a parse error
        // - good.abide: is valid
        let dir = tempfile::tempdir().expect("create tempdir");

        let bad_path = dir.path().join("bad.abide");
        let mut bad = std::fs::File::create(&bad_path).unwrap();
        writeln!(bad, "import \"something\" as X").unwrap(); // removed keyword → parse error

        let good_path = dir.path().join("good.abide");
        let mut good = std::fs::File::create(&good_path).unwrap();
        writeln!(good, "type GoodType = A | B").unwrap();

        let main_path = dir.path().join("main.abide");
        let mut main_f = std::fs::File::create(&main_path).unwrap();
        writeln!(main_f, "module Test").unwrap();
        writeln!(main_f, "include \"bad.abide\"").unwrap();
        writeln!(main_f, "include \"good.abide\"").unwrap();

        let (env, load_errors, _all_paths) = load_files(&[main_path]);

        // The bad include should produce errors but not block the good include
        assert!(
            load_errors.is_empty(),
            "top-level load should succeed; include errors go to env.errors: {load_errors:?}"
        );

        // env.errors should contain parse error diagnostics from the bad include
        let include_errors: Vec<_> = env
            .errors
            .iter()
            .filter(|e| e.message.contains("included file"))
            .collect();
        assert!(
            !include_errors.is_empty(),
            "should have include parse error in env.errors: {:?}",
            env.errors
        );

        // The parse error should have a span (preserved from ParseError)
        assert!(
            include_errors.iter().any(|e| e.span.is_some()),
            "include parse errors should preserve spans: {:?}",
            include_errors
        );

        // The good include's type should be present in the env
        let has_good_type = env.types.values().any(|ty| {
            if let crate::elab::types::Ty::Enum(name, _) = ty {
                name == "GoodType"
            } else {
                false
            }
        });
        assert!(
            has_good_type,
            "good include's type should be loaded despite bad sibling"
        );
    }
}
