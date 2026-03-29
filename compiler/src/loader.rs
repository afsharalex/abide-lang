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
pub fn load_files(paths: &[PathBuf]) -> Result<Env, LoadError> {
    let mut env = Env::new();
    let mut visited = HashSet::new();

    for path in paths {
        let canonical = canonicalize(path)?;
        // Each top-level file gets independent module scoping.
        load_file_into(&mut env, &canonical, &mut visited, None)?;
    }

    Ok(env)
}

/// Load a single file into an existing Env, resolving includes transitively.
///
/// `parent_module`: if Some, this file was included by a file declaring that module.
/// Included files without their own `module` declaration inherit the parent's module.
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
    let program = parser.parse_program().map_err(|e| LoadError::Parse {
        path: path.to_owned(),
        error: e,
    })?;

    // Scope module context per-file: each file gets its own module context
    // so declarations are tagged correctly.
    let saved_module = env.module_name.take();

    // If this file is included and the parent has a module, pre-set it
    // so declarations without their own `module` decl inherit the parent's.
    if let Some(pm) = parent_module {
        env.module_name = Some(pm.to_string());
    }

    collect::collect_into(env, &program);

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
                // Included files inherit this file's module
                load_file_into(env, &canonical, visited, file_module.as_deref())?;
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
    Parse {
        path: PathBuf,
        error: crate::diagnostic::ParseError,
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
            LoadError::Parse { path, error } => {
                write!(f, "parse error in {}: {error:?}", path.display())
            }
        }
    }
}

impl std::error::Error for LoadError {}
