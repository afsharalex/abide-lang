//! Multi-file loader for the Abide compiler.
//!
//! Loads one or more source files, resolves `include` declarations
//! transitively, and collects all declarations into a single `Env`.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::elab::collect;
use crate::elab::env::Env;

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
    let mut include_stack = Vec::new();
    let mut errors = Vec::new();

    for path in paths {
        match canonicalize(path) {
            Ok(canonical) => {
                if let Err(e) =
                    load_file_into(&mut env, &canonical, &mut visited, &mut include_stack, None)
                {
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
///
/// `include_stack` tracks the current chain of files being processed (for cycle
/// detection). `visited` tracks all files ever loaded (for diamond dedup).
/// A cycle is a back-edge in the include stack; a diamond is the same file
/// reached via different paths — only cycles are errors.
#[allow(clippy::too_many_lines)]
fn load_file_into(
    env: &mut Env,
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    include_stack: &mut Vec<PathBuf>,
    parent_module: Option<&str>,
) -> Result<(), LoadError> {
    if !visited.insert(path.to_owned()) {
        return Ok(());
    }

    // Push before, pop after — the closure ensures cleanup on all exit
    // paths (? returns, early returns, normal completion).
    include_stack.push(path.to_owned());
    let result = load_file_inner(env, path, visited, include_stack, parent_module);
    include_stack.pop();
    result
}

/// Inner logic for `load_file_into`, separated so the caller can
/// guarantee push/pop around every exit path.
#[allow(clippy::too_many_lines)]
fn load_file_inner(
    env: &mut Env,
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    include_stack: &mut Vec<PathBuf>,
    parent_module: Option<&str>,
) -> Result<(), LoadError> {
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
    // Mark as inherited so the collector allows the file's own `module`
    // declaration to override it without "conflicting module" error.
    if let Some(pm) = parent_module {
        env.module_name = Some(pm.to_string());
        env.module_inherited = true;
    }

    let saved_file = env.current_file.take();
    env.current_file = Some(path.display().to_string());

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

    // Restore the previous module/file context.
    // For the first file (saved=None), keep the file's module/file as the root.
    // For subsequent files, restore so each file gets its own scope.
    if saved_module.is_some() {
        env.module_name = saved_module;
        env.module_inherited = false;
    }
    // else: keep file_module (first file sets the root module)
    if saved_file.is_some() {
        env.current_file = saved_file;
    }
    // else: keep current_file (first file sets the root file for resolve/check tagging)

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
                // Check for circular include: if the canonical path is already
                // on the include stack, we have a cycle (A → B → A).
                // This is distinct from diamond dedup (visited set) — diamonds
                // are fine, cycles are errors.
                if include_stack.contains(&canonical) {
                    let mut chain: Vec<PathBuf> = include_stack
                        .iter()
                        .skip_while(|p| **p != canonical)
                        .cloned()
                        .collect();
                    chain.push(canonical);
                    env.include_load_errors
                        .push(LoadError::CircularInclude { chain });
                    continue;
                }
                if visited.contains(&canonical) {
                    continue;
                }
                // Included files inherit this file's module.
                // Don't short-circuit on error — continue processing sibling includes.
                if let Err(e) = load_file_into(
                    env,
                    &canonical,
                    visited,
                    include_stack,
                    file_module.as_deref(),
                ) {
                    // Preserve all include load errors as structured LoadError
                    // for miette rendering (parse, lex, and IO errors alike).
                    env.include_load_errors.push(e);
                }
            }
            Err(_) => {
                // File not found — create a structured Io error
                env.include_load_errors.push(LoadError::Io {
                    path: resolved,
                    error: format!("include file not found: '{inc_path}'"),
                });
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
#[derive(Debug, Clone, thiserror::Error)]
pub enum LoadError {
    #[error("failed to read {}: {error}", path.display())]
    Io { path: PathBuf, error: String },

    #[error("{} lex error(s) in {}", errors.len(), path.display())]
    Lex {
        path: PathBuf,
        errors: Vec<crate::diagnostic::LexError>,
    },

    #[error("{} parse error(s) in {}", errors.len(), path.display())]
    ParseErrors {
        path: PathBuf,
        errors: Vec<crate::diagnostic::ParseError>,
    },

    #[error("{}", format_circular_chain(chain))]
    CircularInclude { chain: Vec<PathBuf> },
}

fn format_circular_chain(chain: &[PathBuf]) -> String {
    let names: Vec<String> = chain.iter().map(|p| p.display().to_string()).collect();
    format!("circular include detected: {}", names.join(" → "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn circular_include_detected() {
        let dir = tempfile::tempdir().expect("create tempdir");

        let a_path = dir.path().join("a.ab");
        let mut a = std::fs::File::create(&a_path).unwrap();
        writeln!(a, "include \"b.ab\"").unwrap();

        let b_path = dir.path().join("b.ab");
        let mut b = std::fs::File::create(&b_path).unwrap();
        writeln!(b, "include \"a.ab\"").unwrap();

        let (env, load_errors, _) = load_files(&[a_path]);
        assert!(load_errors.is_empty(), "top-level should succeed");

        let circular: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::CircularInclude { .. }))
            .collect();
        assert_eq!(
            circular.len(),
            1,
            "should detect exactly one circular include: {:?}",
            env.include_load_errors
        );

        if let LoadError::CircularInclude { chain } = &circular[0] {
            assert!(
                chain.len() >= 2,
                "chain should have at least 2 entries (cycle): {chain:?}"
            );
            // Chain should end where it started
            assert_eq!(
                chain.first().unwrap().file_name(),
                chain.last().unwrap().file_name(),
                "chain should be a cycle"
            );
        }
    }

    #[test]
    fn self_include_detected() {
        let dir = tempfile::tempdir().expect("create tempdir");

        let path = dir.path().join("self.ab");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(f, "include \"self.ab\"").unwrap();

        let (env, load_errors, _) = load_files(&[path]);
        assert!(load_errors.is_empty());

        let circular: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::CircularInclude { .. }))
            .collect();
        assert_eq!(circular.len(), 1, "self-include should be detected");
    }

    #[test]
    fn deep_cycle_detected() {
        let dir = tempfile::tempdir().expect("create tempdir");

        let a_path = dir.path().join("a.ab");
        let mut a = std::fs::File::create(&a_path).unwrap();
        writeln!(a, "include \"b.ab\"").unwrap();

        let b_path = dir.path().join("b.ab");
        let mut b = std::fs::File::create(&b_path).unwrap();
        writeln!(b, "include \"c.ab\"").unwrap();

        let c_path = dir.path().join("c.ab");
        let mut c = std::fs::File::create(&c_path).unwrap();
        writeln!(c, "include \"a.ab\"").unwrap();

        let (env, load_errors, _) = load_files(&[a_path]);
        assert!(load_errors.is_empty());

        let circular: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::CircularInclude { .. }))
            .collect();
        assert_eq!(circular.len(), 1, "3-file cycle should be detected");

        if let LoadError::CircularInclude { chain } = &circular[0] {
            assert!(
                chain.len() >= 3,
                "chain should have at least 3 entries: {chain:?}"
            );
        }
    }

    #[test]
    fn diamond_include_not_error() {
        // A includes B and C; both B and C include D.
        // This is a diamond (not a cycle) — should not error.
        let dir = tempfile::tempdir().expect("create tempdir");

        let d_path = dir.path().join("d.ab");
        let mut d = std::fs::File::create(&d_path).unwrap();
        writeln!(d, "enum Shared = X | Y").unwrap();

        let b_path = dir.path().join("b.ab");
        let mut b = std::fs::File::create(&b_path).unwrap();
        writeln!(b, "include \"d.ab\"").unwrap();

        let c_path = dir.path().join("c.ab");
        let mut c = std::fs::File::create(&c_path).unwrap();
        writeln!(c, "include \"d.ab\"").unwrap();

        let a_path = dir.path().join("a.ab");
        let mut a = std::fs::File::create(&a_path).unwrap();
        writeln!(a, "include \"b.ab\"").unwrap();
        writeln!(a, "include \"c.ab\"").unwrap();

        let (env, load_errors, _) = load_files(&[a_path]);
        assert!(load_errors.is_empty());
        assert!(
            env.include_load_errors.is_empty(),
            "diamond should not produce errors: {:?}",
            env.include_load_errors
        );
    }

    #[test]
    fn cycle_does_not_block_siblings() {
        // A includes B (which cycles back to A) and C (valid).
        // C should still load successfully.
        let dir = tempfile::tempdir().expect("create tempdir");

        let a_path = dir.path().join("a.ab");
        let mut a = std::fs::File::create(&a_path).unwrap();
        writeln!(a, "include \"b.ab\"").unwrap();
        writeln!(a, "include \"c.ab\"").unwrap();

        let b_path = dir.path().join("b.ab");
        let mut b = std::fs::File::create(&b_path).unwrap();
        writeln!(b, "include \"a.ab\"").unwrap();

        let c_path = dir.path().join("c.ab");
        let mut c = std::fs::File::create(&c_path).unwrap();
        writeln!(c, "enum GoodType = A | B").unwrap();

        let (env, load_errors, _) = load_files(&[a_path]);
        assert!(load_errors.is_empty());

        // Should have one circular error from B → A
        let circular: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::CircularInclude { .. }))
            .collect();
        assert_eq!(circular.len(), 1, "should detect cycle through B");

        // C should still have been loaded
        let has_good_type = env.types.values().any(|ty| {
            if let crate::elab::types::Ty::Enum(name, _) = ty {
                name == "GoodType"
            } else {
                false
            }
        });
        assert!(
            has_good_type,
            "good sibling C should still load despite cycle through B"
        );
    }

    #[test]
    fn failed_include_does_not_poison_stack() {
        // A includes bad.ab (parse error) and then includes good.ab
        // which also includes bad.ab. The failed load of bad.ab must
        // not leave it on the include stack, otherwise good.ab's include
        // of bad.ab would be falsely reported as a circular include.
        let dir = tempfile::tempdir().expect("create tempdir");

        let bad_path = dir.path().join("bad.ab");
        let mut bad = std::fs::File::create(&bad_path).unwrap();
        writeln!(bad, "import \"broken\"").unwrap(); // parse error

        let good_path = dir.path().join("good.ab");
        let mut good = std::fs::File::create(&good_path).unwrap();
        writeln!(good, "include \"bad.ab\"").unwrap();

        let main_path = dir.path().join("main.ab");
        let mut main_f = std::fs::File::create(&main_path).unwrap();
        writeln!(main_f, "include \"bad.ab\"").unwrap();
        writeln!(main_f, "include \"good.ab\"").unwrap();

        let (env, load_errors, _) = load_files(&[main_path]);
        assert!(load_errors.is_empty(), "top-level should succeed");

        // Should have parse errors for bad.ab but NO circular include errors
        let circular: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::CircularInclude { .. }))
            .collect();
        assert!(
            circular.is_empty(),
            "failed include must not cause false circular detection: {circular:?}"
        );
    }

    #[test]
    fn bad_include_does_not_block_good_sibling() {
        // Create a temp directory with three files:
        // - main.ab: includes both bad.ab and good.ab
        // - bad.ab: has a parse error
        // - good.ab: is valid
        let dir = tempfile::tempdir().expect("create tempdir");

        let bad_path = dir.path().join("bad.ab");
        let mut bad = std::fs::File::create(&bad_path).unwrap();
        writeln!(bad, "import \"something\" as X").unwrap(); // removed keyword → parse error

        let good_path = dir.path().join("good.ab");
        let mut good = std::fs::File::create(&good_path).unwrap();
        writeln!(good, "enum GoodType = A | B").unwrap();

        let main_path = dir.path().join("main.ab");
        let mut main_f = std::fs::File::create(&main_path).unwrap();
        writeln!(main_f, "module Test").unwrap();
        writeln!(main_f, "include \"bad.ab\"").unwrap();
        writeln!(main_f, "include \"good.ab\"").unwrap();

        let (env, load_errors, _all_paths) = load_files(&[main_path]);

        // The bad include should produce errors but not block the good include
        assert!(
            load_errors.is_empty(),
            "top-level load should succeed; include errors go to env.include_load_errors: {load_errors:?}"
        );

        // env.include_load_errors should contain the structured parse error from the bad include
        let include_errors: Vec<_> = env
            .include_load_errors
            .iter()
            .filter(|e| matches!(e, LoadError::ParseErrors { .. }))
            .collect();
        assert!(
            !include_errors.is_empty(),
            "should have structured ParseErrors in include_load_errors: {:?}",
            env.include_load_errors
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
