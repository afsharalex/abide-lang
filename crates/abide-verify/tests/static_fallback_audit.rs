use std::fs;
use std::path::{Path, PathBuf};

const ALLOW_MARKER: &str = "abide-audit: allow-silent-fallback -- ";

const AUDITED_ROOTS: &[&str] = &[
    "crates/abide-verify/src/verify",
    "crates/abide-ir/src/ir/lower",
    "crates/abide-sema/src/elab",
];

const DEFAULT_PATTERNS: &[&str] = &[
    ".unwrap_or_default(",
    ".unwrap_or(0)",
    ".unwrap_or(false)",
    ".unwrap_or(true)",
];

#[test]
fn verifier_lowering_code_documents_silent_fallback_patterns() {
    let workspace = workspace_root();
    let mut findings = Vec::new();

    for root in AUDITED_ROOTS {
        collect_findings(&workspace.join(root), &workspace, &mut findings);
    }

    assert!(
        findings.is_empty(),
        "silent fallback audit found undocumented risky defaults/drops:\n{}",
        findings.join("\n")
    );
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("abide-verify should live under crates/")
        .to_path_buf()
}

fn collect_findings(path: &Path, workspace: &Path, findings: &mut Vec<String>) {
    if path.is_dir() {
        let mut entries = fs::read_dir(path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
            .map(|entry| entry.expect("failed to read directory entry").path())
            .collect::<Vec<_>>();
        entries.sort();
        for entry in entries {
            collect_findings(&entry, workspace, findings);
        }
        return;
    }

    if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return;
    }

    let source = fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let lines = source.lines().collect::<Vec<_>>();
    let relative = path.strip_prefix(workspace).unwrap_or(path);

    for (index, line) in lines.iter().enumerate() {
        if risky_pattern_on_line(relative, line).is_none() {
            continue;
        }
        if has_allow_reason(line) || previous_line_has_allow_reason(&lines, index) {
            continue;
        }
        findings.push(format!(
            "{}:{}: {}",
            relative.display(),
            index + 1,
            line.trim()
        ));
    }
}

fn risky_pattern_on_line(path: &Path, line: &str) -> Option<&'static str> {
    if let Some(pattern) = DEFAULT_PATTERNS
        .iter()
        .copied()
        .find(|pattern| line.contains(pattern))
    {
        return Some(pattern);
    }

    if line.contains(".map_or(") && map_or_uses_silent_default(line) {
        return Some(".map_or(<silent default>, ...)");
    }

    if line.contains(".filter_map(") && filter_map_can_drop_verifier_semantics(path) {
        return Some(".filter_map(<drop>, ...)");
    }

    None
}

fn map_or_uses_silent_default(line: &str) -> bool {
    [
        "Ty::Error",
        "IRType::String",
        "(Vec::new(), None)",
        "\"?\"",
        "false",
        "true",
        "&[]",
        "0,",
    ]
    .iter()
    .any(|default| line.contains(default))
}

fn filter_map_can_drop_verifier_semantics(path: &Path) -> bool {
    let path = path.to_string_lossy();
    [
        "crates/abide-verify/src/verify/defenv.rs",
        "crates/abide-verify/src/verify/explicit.rs",
        "crates/abide-verify/src/verify/harness",
        "crates/abide-verify/src/verify/property.rs",
        "crates/abide-verify/src/verify/relational.rs",
        "crates/abide-verify/src/verify/relation_sat.rs",
        "crates/abide-verify/src/verify/scene.rs",
        "crates/abide-verify/src/verify/temporal_relational.rs",
        "crates/abide-verify/src/verify/walkers.rs",
        "crates/abide-ir/src/ir/lower",
        "crates/abide-sema/src/elab/check",
        "crates/abide-sema/src/elab/collect",
        "crates/abide-sema/src/elab/resolve",
    ]
    .iter()
    .any(|audited_path| path.contains(audited_path))
}

fn previous_line_has_allow_reason(lines: &[&str], index: usize) -> bool {
    index
        .checked_sub(1)
        .and_then(|previous| lines.get(previous))
        .is_some_and(|line| has_allow_reason(line))
}

fn has_allow_reason(line: &str) -> bool {
    line.split_once(ALLOW_MARKER)
        .is_some_and(|(_, reason)| reason.trim().len() >= 12)
}
