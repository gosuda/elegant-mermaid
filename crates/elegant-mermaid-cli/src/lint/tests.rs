use super::{fix_source, run};
use elegant_mermaid::{FixSafety, LintConfig};
use std::io;
use std::path::PathBuf;

struct TestDir(PathBuf);

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn fix_persists_utf8_repair_without_rule_edits() -> io::Result<()> {
    let path = std::env::temp_dir().join(format!("emd-lint-repair-{}", std::process::id()));
    std::fs::create_dir(&path)?;
    let dir = TestDir(path);
    let cases: [(&str, &[u8]); 2] = [
        ("diagram.mmd", b"flowchart LR\n%% \xff\nA --> B\n"),
        (
            "document.md",
            b"# Notes\n\n```mermaid\nflowchart LR\n%% \xff\nA --> B\n```\n",
        ),
    ];
    for (name, source) in cases {
        let path = dir.0.join(name);
        std::fs::write(&path, source)?;
        let fixed = fix_source(name, source, &LintConfig::default(), FixSafety::Safe);
        assert_eq!(fixed.applied, 0, "the fixture needs only UTF-8 repair");
        let args = [
            "--fix".to_owned(),
            "--no-config".to_owned(),
            "--color".to_owned(),
            "never".to_owned(),
            path.to_string_lossy().into_owned(),
        ];
        assert_eq!(
            run(&args, &crate::environment()),
            (String::new(), String::new(), 0)
        );
        assert_eq!(std::fs::read(&path)?, fixed.text.as_bytes(), "{name}");
    }
    Ok(())
}

#[test]
fn fix_preserves_markdown_host_bytes() -> io::Result<()> {
    let cases: [(&str, &[u8], &[u8]); 10] = [
        ("prose", b"Caf\xe9\n", b"Caf\xe9\n"),
        (
            "clean",
            b"Caf\xe9\n```mermaid\nflowchart LR\nA --> B\n```\nTail\xff\n",
            b"Caf\xe9\n```mermaid\nflowchart LR\nA --> B\n```\nTail\xff\n",
        ),
        (
            "fixed",
            b"Caf\xe9\r\n```mermaid\r\nflowchart LR\r\n%% \xe2\x82\r\nA -> B\r\n```\r\nTail\xff\r\n",
            b"Caf\xe9\r\n```mermaid\r\nflowchart LR\r\n%% \xef\xbf\xbd\r\nA --> B\r\n```\r\nTail\xff\r\n",
        ),
        (
            "nested",
            b"Prose\xff\n> - Notes\n>   ```mermaid \xfe\n>   flowchart LR\n>   %% \xe2\x82\n>   A -> B\n>   ```\nTail\xff\n",
            b"Prose\xff\n> - Notes\n>   ```mermaid \xfe\n>   flowchart LR\n>   %% \xef\xbf\xbd\n>   A --> B\n>   ```\nTail\xff\n",
        ),
        (
            "empty",
            b"Prose\xff\n```mermaid\n```\n",
            b"Prose\xff\n```mermaid\n```\n",
        ),
        (
            "unclosed",
            b"Prose\xff\n```mermaid\nflowchart LR\nA -> B",
            b"Prose\xff\n```mermaid\nflowchart LR\nA --> B",
        ),
        ("foreign", b"```text\nCaf\xe9\n```\n", b"```text\nCaf\xe9\n```\n"),
        (
            "multiple",
            b"Before\xff\n```mermaid\nflowchart LR\nA -> B\n```\nBetween\xe2\x82\n~~~mmd\nflowchart LR\nC -> D\n~~~\nAfter\xfe\n",
            b"Before\xff\n```mermaid\nflowchart LR\nA --> B\n```\nBetween\xe2\x82\n~~~mmd\nflowchart LR\nC --> D\n~~~\nAfter\xfe\n",
        ),
        (
            "container-exit",
            b"Before\xff\n> ```mermaid\n> flowchart LR\n> A -> B\nAfter\xe9\n",
            b"Before\xff\n> ```mermaid\n> flowchart LR\n> A --> B\nAfter\xe9\n",
        ),
        (
            "indented-quote",
            b"Before\xff\n  > ```mermaid\n  > flowchart LR\n  > %% \xe2\x82\n  > A -> B\n  > ```\nAfter\xfe\n",
            b"Before\xff\n  > ```mermaid\n  > flowchart LR\n  > %% \xef\xbf\xbd\n  > A --> B\n  > ```\nAfter\xfe\n",
        ),
    ];
    for (name, before, after) in cases {
        assert_fixed_host_bytes(name, before, after, false)?;
    }
    Ok(())
}

#[test]
fn fix_preserves_host_bytes_around_line_deletion() -> io::Result<()> {
    let before = b"Before\xff\r\n> ```mermaid\r\n> flowchart LR\r\n>   A --> B\r\n>   end\r\n> ```\r\nAfter\xfe\r\n";
    let after =
        b"Before\xff\r\n> ```mermaid\r\n> flowchart LR\r\n>   A --> B\r\n> ```\r\nAfter\xfe\r\n";
    assert_fixed_host_bytes("line-deletion", before, after, true)
}

#[test]
fn fix_preserves_host_bytes_when_line_endings_join() -> io::Result<()> {
    let before = b"Before\xff\n> ```mermaid\n> flowchart LR\r> end\n\nAfter\xfe\n";
    let after = b"Before\xff\n> ```mermaid\n> flowchart LR\r\nAfter\xfe\n";
    assert_fixed_host_bytes("joined-line-endings", before, after, true)
}

fn assert_fixed_host_bytes(
    name: &str,
    before: &[u8],
    after: &[u8],
    unsafe_fixes: bool,
) -> io::Result<()> {
    let path = std::env::temp_dir().join(format!("emd-lint-host-{name}-{}", std::process::id()));
    std::fs::create_dir(&path)?;
    let dir = TestDir(path);
    let path = dir.0.join("document.md");
    std::fs::write(&path, before)?;
    let check_args = [
        "--no-config".to_owned(),
        "--color".to_owned(),
        "never".to_owned(),
        path.to_string_lossy().into_owned(),
    ];
    let mut fix_args = vec!["--fix".to_owned()];
    if unsafe_fixes {
        fix_args.push("--unsafe-fixes".to_owned());
    }
    fix_args.extend_from_slice(&check_args);
    let fixed = run(&fix_args, &crate::environment());
    assert_eq!(std::fs::read(&path)?, after, "{name}");
    assert_eq!(fixed.2, 1, "{name}: {fixed:?}");
    assert!(fixed.1.is_empty(), "{name}: {fixed:?}");
    assert!(fixed.0.contains("source/invalid-utf8"), "{name}: {fixed:?}");
    let checked = run(&check_args, &crate::environment());
    assert_eq!(
        fixed, checked,
        "{name}: diagnostics must describe the written bytes"
    );
    Ok(())
}
