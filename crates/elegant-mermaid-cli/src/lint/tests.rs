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
