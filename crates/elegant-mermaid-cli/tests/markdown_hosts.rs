use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

type TestResult = Result<(), Box<dyn std::error::Error>>;
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Result<Self, std::io::Error> {
        let path = std::env::temp_dir().join(format!(
            "emd-markdown-hosts-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path)?;
        Ok(Self(path))
    }
    fn check(&self, args: &[&str]) -> Result<Output, std::io::Error> {
        let binary = std::env::var_os("EMD_BIN").unwrap_or_default();
        assert!(
            !binary.is_empty(),
            "EMD_BIN is not set; run just rust-check"
        );
        Command::new(binary)
            .current_dir(&self.0)
            .args(args)
            .output()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn markdown_hosts_map_nested_blocks_and_multiple_diagnostics() -> TestResult {
    let fixture = Fixture::new()?;
    let source = "# hé😀\n\n> - ```mermaid\n>   flowchart LR\n>   A -> B\n>   ```\n\n:::mermaid\nflowchart LR\nC -> D\n:::\n";
    std::fs::write(fixture.0.join("host.md"), source)?;
    let output = fixture.check(&["check", "host.md", "--output-format", "json"])?;
    assert_eq!(output.status.code(), Some(1));
    assert!(
        output.stderr.is_empty(),
        "markdown_hosts_map_nested_blocks_and_multiple_diagnostics: required output.stderr.is_empty(); observed: {:?}",
        output.stderr
    );
    let json = String::from_utf8(output.stdout)?;
    assert!(
        json.contains("\"path\":\"host.md\",\"kind\":null"),
        "markdown_hosts_map_nested_blocks_and_multiple_diagnostics: required json.contains(\"\\\"path\\\":\\\"host.md\\\",\\\"kind\\\":null\"); observed: {:?}",
        json
    );
    for (arrow, line, column) in [("A ->", 5, 7), ("C ->", 10, 3)] {
        let start = source.find(arrow).ok_or("missing arrow")? + 2;
        assert!(
            json.contains(&format!(
                "\"span\":{{\"start\":{start},\"end\":{}}}",
                start + 2
            )),
            "{json}"
        );
        assert!(
            json.contains(&format!("\"line\":{line},\"column\":{column}")),
            "{json}"
        );
        assert!(json.contains("\"new_text\":\"-->\""), "{json}");
    }
    assert!(
        json.contains("\"summary\":{\"files\":1,\"errors\":2,\"warnings\":0,\"info\":0}"),
        "markdown_hosts_map_nested_blocks_and_multiple_diagnostics: required json.contains(\"\\\"summary\\\":{{\\\"files\\\":1,\\\"errors\\\":2,\\\"warnings\\\":0,\\\"info\\\":0}}\"); observed: {:?}",
        json
    );
    let text = fixture.check(&["check", "--color", "never", "host.md"])?;
    let text = String::from_utf8(text.stdout)?;
    assert!(
        text.contains("host.md:5:7: error[flowchart/arrow-invalid]"),
        "markdown_hosts_map_nested_blocks_and_multiple_diagnostics: required text.contains(\"host.md:5:7: error[flowchart/arrow-invalid]\"); observed: {:?}",
        text
    );
    assert!(
        text.contains(">   A -> B"),
        "markdown_hosts_map_nested_blocks_and_multiple_diagnostics: required text.contains(\">   A -> B\"); observed: {:?}",
        text
    );
    Ok(())
}

#[test]
fn markdown_hosts_include_clean_and_prose_files_in_walks() -> TestResult {
    let fixture = Fixture::new()?;
    for (name, source) in [
        ("a.md", "prose only\n"),
        ("b.markdown", "~~~MMD\nflowchart LR\nA --> B\n~~~\n"),
        ("c.mdx", "```{mermaid}\nflowchart LR\nA --> B\n```\n"),
        ("d.mmd", "flowchart LR\nA --> B\n"),
    ] {
        std::fs::write(fixture.0.join(name), source)?;
    }
    for directory in [".hidden", "node_modules", "target"] {
        std::fs::create_dir(fixture.0.join(directory))?;
        std::fs::write(
            fixture.0.join(directory).join("bad.md"),
            "```mermaid\nbogus\n```\n",
        )?;
    }
    let output = fixture.check(&["check", "--output-format", "json"])?;
    assert!(
        output.status.success(),
        "markdown_hosts_include_clean_and_prose_files_in_walks: required output.status.success(); observed: {:?}",
        output.status
    );
    assert!(
        output.stderr.is_empty(),
        "markdown_hosts_include_clean_and_prose_files_in_walks: required output.stderr.is_empty(); observed: {:?}",
        output.stderr
    );
    let json = String::from_utf8(output.stdout)?;
    assert!(json.contains("\"files\":4,\"errors\":0"), "{json}");
    let positions: Vec<_> = ["a.md", "b.markdown", "c.mdx", "d.mmd"]
        .iter()
        .map(|name| json.find(name).ok_or("missing file"))
        .collect::<Result<_, _>>()?;
    assert!(
        positions.windows(2).all(|pair| pair[0] < pair[1]),
        "markdown_hosts_include_clean_and_prose_files_in_walks: required positions.windows(2).all(|pair| pair[0] < pair[1]); observed: {:?}",
        positions
    );
    let prose = fixture.check(&["check", "a.md", "--output-format", "json"])?;
    assert!(
        prose.status.success(),
        "markdown_hosts_include_clean_and_prose_files_in_walks: required prose.status.success(); observed: {:?}",
        prose.status
    );
    let json = String::from_utf8(prose.stdout)?;
    assert!(json.contains("\"kind\":null,\"diagnostics\":[]"), "{json}");
    assert!(
        json.contains("\"files\":1,\"errors\":0"),
        "markdown_hosts_include_clean_and_prose_files_in_walks: required json.contains(\"\\\"files\\\":1,\\\"errors\\\":0\"); observed: {:?}",
        json
    );
    Ok(())
}

#[test]
fn markdown_hosts_repair_before_extracting_and_mapping() -> TestResult {
    for source in [
        &b"prose \xff\n```mermaid\nflowchart LR\nA -> B\n```\n"[..],
        &b"> ```mermaid\n> flowchart LR\n> A[\xff]\n> B -> C\n> ```\n"[..],
    ] {
        let fixture = Fixture::new()?;
        std::fs::write(fixture.0.join("invalid.md"), source)?;
        let output = fixture.check(&["check", "invalid.md", "--output-format", "json"])?;
        assert_eq!(output.status.code(), Some(1));
        assert!(
            output.stderr.is_empty(),
            "markdown_hosts_repair_before_extracting_and_mapping: required output.stderr.is_empty(); observed: {:?}",
            output.stderr
        );
        let json = String::from_utf8(output.stdout)?;
        let (repaired, first_bad) = elegant_mermaid::source::repair_utf8(source);
        let bad = first_bad.ok_or("missing invalid byte")?;
        assert_eq!(
            json.matches("\"code\":\"source/invalid-utf8\"").count(),
            1,
            "{json}"
        );
        assert!(
            json.contains(&format!("\"span\":{{\"start\":{bad},\"end\":{}}}", bad + 3)),
            "{json}"
        );
        let arrow = repaired.find("->").ok_or("missing arrow")?;
        let span = format!("\"span\":{{\"start\":{arrow},\"end\":{}}}", arrow + 2);
        assert_eq!(json.matches(&span).count(), 2, "{json}");
        let index = elegant_mermaid::source::LineIndex::new(&repaired);
        let position = index.position(arrow);
        assert!(
            json.contains(&format!(
                "\"line\":{},\"column\":{}",
                position.line, position.column
            )),
            "{json}"
        );
        assert!(json.contains("\"new_text\":\"-->\""), "{json}");
    }
    Ok(())
}
