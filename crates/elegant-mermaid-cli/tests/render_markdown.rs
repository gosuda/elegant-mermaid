use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

type TestResult = Result<(), Box<dyn std::error::Error>>;
static NEXT: AtomicUsize = AtomicUsize::new(0);
const FIRST: &str = "flowchart LR\nA --> B\n";
const SECOND: &str = "flowchart TD\nC --> D\n";

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> std::io::Result<Self> {
        let path = std::env::temp_dir().join(format!(
            "emd-render-markdown-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path)?;
        Ok(Self(path))
    }

    fn write(&self, name: &str, bytes: impl AsRef<[u8]>) -> std::io::Result<()> {
        std::fs::write(self.0.join(name), bytes)
    }

    fn read(&self, name: &str) -> std::io::Result<Vec<u8>> {
        std::fs::read(self.0.join(name))
    }

    fn run(&self, args: &[&str]) -> std::io::Result<Output> {
        let binary =
            std::env::var_os("EMD_BIN").unwrap_or_else(|| env!("CARGO_BIN_EXE_emd").into());
        Command::new(binary)
            .current_dir(&self.0)
            .args(args)
            .env_remove("NO_COLOR")
            .env_remove("FORCE_COLOR")
            .env_remove("CLICOLOR_FORCE")
            .output()
    }

    fn two_blocks(&self) -> std::io::Result<()> {
        self.write(
            "input.md",
            format!("Before\n```mermaid\n{FIRST}```\nBetween\n~~~mmd\n{SECOND}~~~\nAfter\n"),
        )
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn success(output: &Output) {
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
}

#[test]
fn markdown_image_outputs_match_standalone_blocks() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.two_blocks()?;
    let output = fixture.run(&[
        "render",
        "input.md",
        "-o",
        "diagram.svg",
        "--color",
        "never",
    ])?;
    success(&output);
    assert!(output.stdout.is_empty());
    assert!(!fixture.0.join("diagram.svg").exists());
    for (number, source) in [(1, FIRST), (2, SECOND)] {
        fixture.write("single.mmd", source)?;
        let single = fixture.run(&["render", "single.mmd", "-e", "svg", "--color", "never"])?;
        success(&single);
        assert_eq!(
            fixture.read(&format!("diagram-{number}.svg"))?,
            single.stdout
        );
    }
    Ok(())
}

#[test]
fn markdown_artefact_directory_and_image_name_are_independent() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.two_blocks()?;
    let text = fixture.run(&[
        "render",
        "input.md",
        "-a",
        "nested/assets",
        "-e",
        "text",
        "--color",
        "never",
    ])?;
    success(&text);
    assert!(text.stdout.is_empty());
    assert!(!fixture.read("nested/assets/input-1.txt")?.is_empty());
    assert!(!fixture.read("nested/assets/input-2.txt")?.is_empty());

    let image = fixture.run(&[
        "render",
        "input.md",
        "-o",
        "unused/picture.dat",
        "-a",
        "actual",
        "-e",
        "svg",
    ])?;
    success(&image);
    assert!(!fixture.0.join("unused").exists());
    assert!(fixture.read("actual/picture-1.dat")?.starts_with(b"<svg"));
    assert!(fixture.read("actual/picture-2.dat")?.starts_with(b"<svg"));

    let current = fixture.run(&["render", "input.md", "--a=", "-e", "svg"])?;
    success(&current);
    assert!(fixture.0.join("input-1.svg").exists());
    assert!(fixture.0.join("input-2.svg").exists());
    Ok(())
}

#[test]
fn markdown_host_rewrites_preserve_raw_prose_containers_and_line_endings() -> TestResult {
    let before = b"Before\xff\r\n> - ```mermaid\r\n>   flowchart LR\r\n>   accTitle: Title [safe] & more!\r\n>   A --> B\r\n>   ```\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n~~~mmd\nflowchart LR\nC --> D\n~~~\nAfter\n";
    for suffix in ["md", "markdown", "mdx"] {
        let fixture = Fixture::new()?;
        let input = format!("input.{suffix}");
        let output = format!("reports/published.{suffix}");
        fixture.write(&input, before)?;
        let rendered = fixture.run(&["render", &input, "-o", &output, "--color", "never"])?;
        success(&rendered);
        assert!(rendered.stdout.is_empty());
        assert_eq!(
            fixture.read(&output)?,
            b"Before\xff\r\n> - ![Title \\[safe\\] \\& more\\!](published.assets/published-1.svg)\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n![diagram](published.assets/published-2.svg)\nAfter\n"
        );
        assert!(
            fixture
                .0
                .join("reports/published.assets/published-1.svg")
                .exists()
        );
        assert!(
            fixture
                .0
                .join("reports/published.assets/published-2.svg")
                .exists()
        );
        assert_eq!(fixture.read(&input)?, before);
    }
    Ok(())
}

#[test]
fn markdown_dotfile_hosts_keep_their_stem() -> TestResult {
    for name in [".md", ".markdown", ".mdx"] {
        let fixture = Fixture::new()?;
        fixture.write(name, format!("```mermaid\n{FIRST}```\n"))?;
        let output = fixture.run(&["render", name, "-a", "assets"])?;
        success(&output);
        assert!(fixture.0.join(format!("assets/{name}-1.svg")).exists());
    }
    Ok(())
}

#[test]
fn markdown_image_links_are_relative_and_percent_encoded() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    let output = fixture.run(&[
        "render",
        "input.md",
        "-o",
        "docs/renamed.md",
        "-a",
        "assets/a b#%()é",
    ])?;
    success(&output);
    assert_eq!(
        fixture.read("docs/renamed.md")?,
        b"![diagram](../assets/a%20b%23%25%28%29%C3%A9/renamed-1.svg)\n"
    );
    assert!(fixture.0.join("assets/a b#%()é/renamed-1.svg").exists());
    Ok(())
}

#[test]
fn markdown_unclosed_blocks_preserve_the_final_line_ending() -> TestResult {
    for (before, after) in [
        (
            "Before\n> :::mermaid\n> flowchart LR\r> A --> B\rAfter\n",
            "Before\n> ![diagram](out.assets/out-1.svg)\rAfter\n",
        ),
        (
            "Before\n  > ```mermaid\r\n  > flowchart LR\r\n  > A --> B\r\nAfter\n",
            "Before\n  > ![diagram](out.assets/out-1.svg)\r\nAfter\n",
        ),
        (
            "Before\n```mermaid\nflowchart LR\nA --> B",
            "Before\n![diagram](out.assets/out-1.svg)",
        ),
    ] {
        let fixture = Fixture::new()?;
        fixture.write("input.md", before)?;
        let output = fixture.run(&["render", "input.md", "-o", "out.md"])?;
        success(&output);
        assert_eq!(fixture.read("out.md")?, after.as_bytes());
    }
    Ok(())
}

#[test]
fn markdown_host_rewrite_supports_png() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "out.mdx", "-e", "png", "-s", "1",
    ])?;
    success(&output);
    assert_eq!(
        fixture.read("out.mdx")?,
        b"![diagram](out.assets/out-1.png)\n"
    );
    assert!(
        fixture
            .read("out.assets/out-1.png")?
            .starts_with(b"\x89PNG\r\n\x1a\n")
    );
    Ok(())
}

#[test]
fn markdown_render_usage_errors_are_explicit() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.two_blocks()?;
    fixture.write("single.mmd", FIRST)?;
    for (args, message) in [
        (
            vec!["render", "input.md"],
            "rendering Markdown input requires -o OUTPUT or -a ARTEFACT_DIR\n",
        ),
        (
            vec!["render", "single.mmd", "-a", "assets"],
            "-a requires Markdown input\n",
        ),
        (
            vec!["render", "single.mmd", "--a="],
            "-a requires Markdown input\n",
        ),
        (
            vec!["render", "input.md", "-o", "out.md", "-e", "text"],
            "invalid value text for -e; expected one of: svg, png\n",
        ),
    ] {
        let output = fixture.run(&args)?;
        assert_eq!(output.status.code(), Some(2), "{args:?}");
        assert!(output.stdout.is_empty(), "{args:?}");
        assert_eq!(output.stderr, message.as_bytes(), "{args:?}");
    }
    assert!(!fixture.0.join("assets").exists());
    assert!(!fixture.0.join("out.md").exists());
    Ok(())
}

#[test]
fn markdown_zero_blocks_and_later_parse_errors_write_nothing() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("empty.md", "prose\n```rust\nlet x = 1;\n```\n")?;
    let empty = fixture.run(&["render", "empty.md", "-o", "absent/out.md"])?;
    assert_eq!(empty.status.code(), Some(1));
    assert!(empty.stdout.is_empty());
    assert_eq!(
        empty.stderr,
        b"no Mermaid blocks found in empty.md; add a fenced code block labelled mermaid\n"
    );
    assert!(!fixture.0.join("absent").exists());

    fixture.write(
        "bad.md",
        format!("```mermaid\n{FIRST}```\n```mermaid\nflowchart LR\nC -> D\n```\n"),
    )?;
    fixture.write("out-1.svg", b"existing asset")?;
    let failed = fixture.run(&["render", "bad.md", "-o", "out.svg", "--color", "never"])?;
    assert_eq!(failed.status.code(), Some(1));
    assert!(failed.stdout.is_empty());
    assert!(
        String::from_utf8(failed.stderr)?.contains("bad.md:7:3: error[flowchart/arrow-invalid]")
    );
    assert_eq!(fixture.read("out-1.svg")?, b"existing asset");
    assert!(!fixture.0.join("out-2.svg").exists());
    Ok(())
}

#[test]
fn markdown_render_maps_all_source_diagnostics_to_host_positions() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write(
        "bad.md",
        "# hé😀\n\n> - ```mermaid\n>   flowchart LR\n>   A -> B\n>   ```\n\n:::mermaid\nflowchart LR\nC -> D\n:::\n",
    )?;
    let checked = fixture.run(&["check", "bad.md", "--color", "never"])?;
    let rendered = fixture.run(&["render", "bad.md", "-o", "out.svg", "--color", "never"])?;
    assert_eq!(checked.status.code(), Some(1));
    assert_eq!(rendered.status.code(), Some(1));
    assert!(rendered.stdout.is_empty());
    assert_eq!(rendered.stderr, checked.stdout);
    assert!(!fixture.0.join("out-1.svg").exists());
    Ok(())
}

#[test]
fn markdown_render_rejects_invalid_block_bytes_at_repaired_host_positions() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write(
        "invalid.md",
        b"Before\xff\n> ```mermaid\n> flowchart LR\n> %% bad \xfe\n> A --> B\n> ```\n",
    )?;
    let output = fixture.run(&["render", "invalid.md", "-o", "out.md", "--color", "never"])?;
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr)?;
    assert!(
        stderr.contains("invalid.md:4:10: error[source/invalid-utf8]"),
        "{stderr}"
    );
    assert_eq!(stderr.matches("error[source/invalid-utf8]").count(), 1);
    assert!(!fixture.0.join("out.md").exists());
    assert!(!fixture.0.join("out.assets").exists());
    Ok(())
}

#[test]
fn markdown_render_applies_config_limits_to_each_block_only() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("config.yaml", "maxTextSize: 30\n")?;
    fixture.write(
        "input.md",
        format!("{}\n```mermaid\n{FIRST}```\n", "prose ".repeat(100)),
    )?;
    let output = fixture.run(&["render", "input.md", "-o", "out.svg", "-c", "config.yaml"])?;
    success(&output);
    assert!(fixture.0.join("out-1.svg").exists());
    Ok(())
}
