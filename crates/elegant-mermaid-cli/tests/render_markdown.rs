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

#[test]
fn markdown_late_layout_failure_keeps_existing_assets_and_host() -> TestResult {
    let fixture = Fixture::new()?;
    let overflow = "pie\n\"A\" : 99999999999\n";
    fixture.write("single.mmd", overflow)?;
    let single = fixture.run(&["render", "single.mmd", "-e", "svg"])?;
    assert_eq!(single.status.code(), Some(1));
    assert_eq!(single.stderr, b"arithmetic overflow\n");
    fixture.write(
        "input.md",
        format!("```mermaid\n{FIRST}```\n```mermaid\n{overflow}```\n"),
    )?;
    fixture.write("out-1.svg", b"existing image")?;
    fixture.write("out.md", b"existing host")?;
    let output = fixture.run(&["render", "input.md", "-o", "out.md", "-a", "."])?;
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, single.stderr);
    assert_eq!(fixture.read("out-1.svg")?, b"existing image");
    assert_eq!(fixture.read("out.md")?, b"existing host");
    assert!(!fixture.0.join("out-2.svg").exists());
    Ok(())
}

#[test]
fn markdown_output_directory_operands_are_not_renamed() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.two_blocks()?;
    std::fs::create_dir(fixture.0.join("directory.svg"))?;
    for path in [".", "directory.svg", "missing/", "missing/.", "missing/.."] {
        let output = fixture.run(&["render", "input.md", "-o", path, "-e", "svg"])?;
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert_eq!(
            output.stderr,
            format!("cannot write {path}: is a directory\n").as_bytes()
        );
    }
    assert!(!fixture.0.join("directory-1.svg").exists());
    assert!(!fixture.0.join("missing").exists());
    Ok(())
}

#[test]
fn markdown_write_failures_keep_mapped_diagnostics() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write(
        "input.md",
        "```mermaid\n---\nconfig:\n  fontFamily: serif\n---\nflowchart LR\nA --> B\n```\n",
    )?;
    fixture.write("blocked", b"not a directory")?;
    let output = fixture.run(&[
        "render",
        "input.md",
        "-o",
        "out.md",
        "-a",
        "blocked/assets",
        "--color",
        "never",
    ])?;
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr)?;
    assert!(
        stderr.contains("input.md:4:3: info[config/font-metrics-approximate]"),
        "{stderr}"
    );
    assert!(
        stderr.ends_with("cannot write out.md: not a directory\n"),
        "{stderr}"
    );
    assert!(!fixture.0.join("out.md").exists());
    assert_eq!(fixture.read("blocked")?, b"not a directory");
    Ok(())
}

#[test]
fn standalone_write_failures_keep_source_diagnostics() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write(
        "single.mmd",
        "---\nconfig:\n  fontFamily: serif\n---\nflowchart LR\nA --> B\n",
    )?;
    fixture.write("blocked", b"not a directory")?;
    let output = fixture.run(&[
        "render",
        "single.mmd",
        "-o",
        "blocked/out.svg",
        "--color",
        "never",
    ])?;
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr)?;
    assert!(
        stderr.contains("single.mmd:3:3: info[config/font-metrics-approximate]"),
        "{stderr}"
    );
    assert!(
        stderr.ends_with("cannot write blocked/out.svg: not a directory\n"),
        "{stderr}"
    );
    assert_eq!(fixture.read("blocked")?, b"not a directory");
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_host_output_replaces_the_named_symlink() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    std::fs::create_dir(fixture.0.join("directory"))?;
    std::os::unix::fs::symlink("directory", fixture.0.join("out.md"))?;
    let output = fixture.run(&["render", "input.md", "-o", "out.md"])?;
    success(&output);
    assert_eq!(
        fixture.read("out.md")?,
        b"![diagram](out.assets/out-1.svg)\n"
    );
    assert!(
        !std::fs::symlink_metadata(fixture.0.join("out.md"))?
            .file_type()
            .is_symlink()
    );
    assert!(fixture.0.join("directory").is_dir());
    Ok(())
}

#[test]
fn markdown_artefact_directory_does_not_probe_the_unused_output_parent() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.two_blocks()?;
    fixture.write("report", b"unrelated file")?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "report/diagram.svg", "-a", "assets",
    ])?;
    success(&output);
    assert_eq!(fixture.read("report")?, b"unrelated file");
    assert!(fixture.read("assets/diagram-1.svg")?.starts_with(b"<svg"));
    assert!(fixture.read("assets/diagram-2.svg")?.starts_with(b"<svg"));

    for path in ["missing/", "missing/.", "missing/.."] {
        let output = fixture.run(&[
            "render", "input.md", "-o", path, "-a", "assets", "-e", "svg",
        ])?;
        assert_eq!(output.status.code(), Some(2));
        assert_eq!(
            output.stderr,
            format!("cannot write {path}: is a directory\n").as_bytes()
        );
    }
    Ok(())
}

#[test]
fn leading_dot_output_names_infer_their_format() -> TestResult {
    for (name, prefix) in [
        (".svg", &b"<svg"[..]),
        (".png", &b"\x89PNG\r\n\x1a\n"[..]),
        (".txt", &b""[..]),
    ] {
        let fixture = Fixture::new()?;
        fixture.write("single.mmd", FIRST)?;
        fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
        let single = fixture.run(&["render", "single.mmd", "-o", name, "--color", "never"])?;
        success(&single);
        let expected = fixture.read(name)?;
        assert!(!expected.is_empty());
        assert!(expected.starts_with(prefix));

        let host = fixture.run(&["render", "input.md", "-o", name, "--color", "never"])?;
        success(&host);
        assert_eq!(fixture.read(&format!("{name}-1"))?, expected);
    }
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_asset_directory_resolves_symlinks_before_parent_components() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    std::fs::create_dir_all(fixture.0.join("physical/nested"))?;
    std::os::unix::fs::symlink("physical/nested", fixture.0.join("alias"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "docs/out.md", "-a", "alias/../images",
    ])?;
    success(&output);
    assert!(fixture.read("physical/images/out-1.svg")?.starts_with(b"<svg"));
    assert!(!fixture.0.join("images").exists());
    assert_eq!(
        fixture.read("docs/out.md")?,
        b"![diagram](../physical/images/out-1.svg)\n"
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_host_directory_resolves_symlinks_before_parent_components() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    std::fs::create_dir_all(fixture.0.join("physical/nested"))?;
    std::os::unix::fs::symlink("physical/nested", fixture.0.join("alias"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "alias/../reports/out.md", "-a", "assets",
    ])?;
    success(&output);
    assert_eq!(
        fixture.read("physical/reports/out.md")?,
        b"![diagram](../../assets/out-1.svg)\n"
    );
    assert!(fixture.read("assets/out-1.svg")?.starts_with(b"<svg"));
    assert!(!fixture.0.join("reports").exists());
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_links_use_the_physical_host_directory_without_parent_components() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    std::fs::create_dir_all(fixture.0.join("physical/nested"))?;
    std::os::unix::fs::symlink("physical/nested", fixture.0.join("alias"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "alias/out.md", "-a", "assets",
    ])?;
    success(&output);
    assert_eq!(
        fixture.read("physical/nested/out.md")?,
        b"![diagram](../../assets/out-1.svg)\n"
    );
    Ok(())
}

#[test]
fn markdown_links_allow_prospective_parent_components() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "reports/missing/../out.md", "-a",
        "assets/missing/../images",
    ])?;
    success(&output);
    assert_eq!(
        fixture.read("reports/out.md")?,
        b"![diagram](../assets/images/out-1.svg)\n"
    );
    assert!(fixture.read("assets/images/out-1.svg")?.starts_with(b"<svg"));
    Ok(())
}

#[test]
fn markdown_links_reject_file_parent_traversal_before_writing() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    fixture.write("blocked", b"unrelated file")?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "out.md", "-a", "blocked/../images",
    ])?;
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(output.stderr, b"cannot write out.md: not a directory\n");
    assert!(!fixture.0.join("out.md").exists());
    assert!(!fixture.0.join("images").exists());
    assert_eq!(fixture.read("blocked")?, b"unrelated file");
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_links_reject_dangling_directory_links_before_writing() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    std::os::unix::fs::symlink("missing", fixture.0.join("dangling"))?;
    let output = fixture.run(&[
        "render", "input.md", "-o", "out.md", "-a", "dangling/../images",
    ])?;
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(output.stderr, b"cannot write out.md: no such file or directory\n");
    assert!(!fixture.0.join("out.md").exists());
    assert!(!fixture.0.join("images").exists());
    Ok(())
}

#[cfg(unix)]
#[test]
fn markdown_asset_output_replaces_the_named_symlink() -> TestResult {
    let fixture = Fixture::new()?;
    fixture.write("input.md", format!("```mermaid\n{FIRST}```\n"))?;
    fixture.write("sentinel", b"unrelated file")?;
    std::fs::create_dir(fixture.0.join("out.assets"))?;
    std::os::unix::fs::symlink("../sentinel", fixture.0.join("out.assets/out-1.svg"))?;
    let output = fixture.run(&["render", "input.md", "-o", "out.md"])?;
    success(&output);
    assert_eq!(fixture.read("sentinel")?, b"unrelated file");
    assert_eq!(fixture.read("out.md")?, b"![diagram](out.assets/out-1.svg)\n");
    assert!(fixture.read("out.assets/out-1.svg")?.starts_with(b"<svg"));
    assert!(
        !std::fs::symlink_metadata(fixture.0.join("out.assets/out-1.svg"))?
            .file_type()
            .is_symlink()
    );
    Ok(())
}
