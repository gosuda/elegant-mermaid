mod common;

use std::path::PathBuf;
use std::process::{Command, Stdio};

type TestResult = Result<(), Box<dyn std::error::Error>>;

const DIAGRAM: &str = "flowchart LR\n  A[Start] --> B[End]\n";
const ICON_DIAGRAM: &str = "flowchart LR\n  A@{ icon: 't:box', label: 'Boxed' } --> B[End]\n";
const PACK: &str = r#"{"prefix":"t","width":24,"height":24,"icons":{"box":{"body":"<path d=\"M0 0h24v24H0z\"/>"}}}"#;

struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Result<Scratch, std::io::Error> {
        let path = std::env::temp_dir().join(format!("emd-features-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&path)?;
        Ok(Scratch(path))
    }

    fn file(&self, name: &str, text: &str) -> Result<String, std::io::Error> {
        let path = self.0.join(name);
        std::fs::write(&path, text)?;
        Ok(path.to_string_lossy().into_owned())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn run(args: &[&str], source: &str) -> Result<(i32, String, String), Box<dyn std::error::Error>> {
    let binary = std::env::var_os("EMD_BIN").unwrap_or_default();
    assert!(
        !binary.is_empty(),
        "EMD_BIN is not set; run just rust-check"
    );
    let mut cmd = Command::new(binary);
    cmd.args(args)
        .env_remove("NO_COLOR")
        .env_remove("FORCE_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let output = common::run_with_stdin(cmd, source.as_bytes())?;
    Ok((
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout)?,
        String::from_utf8(output.stderr)?,
    ))
}

#[test]
fn render_config_file_selects_the_hand_drawn_look() -> TestResult {
    let scratch = Scratch::new("config")?;
    let config = scratch.file("look.yaml", "look: handDrawn\nhandDrawnSeed: 7\n")?;
    let (code, first, stderr) = run(&["render", "-c", &config, "-e", "svg"], DIAGRAM)?;
    assert_eq!((code, stderr.as_str()), (0, ""));
    assert!(first.contains("<path class='emd-h-edge'"), "{first}");
    let (_, second, _) = run(&["render", "-e", "svg", "-c", &config], DIAGRAM)?;
    assert_eq!(first, second);
    let (_, plain, _) = run(&["render", "-e", "svg"], DIAGRAM)?;
    assert!(!plain.contains("emd-h-"), "{plain}");
    let neo = scratch.file("neo.yaml", "look: neo\n")?;
    let (_, neo_svg, _) = run(&["render", "-e", "svg", "-c", &neo], DIAGRAM)?;
    assert!(neo_svg.contains("stroke-width='2'"), "{neo_svg}");
    let (_, text, _) = run(&["render", "-e", "text", "-c", &config], DIAGRAM)?;
    let (_, plain_text, _) = run(&["render", "-e", "text"], DIAGRAM)?;
    assert_eq!(text, plain_text);
    Ok(())
}

#[test]
fn render_config_file_failures_exit_two() -> TestResult {
    let scratch = Scratch::new("config-failures")?;
    let missing = scratch.0.join("absent.yaml").to_string_lossy().into_owned();
    let (code, stdout, stderr) = run(&["render", "-c", &missing], DIAGRAM)?;
    assert_eq!((code, stdout.as_str()), (2, ""));
    assert_eq!(
        stderr,
        format!("cannot read {missing}: no such file or directory\n")
    );
    for (name, text, message) in [
        ("broken.yaml", "theme: [\n", "malformed config value"),
        ("scalar.yaml", "plain\n", "config must be a mapping"),
        (
            "seed.yaml",
            "handDrawnSeed: -3\n",
            "invalid config value -3 for handDrawnSeed",
        ),
        (
            "edges.yaml",
            "maxEdges: -1\n",
            "invalid config value -1 for maxEdges",
        ),
        (
            "text-size.yaml",
            "maxTextSize: 2147483648\n",
            "invalid config value 2147483648 for maxTextSize",
        ),
        (
            "font.yaml",
            "fontFamily: false\n",
            "invalid config value false for fontFamily",
        ),
    ] {
        let path = scratch.file(name, text)?;
        let (code, stdout, stderr) = run(&["render", "-c", &path], DIAGRAM)?;
        assert_eq!((code, stdout.as_str()), (2, ""), "{name}");
        assert_eq!(
            stderr,
            format!("{path}: invalid config: {message}\n"),
            "{name}"
        );
    }
    Ok(())
}

#[test]
fn render_config_file_overrides_source_limits_before_rejection() -> TestResult {
    let scratch = Scratch::new("config-limits")?;
    let source = "---\nconfig:\n  maxEdges: 0\n---\nflowchart LR\nA --> B\n";
    let raised = scratch.file("raised.yaml", "maxEdges: 1\n")?;
    for format in ["svg", "text"] {
        let (code, stdout, stderr) = run(&["render", "-e", format], source)?;
        assert_eq!((code, stdout.as_str()), (1, ""));
        assert!(
            stderr.contains("error[limit/max-edges]: diagram has 1 edges; the limit is 0"),
            "{stderr}"
        );
        let (code, stdout, stderr) = run(&["render", "-e", format, "-c", &raised], source)?;
        assert_eq!((code, stderr.as_str()), (0, ""));
        assert!(!stdout.is_empty());
    }

    let lower = scratch.file("lower.yaml", "maxTextSize: 1\n")?;
    let (code, stdout, stderr) = run(&["render", "-e", "svg", "-c", &lower], DIAGRAM)?;
    assert_eq!((code, stdout.as_str()), (1, ""));
    assert!(stderr.contains("error[limit/max-text-size]"), "{stderr}");
    assert!(stderr.contains("the limit is 1 bytes"), "{stderr}");
    Ok(())
}

#[test]
fn render_config_font_family_reports_the_effective_value_once() -> TestResult {
    let scratch = Scratch::new("config-font")?;
    let source = "---\nconfig:\n  fontFamily: Source\n---\nflowchart LR\nA[Alphabet]\n";
    let configured = scratch.file("font.yaml", "fontFamily: 'Custom & <Font>'\n")?;
    let (code, svg, stderr) = run(&["render", "-e", "svg", "-c", &configured], source)?;
    assert_eq!(code, 0, "{stderr}");
    assert!(
        svg.contains("font-family='Custom &amp; &lt;Font&gt;'"),
        "{svg}"
    );
    assert_eq!(
        stderr
            .matches("info[config/font-metrics-approximate]")
            .count(),
        1,
        "{stderr}"
    );
    assert!(stderr.contains("fontFamily is Custom & <Font>"), "{stderr}");
    assert!(!stderr.contains("fontFamily is Source"), "{stderr}");

    let clear = scratch.file("clear.yaml", "fontFamily: ''\n")?;
    let (code, svg, stderr) = run(&["render", "-e", "svg", "-c", &clear], source)?;
    assert_eq!((code, stderr.as_str()), (0, ""));
    assert!(!svg.contains("font-family='Source'"));
    Ok(())
}

#[test]
fn render_icon_pack_flag_draws_pack_icons() -> TestResult {
    let scratch = Scratch::new("pack")?;
    let pack = scratch.file("pack.json", PACK)?;
    let (code, svg, stderr) = run(&["render", "--icon-pack", &pack, "-e", "svg"], ICON_DIAGRAM)?;
    assert_eq!((code, stderr.as_str()), (0, ""));
    assert!(svg.contains("<path class='emd-s-ink' d='M "), "{svg}");
    assert!(!svg.contains(" C "), "{svg}");
    let (code, svg, stderr) = run(&["render", "-e", "svg"], ICON_DIAGRAM)?;
    assert_eq!(code, 0);
    assert_eq!(svg.matches("<path class='emd-s-ink'").count(), 1, "{svg}");
    assert!(svg.contains(" C "), "{svg}");
    assert!(
        stderr.contains("info[icon/pack-missing]: icon t:box is not available"),
        "{stderr}"
    );
    let second = scratch.file("second.json", r#"{"prefix":"u","icons":{}}"#)?;
    let (code, _, stderr) = run(
        &[
            "render",
            "--icon-pack",
            &second,
            "--icon-pack",
            &pack,
            "-e",
            "text",
        ],
        ICON_DIAGRAM,
    )?;
    assert_eq!((code, stderr.as_str()), (0, ""));
    Ok(())
}

#[test]
fn render_icon_pack_flag_failures_exit_two() -> TestResult {
    let scratch = Scratch::new("pack-failures")?;
    let missing = scratch.0.join("absent.json").to_string_lossy().into_owned();
    let (code, stdout, stderr) = run(&["render", "--icon-pack", &missing], ICON_DIAGRAM)?;
    assert_eq!((code, stdout.as_str()), (2, ""));
    assert!(
        stderr.starts_with(&format!("cannot read {missing}: ")),
        "{stderr}"
    );
    for (name, text, reason) in [
        (
            "a.json",
            "{",
            "invalid JSON at byte 1: expected a member name",
        ),
        ("b.json", "[]", "the root must be an object"),
        ("c.json", r#"{"prefix":"p"}"#, "missing icons object"),
    ] {
        let path = scratch.file(name, text)?;
        let (code, stdout, stderr) = run(&["render", "--icon-pack", &path], ICON_DIAGRAM)?;
        assert_eq!((code, stdout.as_str()), (2, ""), "{name}");
        assert_eq!(
            stderr,
            format!("{path}: malformed icon pack: {reason}\n"),
            "{name}"
        );
    }
    Ok(())
}
