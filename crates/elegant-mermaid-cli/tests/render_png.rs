mod common;

use std::ffi::OsString;
use std::process::{Command, Output, Stdio};

type TestResult = Result<(), Box<dyn std::error::Error>>;

const SOURCE: &str = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n";
const PNG_SIGNATURE: [u8; 8] = [0x89, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a];
const TERMINAL_MESSAGE: &str =
    "cannot write PNG to a terminal; use -o FILE.png or redirect stdout to a file";

fn binary() -> OsString {
    let path = std::env::var_os("EMD_BIN").unwrap_or_default();
    assert!(!path.is_empty(), "EMD_BIN is not set; run just rust-check");
    path
}

fn invoke(args: &[&str], source: &str) -> Result<Output, Box<dyn std::error::Error>> {
    let mut cmd = Command::new(binary());
    cmd.args(args)
        .env_remove("NO_COLOR")
        .env_remove("FORCE_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    Ok(common::run_with_stdin(cmd, source.as_bytes())?)
}

fn scratch(name: &str) -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
    let dir = std::env::temp_dir().join(format!("emd-png-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn path_text(path: &std::path::Path) -> Result<&str, Box<dyn std::error::Error>> {
    Ok(path.to_str().ok_or("non UTF-8 path")?)
}

fn number_after(text: &str, key: &str) -> Result<i64, Box<dyn std::error::Error>> {
    let (_, rest) = text.split_once(key).ok_or("missing key")?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    Ok(digits.parse()?)
}

fn canvas() -> Result<(i64, i64), Box<dyn std::error::Error>> {
    let dump = String::from_utf8(invoke(&["layout"], SOURCE)?.stdout)?;
    Ok((
        number_after(&dump, "\"canvas\":{\"w\":")?,
        number_after(&dump, "\"h\":")?,
    ))
}

fn png_size(bytes: &[u8]) -> Result<(i64, i64), Box<dyn std::error::Error>> {
    assert_eq!(bytes.get(..8), Some(&PNG_SIGNATURE[..]));
    assert_eq!(bytes.get(12..16), Some(&b"IHDR"[..]));
    let field = |at: usize| -> Result<i64, Box<dyn std::error::Error>> {
        let raw: [u8; 4] = bytes.get(at..at + 4).ok_or("short IHDR")?.try_into()?;
        Ok(i64::from(u32::from_be_bytes(raw)))
    };
    Ok((field(16)?, field(20)?))
}

fn expected_size(scale: i64) -> Result<(i64, i64), Box<dyn std::error::Error>> {
    let (w, h) = canvas()?;
    Ok(((w * scale + 63) / 64, (h * scale + 63) / 64))
}

#[test]
fn png_file_has_the_scaled_canvas_size() -> TestResult {
    let dir = scratch("size")?;
    for scale in [1, 2, 3, 8] {
        let file = dir.join(format!("s{scale}.png"));
        let text = scale.to_string();
        let output = invoke(
            &["render", "-e", "png", "-s", &text, "-o", path_text(&file)?],
            SOURCE,
        )?;
        assert_eq!(output.status.code(), Some(0), "scale {scale}");
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
        assert_eq!(
            png_size(&std::fs::read(&file)?)?,
            expected_size(scale)?,
            "scale {scale}"
        );
    }
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn png_extension_infers_the_format_and_scale_defaults_to_two() -> TestResult {
    let dir = scratch("infer")?;
    let file = dir.join("demo.png");
    let output = invoke(&["render", "-o", path_text(&file)?], SOURCE)?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(png_size(&std::fs::read(&file)?)?, expected_size(2)?);
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn png_on_a_pipe_equals_the_file_bytes() -> TestResult {
    let dir = scratch("pipe")?;
    let file = dir.join("demo.png");
    invoke(
        &["render", "-e", "png", "-s", "1", "-o", path_text(&file)?],
        SOURCE,
    )?;
    let piped = invoke(&["render", "-e", "png", "-s", "1"], SOURCE)?;
    assert_eq!(piped.status.code(), Some(0));
    assert!(piped.stderr.is_empty());
    assert_eq!(piped.stdout.get(..8), Some(&PNG_SIGNATURE[..]));
    assert_eq!(piped.stdout, std::fs::read(&file)?);
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn png_background_and_theme_change_the_pixels() -> TestResult {
    let base = invoke(&["render", "-e", "png", "-s", "1"], SOURCE)?.stdout;
    for extra in [
        vec!["-b", "#ff0000"],
        vec!["-b", "#f00"],
        vec!["-t", "elegant-dark"],
    ] {
        let mut args = vec!["render", "-e", "png", "-s", "1"];
        args.extend(extra.iter());
        let output = invoke(&args, SOURCE)?;
        assert_eq!(output.status.code(), Some(0), "{extra:?}");
        assert_eq!(png_size(&output.stdout)?, png_size(&base)?);
        assert_ne!(output.stdout, base, "{extra:?}");
    }
    Ok(())
}

#[test]
fn png_scale_must_be_one_to_eight() -> TestResult {
    for scale in ["0", "9", "x", "2.5"] {
        let output = invoke(&["render", "-e", "png", "-s", scale], SOURCE)?;
        assert_eq!(output.status.code(), Some(2), "{scale}");
        assert!(output.stdout.is_empty());
        assert_eq!(
            String::from_utf8(output.stderr)?,
            format!("invalid value {scale} for -s; expected one of: 1..8\n")
        );
    }
    Ok(())
}

#[test]
fn png_is_refused_on_a_terminal_unless_written_to_a_file() -> TestResult {
    let dir = scratch("terminal")?;
    let input = dir.join("demo.mmd");
    std::fs::write(&input, SOURCE)?;
    let output = Command::new("script")
        .args([
            "-qec",
            "\"$EMD_BIN\" render -e png \"$EMD_INPUT\"",
            "/dev/null",
        ])
        .env("EMD_BIN", binary())
        .env("EMD_INPUT", &input)
        .stdin(Stdio::null())
        .output()?;
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(output.stdout, format!("{TERMINAL_MESSAGE}\r\n").as_bytes());
    let file = dir.join("demo.png");
    let output = Command::new("script")
        .args([
            "-qec",
            "\"$EMD_BIN\" render \"$EMD_INPUT\" -o \"$EMD_OUTPUT\"",
            "/dev/null",
        ])
        .env("EMD_BIN", binary())
        .env("EMD_INPUT", &input)
        .env("EMD_OUTPUT", &file)
        .stdin(Stdio::null())
        .output()?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(png_size(&std::fs::read(&file)?)?, expected_size(2)?);
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn svg_text_paths_draw_outlines_instead_of_text() -> TestResult {
    let font = String::from_utf8(invoke(&["render", "-e", "svg"], SOURCE)?.stdout)?;
    assert!(font.contains("<text"), "{font}");
    assert!(!font.contains("<path class='emd-s-text'"), "{font}");
    for args in [
        vec!["render", "-e", "svg", "--svg-text", "paths"],
        vec!["render", "-e", "svg", "--svg-text=paths"],
    ] {
        let output = invoke(&args, SOURCE)?;
        assert_eq!(output.status.code(), Some(0), "{args:?}");
        assert!(output.stderr.is_empty());
        let paths = String::from_utf8(output.stdout)?;
        assert!(paths.contains("<path class='emd-s-text' d='M"), "{paths}");
        assert!(!paths.contains("<text"), "{paths}");
        assert!(!paths.contains("<tspan"), "{paths}");
        assert_eq!(
            paths.matches("<path class='emd-s-text'").count(),
            font.matches("<text").count()
        );
    }
    Ok(())
}

#[test]
fn svg_text_paths_do_not_change_text_output() -> TestResult {
    let plain = invoke(&["render", "-e", "text", "--color", "never"], SOURCE)?;
    let paths = invoke(
        &[
            "render",
            "-e",
            "text",
            "--color",
            "never",
            "--svg-text",
            "paths",
        ],
        SOURCE,
    )?;
    assert_eq!(paths.status.code(), Some(0));
    assert_eq!(paths.stdout, plain.stdout);
    Ok(())
}
