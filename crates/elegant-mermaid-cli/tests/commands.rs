use std::io::Write;
use std::process::{Command, Stdio};

type TestResult = Result<(), Box<dyn std::error::Error>>;
fn invoke(args: &[&str], source: &str) -> Result<std::process::Output, Box<dyn std::error::Error>> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(args)
        .env_remove("NO_COLOR")
        .env_remove("FORCE_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .ok_or("missing stdin")?
        .write_all(source.as_bytes())?;
    Ok(child.wait_with_output()?)
}
#[test]
fn command_contract() -> TestResult {
    for (args, code, message) in [
        (
            vec!["render", "-e", "png"],
            2,
            "invalid value png for -e; expected one of: svg, text",
        ),
        (
            vec!["render", "-s", "2"],
            2,
            "unknown flag -s; run emd render --help",
        ),
        (
            vec!["render", "--svg-text", "paths"],
            2,
            "invalid value paths for --svg-text; expected one of: font",
        ),
        (
            vec!["render", "--width", "9999999999999999999999"],
            2,
            "invalid value 9999999999999999999999 for --width; expected one of: non-negative integers",
        ),
        (
            vec!["render", "x", "-i", "y"],
            2,
            "pass input either as INPUT or with -i, not both",
        ),
        (
            vec!["render", "-t", "bad"],
            2,
            "invalid value bad for -t; expected one of: elegant-light, elegant-dark",
        ),
        (
            vec!["render", "-b", "red"],
            2,
            "invalid value red for -b; expected one of: #rgb, #rrggbb",
        ),
        (vec!["bad"], 2, "unknown command bad; run emd --help"),
    ] {
        let output = invoke(&args, "")?;
        assert_eq!(output.status.code(), Some(code));
        assert!(output.stdout.is_empty());
        assert_eq!(String::from_utf8(output.stderr)?, format!("{message}\n"));
    }
    let output = invoke(&["--version"], "")?;
    assert!(output.status.success());
    assert_eq!(output.stdout, b"emd 0.1.0\n");
    assert!(output.stderr.is_empty());
    Ok(())
}
#[test]
fn stdin_diagnostic_path() -> TestResult {
    let output = invoke(&["check", "-"], "flowchart LR\n  A[Start --> B\n")?;
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8(output.stdout)?
            .starts_with("<stdin>:2:4: error[flowchart/unclosed-node-bracket]:")
    );
    assert!(output.stderr.is_empty());
    Ok(())
}
#[test]
fn help_and_version() -> TestResult {
    for args in [
        vec!["-h"],
        vec!["--help"],
        vec!["render", "--help"],
        vec!["check", "--help"],
        vec!["layout", "--help"],
    ] {
        let output = invoke(&args, "")?;
        assert!(output.status.success());
        assert!(output.stderr.is_empty());
        let text = String::from_utf8(output.stdout)?;
        assert!(text.contains("Usage: emd"));
        assert!(!text.contains("kernel-eval"));
        assert!(!text.contains("--stage"));
    }
    let output = invoke(&[], "")?;
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8(output.stderr)?.starts_with("Usage: emd"));
    Ok(())
}
#[test]
fn check_json_exact() -> TestResult {
    let output = invoke(
        &["check", "-", "--output-format", "json"],
        "flowchart LR\n  A[Start --> B\n",
    )?;
    let want = "{\"version\":1,\"files\":[{\"path\":\"<stdin>\",\"kind\":\"flowchart\",\"diagnostics\":[{\"code\":\"flowchart/unclosed-node-bracket\",\"severity\":\"error\",\"message\":\"node bracket [ is never closed\",\"span\":{\"start\":16,\"end\":29},\"line\":2,\"column\":4,\"end_line\":3,\"end_column\":1,\"related\":[],\"help\":\"Add the closing bracket that matches the opening bracket.\",\"fixes\":[{\"title\":\"Add the closing bracket\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":29,\"end\":29},\"new_text\":\"]\"}]}]}]}],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":0,\"info\":0}}\n";
    assert_eq!(output.stdout, want.as_bytes());
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    Ok(())
}

#[test]
fn files_order_outputs_and_empty_scan() -> TestResult {
    let dir = std::env::temp_dir().join(format!("emd-command-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let path = dir.to_str().ok_or("non UTF-8 path")?;
    let empty = invoke(&["check", path], "")?;
    assert_eq!(empty.status.code(), Some(2));
    assert_eq!(
        String::from_utf8(empty.stderr)?,
        format!("no Mermaid files found in {path}\n")
    );
    let implicit = Command::new(env!("CARGO_BIN_EXE_emd"))
        .arg("check")
        .current_dir(&dir)
        .output()?;
    assert!(implicit.status.success());
    assert!(implicit.stdout.is_empty());
    assert_eq!(implicit.stderr, b"no Mermaid files found in .\n");
    let source = "flowchart LR\n A --> B\n";
    for name in ["b.mmd", "a.mermaid"] {
        std::fs::write(dir.join(name), source)?;
    }
    let output = invoke(&["check", path, "--output-format", "json"], "")?;
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout)?;
    assert!(text.find("a.mermaid") < text.find("b.mmd"));
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn render_argument_order_and_output_files() -> TestResult {
    let dir = std::env::temp_dir().join(format!("emd-render-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let file = dir.join("b.mmd");
    std::fs::write(&file, "flowchart LR\n A --> B\n")?;
    let file = file.to_str().ok_or("non UTF-8 path")?;
    let mut previous = Vec::new();
    for args in [
        vec!["render", "-e", "text", file],
        vec!["render", file, "-e", "text"],
        vec!["render", "-e", "text", "--", file],
    ] {
        let output = invoke(&args, "")?;
        assert!(output.status.success(), "{:?}", output.stderr);
        assert!(output.stderr.is_empty());
        if !previous.is_empty() {
            assert_eq!(previous, output.stdout);
        }
        previous = output.stdout;
    }
    for ext in ["svg", "txt"] {
        let destination = dir.join(format!("demo.{ext}"));
        let output = invoke(
            &[
                "render",
                file,
                "-o",
                destination.to_str().ok_or("non UTF-8")?,
            ],
            "",
        )?;
        assert!(output.status.success(), "{:?}", output.stderr);
        assert!(output.stdout.is_empty());
        let bytes = std::fs::read(&destination)?;
        assert!(!bytes.is_empty());
        if ext == "svg" {
            let svg = String::from_utf8(bytes)?;
            assert!(svg.contains("graphics-document document"));
            assert!(!svg.contains("foreignObject"));
        }
    }
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn terminal_stdin_requires_path() -> TestResult {
    let output = Command::new("script")
        .args(["-qec", "\"$EMD_BIN\" render", "/dev/null"])
        .env("EMD_BIN", env!("CARGO_BIN_EXE_emd"))
        .stdin(Stdio::null())
        .output()?;
    assert_eq!(output.status.code(), Some(2));
    let text = String::from_utf8(output.stdout)?;
    assert!(text.contains("missing INPUT; pass a path or pipe Mermaid source"));
    Ok(())
}
