use std::io::Write;
use std::process::{Command, Stdio};

fn binary() -> std::ffi::OsString {
    let path = std::env::var_os("EMD_BIN").unwrap_or_default();
    assert!(!path.is_empty(), "EMD_BIN is not set; run just rust-check");
    path
}

type TestResult = Result<(), Box<dyn std::error::Error>>;
fn invoke(args: &[&str], source: &str) -> Result<std::process::Output, Box<dyn std::error::Error>> {
    invoke_bytes(args, source.as_bytes())
}
fn invoke_bytes(
    args: &[&str],
    source: &[u8],
) -> Result<std::process::Output, Box<dyn std::error::Error>> {
    let mut child = Command::new(binary())
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
        .write_all(source)?;
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
    let implicit = Command::new(binary())
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
fn binary_terminal_cli_07() -> TestResult {
    let output = Command::new("script")
        .args(["-qec", "\"$EMD_BIN\" render", "/dev/null"])
        .env("EMD_BIN", binary())
        .stdin(Stdio::null())
        .output()?;
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(
        output.stdout,
        b"missing INPUT; pass a path or pipe Mermaid source\r\n"
    );
    assert_eq!(output.stderr, b"");
    Ok(())
}

#[test]
fn binary_pipe_cli_07() -> TestResult {
    let output = invoke(
        &["render", "-e", "text", "--color", "never"],
        "flowchart LR\n A\n",
    )?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, "┌───┐\n│ A │\n└───┘\n".as_bytes());
    assert_eq!(output.stderr, b"");
    Ok(())
}

#[test]
fn binary_width_cli_25() -> TestResult {
    let output = invoke(
        &["render", "-e", "text", "--color", "never", "--width", "1"],
        "flowchart LR\n A\n",
    )?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, "┌───┐\n│ A │\n└───┘\n".as_bytes());
    assert_eq!(output.stderr, b"");
    Ok(())
}

#[test]
fn binary_colour_cli_36() -> TestResult {
    let plain = "┌───┐\n│ A │\n└───┘\n";
    let coloured =
        "\x1b[90m┌───┐\x1b[39m\n\x1b[90m│ \x1b[39mA \x1b[90m│\x1b[39m\n\x1b[90m└───┘\x1b[39m\n";
    for (name, flag, env, want) in [
        ("always", "always", vec![("NO_COLOR", "1")], coloured),
        ("never", "never", vec![("FORCE_COLOR", "1")], plain),
        (
            "no_color",
            "auto",
            vec![("NO_COLOR", "1"), ("FORCE_COLOR", "1")],
            plain,
        ),
        (
            "clicolor_force",
            "auto",
            vec![("CLICOLOR_FORCE", "1"), ("CLICOLOR", "0")],
            coloured,
        ),
        (
            "force_color",
            "auto",
            vec![("FORCE_COLOR", "1"), ("TERM", "dumb")],
            coloured,
        ),
        ("clicolor", "auto", vec![("CLICOLOR", "0")], plain),
        ("dumb", "auto", vec![("TERM", "dumb")], plain),
        ("pipe", "auto", vec![], plain),
    ] {
        let mut child = Command::new(binary())
            .args(["render", "-e", "text", "--color", flag])
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("TERM", "xterm")
            .envs(env)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        child
            .stdin
            .take()
            .ok_or("missing stdin")?
            .write_all(b"flowchart LR\n A\n")?;
        let output = child.wait_with_output()?;
        assert_eq!(output.status.code(), Some(0), "{name}");
        assert_eq!(output.stdout, want.as_bytes(), "{name}");
        assert_eq!(output.stderr, b"", "{name}");
    }
    Ok(())
}

#[test]
fn binary_argument_order_cli_05() -> TestResult {
    let dir = std::env::temp_dir().join(format!("emd-binary-order-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    std::fs::write(dir.join("-name"), "flowchart LR\n A\n")?;
    for args in [
        vec!["render", "-e", "text", "--", "-name"],
        vec!["render", "-e", "text", "./-name"],
        vec!["render", "./-name", "-e", "text"],
    ] {
        let output = Command::new(binary())
            .args(args)
            .current_dir(&dir)
            .env("NO_COLOR", "1")
            .output()?;
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, "┌───┐\n│ A │\n└───┘\n".as_bytes());
        assert_eq!(output.stderr, b"");
    }
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn binary_inference_cli_23_cli_24() -> TestResult {
    let dir = std::env::temp_dir().join(format!("emd-binary-infer-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    for ext in ["txt", "svg", "unknown", ""] {
        let name = if ext.is_empty() {
            "output".to_owned()
        } else {
            format!("output.{ext}")
        };
        let path = dir.join(name);
        let name = path.to_str().ok_or("non UTF-8 path")?;
        let output = invoke(&["render", "-o", name], "flowchart LR\n A\n")?;
        if ext == "unknown" || ext.is_empty() {
            assert_eq!(output.status.code(), Some(2));
            assert_eq!(output.stdout, b"");
            assert_eq!(
                output.stderr,
                format!("cannot infer the output format from {name}; pass -e\n").as_bytes()
            );
        } else {
            assert_eq!(output.status.code(), Some(0));
            assert_eq!(output.stdout, b"");
            assert_eq!(output.stderr, b"");
            let bytes = std::fs::read(path)?;
            if ext == "txt" {
                assert_eq!(bytes, "┌───┐\n│ A │\n└───┘\n".as_bytes());
            } else {
                assert!(String::from_utf8(bytes)?.contains("<svg"));
            }
        }
    }
    std::fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn binary_colour_terminal_cli_36() -> TestResult {
    let path = std::env::temp_dir().join(format!("emd-terminal-{}.mmd", std::process::id()));
    std::fs::write(&path, "flowchart LR\n A\n")?;
    let output = Command::new("script")
        .args([
            "-qec",
            "\"$EMD_BIN\" render -e text --color auto \"$SOURCE\"",
            "/dev/null",
        ])
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("TERM", "xterm")
        .env("EMD_BIN", binary())
        .env("SOURCE", &path)
        .stdin(Stdio::null())
        .output()?;
    std::fs::remove_file(path)?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout,"\x1b[90m┌───┐\x1b[39m\r\n\x1b[90m│ \x1b[39mA \x1b[90m│\x1b[39m\r\n\x1b[90m└───┘\x1b[39m\r\n".as_bytes());
    assert_eq!(output.stderr, b"");
    Ok(())
}

#[test]
fn binary_explicit_format_cli_23() -> TestResult {
    let path = std::env::temp_dir().join(format!("emd-explicit-{}.txt", std::process::id()));
    let output = invoke(
        &[
            "render",
            "-e",
            "svg",
            "-o",
            path.to_str().ok_or("non UTF-8")?,
        ],
        "flowchart LR\n A\n",
    )?;
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
    assert!(std::fs::read_to_string(&path)?.contains("<svg"));
    std::fs::remove_file(path)?;
    Ok(())
}

#[test]
fn invalid_utf8_rejected_by_source_commands() -> TestResult {
    for malformed in [&b"\xff"[..], &b"\xe2\x82"[..], &b"\xed\xa0\x80"[..]] {
        let mut source = b"flowchart LR\n  %% ".to_vec();
        let start = source.len();
        source.extend_from_slice(malformed);
        source.extend_from_slice(b"\n  A --> B\n");
        let output = invoke_bytes(&["check", "-", "--output-format", "json"], &source)?;
        assert_eq!(output.status.code(), Some(1));
        let json = String::from_utf8(output.stdout)?;
        assert!(json.contains("\"code\":\"source/invalid-utf8\""));
        assert!(json.contains("\"severity\":\"error\""));
        assert!(json.contains(&format!("\"message\":\"invalid UTF-8 at byte {start}\"")));
        assert!(json.contains(&format!(
            "\"span\":{{\"start\":{start},\"end\":{}}}",
            start + 3
        )));
        assert!(json.contains("\"help\":\"Save the source as UTF-8.\""));
        for args in [
            vec!["render", "-e", "svg"],
            vec!["render", "-e", "text"],
            vec!["layout", "--stage", "model"],
            vec!["layout", "--stage", "layout"],
        ] {
            let output = invoke_bytes(&args, &source)?;
            assert_eq!(output.status.code(), Some(1), "{args:?}");
            assert!(output.stdout.is_empty(), "{args:?}");
            let stderr = String::from_utf8(output.stderr)?;
            assert!(stderr.contains("error[source/invalid-utf8]"), "{stderr}");
            assert!(stderr.contains(&format!("invalid UTF-8 at byte {start}")));
            assert!(stderr.contains("Save the source as UTF-8."));
        }
    }
    Ok(())
}

#[test]
fn valid_non_ascii_source_commands() -> TestResult {
    for args in [
        vec!["check", "-", "--output-format", "json"],
        vec!["render", "-e", "svg"],
        vec!["layout", "--stage", "model"],
        vec!["layout", "--stage", "layout"],
    ] {
        let output = invoke(&args, "flowchart LR\n  %% café 日本語 😀\n  A --> B\n")?;
        assert_eq!(output.status.code(), Some(0), "{args:?}");
        assert!(!String::from_utf8(output.stdout)?.contains("source/invalid-utf8"));
        assert!(!String::from_utf8(output.stderr)?.contains("source/invalid-utf8"));
    }
    Ok(())
}

#[test]
fn svg_accessibility_metadata() -> TestResult {
    for (metadata, title, description) in [
        ("", "Mermaid flowchart diagram", None),
        (
            "accTitle: Café & <route>\n",
            "Café &amp; &lt;route&gt;",
            None,
        ),
        (
            "accTitle: Route\naccDescr: A & <B>\n",
            "Route",
            Some("A &amp; &lt;B&gt;"),
        ),
        (
            "accDescr {\nFirst & <second>\nThird line\n}\n",
            "Mermaid flowchart diagram",
            Some("First &amp; &lt;second&gt;\nThird line"),
        ),
    ] {
        let source = format!("flowchart LR\n{metadata}  A --> B\n");
        let output = invoke(&["render", "-e", "svg"], &source)?;
        assert_eq!(output.status.code(), Some(0));
        let svg = String::from_utf8(output.stdout)?;
        assert!(svg.contains("aria-labelledby='title'"));
        assert!(svg.contains(&format!("<title id='title'>{title}</title>")));
        if let Some(description) = description {
            assert!(svg.contains("aria-describedby='desc'"));
            assert!(svg.contains(&format!("<desc id='desc'>{description}</desc>")));
        } else {
            assert!(!svg.contains("aria-describedby="));
            assert!(!svg.contains("<desc"));
        }
    }
    Ok(())
}
