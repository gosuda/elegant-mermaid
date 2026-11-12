use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn layout_model_cli_streams() -> Result<(), Box<dyn std::error::Error>> {
    for (source, profile, code) in [
        ("flowchart\nA --> B\n", "vector", 0),
        ("flowchart\nA --> B\n", "cell", 0),
        ("flowchart\nA[broken\n", "cell", 1),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
            .args(["layout", "--stage", "model", "--profile", profile, "-"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        child
            .stdin
            .take()
            .ok_or("missing stdin")?
            .write_all(source.as_bytes())?;
        let output = child.wait_with_output()?;
        assert_eq!(output.status.code(), Some(code));
        if code == 0 {
            assert!(output.stderr.is_empty());
            assert!(
                String::from_utf8(output.stdout)?.contains(&format!("\"profile\":\"{profile}\""))
            );
        } else {
            assert!(output.stdout.is_empty());
            assert!(String::from_utf8(output.stderr)?.contains("error["));
        }
    }
    Ok(())
}

#[test]
fn layout_model_cli_usage() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(["layout", "--stage", "bad", "-"])
        .output()?;
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(
        String::from_utf8(output.stderr)?,
        "invalid value bad for --stage; expected one of: model\n"
    );
    Ok(())
}
