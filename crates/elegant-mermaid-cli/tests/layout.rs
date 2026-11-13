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
            assert!(
                output.stderr.is_empty(),
                "layout_model_cli_streams: required output.stderr.is_empty(); observed: {:?}",
                output.stderr
            );
            let observed = String::from_utf8(output.stdout)?;
            assert!(
                observed.contains(&format!("\"profile\":\"{profile}\"")),
                "layout_model_cli_streams: required String::from_utf8(output.stdout)?.contains(&format!(\"\\\"profile\\\":\\\"{{profile}}\\\"\")); observed: {:?}",
                observed
            );
        } else {
            assert!(
                output.stdout.is_empty(),
                "layout_model_cli_streams: required output.stdout.is_empty(); observed: {:?}",
                output.stdout
            );
            let observed = String::from_utf8(output.stderr)?;
            assert!(
                observed.contains("error["),
                "layout_model_cli_streams: required String::from_utf8(output.stderr)?.contains(\"error[\"); observed: {:?}",
                observed
            );
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
        "invalid value bad for --stage; expected one of: model, layout\n"
    );
    Ok(())
}

#[test]
fn layout_public_demo() -> Result<(), Box<dyn std::error::Error>> {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    for (profile, metric) in [
        ("vector", elegant_mermaid::scene::Profile::Vector),
        ("cell", elegant_mermaid::scene::Profile::Cell),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
            .args(["layout", "-", "--profile", profile])
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
        assert_eq!(output.status.code(), Some(0));
        assert!(
            output.stderr.is_empty(),
            "layout_public_demo: required output.stderr.is_empty(); observed: {:?}",
            output.stderr
        );
        let text = String::from_utf8(output.stdout)?;
        assert!(
            text.contains("\"stage\":\"layout\""),
            "layout_public_demo: required text.contains(\"\\\"stage\\\":\\\"layout\\\"\"); observed: {:?}",
            text
        );
        let parsed = elegant_mermaid::syntax::flowchart::parse(source, &[]);
        let (model, _) = elegant_mermaid::model::flowchart::resolve(source, &parsed.document);
        let input = elegant_mermaid::layout::flowchart::from_flowchart(
            &model,
            metric,
            elegant_mermaid::scene::DumpOptions::default(),
        );
        let scene = elegant_mermaid::layout::families::layout(&input)?.0;
        assert!(
            scene.check()?,
            "public demo must satisfy scene constraints: profile={profile}, source={source:?}, dump={}",
            scene.dump()
        );
        assert_eq!(text, scene.dump());
        assert_eq!(
            scene
                .labels()
                .iter()
                .map(|label| (label.id.as_str(), label.owner.as_str(), label.text.as_str()))
                .collect::<Vec<_>>(),
            [("e1.label", "e1", "yes"), ("e2.label", "e2", "no")]
        );
        for (owner, caption) in [("A", "Start"), ("B", "Choice"), ("C", "Done")] {
            let group = scene
                .items()
                .iter()
                .find(|group| group.owner == owner)
                .ok_or("missing node scene group")?;
            let captions = group
                .items
                .iter()
                .filter_map(|item| match item {
                    elegant_mermaid::scene::Item::Text(text) => Some(
                        text.lines
                            .iter()
                            .map(|line| caption_line(line))
                            .collect::<Vec<_>>()
                            .join("\n"),
                    ),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(captions, [caption], "{profile} node {owner}");
        }
    }
    Ok(())
}

fn caption_line(line: &[elegant_mermaid::scene::Run]) -> String {
    line.iter().map(|run| run.text.as_str()).collect()
}

#[test]
fn metrics_rejects_cell_profile() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(["layout", "--metrics", "--profile", "cell"])
        .output()?;
    assert_eq!(output.status.code(), Some(2));
    assert!(
        output.stdout.is_empty(),
        "metrics_rejects_cell_profile: required output.stdout.is_empty(); observed: {:?}",
        output.stdout
    );
    assert_eq!(output.stderr, b"--metrics needs --profile vector\n");
    Ok(())
}
