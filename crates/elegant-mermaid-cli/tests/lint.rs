mod common;

use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

const BIN: &str = env!("CARGO_BIN_EXE_emd");
const ARROW: &str = "flowchart LR\n  A -> B\n";
const ARROW_FIXED: &str = "flowchart LR\n  A --> B\n";
const END: &str = "flowchart TD\n  A --> B\n  end\n";
const END_FIXED: &str = "flowchart TD\n  A --> B\n";
const DUPLICATE: &str = "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n";
const BETA: &str = "block-beta\n  columns 1\n";
const CLEAN: &str = "flowchart LR\n  A --> B\n";

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Outcome {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

fn invoke<S: AsRef<OsStr>>(dir: &Path, stdin: &str, args: &[S]) -> io::Result<Outcome> {
    let mut cmd = Command::new(BIN);
    cmd.current_dir(dir)
        .args(args)
        .env_remove("NO_COLOR")
        .env_remove("FORCE_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let output = common::run_with_stdin(cmd, stdin.as_bytes())?;
    Ok(Outcome {
        code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

struct Scratch(PathBuf);

impl Scratch {
    fn new(files: &[(&str, &str)]) -> io::Result<Scratch> {
        let dir = std::env::temp_dir().join(format!(
            "emd-lint-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&dir)?;
        let scratch = Scratch(dir);
        for (name, text) in files {
            let path = scratch.0.join(name);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(path, text)?;
        }
        Ok(scratch)
    }

    fn path(&self, name: &str) -> String {
        self.0.join(name).display().to_string()
    }

    fn read(&self, name: &str) -> io::Result<String> {
        fs::read_to_string(self.0.join(name))
    }

    fn run<S: AsRef<OsStr>>(&self, stdin: &str, args: &[S]) -> io::Result<Outcome> {
        invoke(&self.0, stdin, args)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn golden_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec/golden/lint")
}

fn expect(outcome: &Outcome, stdout: &str, stderr: &str, code: i32) {
    assert_eq!(
        (
            outcome.code,
            outcome.stdout.as_str(),
            outcome.stderr.as_str()
        ),
        (Some(code), stdout, stderr)
    );
}

fn expect_run<S: AsRef<OsStr>>(
    scratch: &Scratch,
    stdin: &str,
    args: &[S],
    stdout: &str,
    stderr: &str,
    code: i32,
) -> io::Result<()> {
    expect(&scratch.run(stdin, args)?, stdout, stderr, code);
    Ok(())
}

#[test]
fn lint_goldens_match_in_all_four_formats() -> io::Result<()> {
    let dir = golden_dir();
    for (name, code) in [
        ("error-duplicate-ids", 1),
        ("warning-quote-unclosed", 0),
        ("safe-fix-arrow-invalid", 1),
        ("unsafe-fix-end-without-subgraph", 1),
        ("suppressed-duplicate-ids", 0),
    ] {
        for format in ["text", "json", "sarif", "github"] {
            let want = fs::read_to_string(dir.join(format!("{name}.{format}")))?;
            let args = [
                "lint",
                "--no-config",
                "--color",
                "never",
                "--output-format",
                format,
                &format!("{name}.mmd"),
            ];
            expect(&invoke(&dir, "", &args)?, &want, "", code);
        }
    }
    Ok(())
}

#[test]
fn severity_override_keeps_the_golden_text() -> io::Result<()> {
    let golden = golden_dir();
    let source = fs::read_to_string(golden.join("error-duplicate-ids.mmd"))?;
    let want = fs::read_to_string(golden.join("error-duplicate-ids.info.txt"))?;
    let scratch = Scratch::new(&[
        ("error-duplicate-ids.mmd", &source),
        (
            "emd.json",
            "{\"lint\":{\"severity\":{\"flowchart/duplicate-ids\":\"info\"}}}",
        ),
    ])?;
    let args = [
        "lint",
        "--color",
        "never",
        "--output-format",
        "text",
        "error-duplicate-ids.mmd",
    ];
    expect_run(&scratch, "", &args, &want, "", 0)
}

#[test]
fn check_machine_formats_match_the_lint_goldens() -> io::Result<()> {
    let dir = golden_dir();
    for name in ["safe-fix-arrow-invalid", "unsafe-fix-end-without-subgraph"] {
        for (format, extension) in [("sarif", "sarif"), ("github", "github")] {
            let want = fs::read_to_string(dir.join(format!("{name}.{extension}")))?;
            let args = ["check", "--output-format", format, &format!("{name}.mmd")];
            expect(&invoke(&dir, "", &args)?, &want, "", 1);
        }
    }
    for (format, extension) in [("sarif", "sarif"), ("github", "github")] {
        let want = fs::read_to_string(dir.join(format!("warning-quote-unclosed.{extension}")))?;
        let args = [
            "check",
            "--output-format",
            format,
            "warning-quote-unclosed.mmd",
        ];
        expect(&invoke(&dir, "", &args)?, &want, "", 0);
    }
    let want = fs::read_to_string(dir.join("suppressed-duplicate-ids.sarif"))?;
    let args = [
        "check",
        "--output-format",
        "sarif",
        "suppressed-duplicate-ids.mmd",
    ];
    expect(&invoke(&dir, "", &args)?, &want, "", 0);
    Ok(())
}

#[test]
fn fix_on_stdin_writes_the_fixed_source() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    expect_run(&scratch, ARROW, &["lint", "--fix", "-"], ARROW_FIXED, "", 0)?;
    let safe_only = scratch.run(END, &["lint", "--fix", "-"])?;
    assert_eq!((safe_only.code, safe_only.stdout.as_str()), (Some(1), END));
    assert!(
        safe_only
            .stderr
            .starts_with("<stdin>:3:3: error[flowchart/end-without-subgraph]"),
        "{}",
        safe_only.stderr
    );
    expect_run(
        &scratch,
        END,
        &["lint", "--fix", "--unsafe-fixes", "-"],
        END_FIXED,
        "",
        0,
    )?;
    expect_run(
        &scratch,
        END,
        &["lint", "--fix", "--output-format", "text", "-"],
        END,
        &safe_only.stderr,
        1,
    )
}

const QUOTE: &str = "sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n";
const QUOTE_FIXED: &str = "sequenceDiagram\n  participant \"Bob\"\n  A->>Bob: hi\n";

#[test]
fn unclosed_quote_needs_unsafe_fixes_and_is_only_a_warning() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let safe_only = scratch.run(QUOTE, &["lint", "--fix", "-"])?;
    assert_eq!(
        (safe_only.code, safe_only.stdout.as_str()),
        (Some(0), QUOTE)
    );
    assert!(
        safe_only
            .stderr
            .starts_with("<stdin>:2:15: warning[sequence/quote-unclosed]"),
        "{}",
        safe_only.stderr
    );
    expect_run(
        &scratch,
        QUOTE,
        &["lint", "--fix", "--unsafe-fixes", "-"],
        QUOTE_FIXED,
        "",
        0,
    )?;
    let denied = scratch.run(QUOTE, &["lint", "--deny-warnings", "-"])?;
    assert_eq!(denied.code, Some(1));
    Ok(())
}

const HOST_FIXTURE: &str = "# T\n\n> ```mermaid\n> sequenceDiagram\n>   participant \"Bob\n>   A->>Bob: hi\n> ```\n\n```mermaid\nflowchart TD\n  A --> B\n  end\n```\n";
const HOST_FIXED: &str = "# T\n\n> ```mermaid\n> sequenceDiagram\n>   participant \"Bob\"\n>   A->>Bob: hi\n> ```\n\n```mermaid\nflowchart TD\n  A --> B\n```\n";

fn host_report(format: &str) -> &'static str {
    match format {
        "text" => {
            "doc.md:5:17: warning[sequence/quote-unclosed]: A participant or actor name or alias starts a quote but does not close it\n  |\n5 | >   participant \"Bob\n  |                 ^~~~\n  = help: Close the quote: participant \"Bob\" or participant Alice as \"Alias\"\n  = fix: Insert the closing quote\n\ndoc.md:12:3: error[flowchart/end-without-subgraph]: end appears without a matching subgraph\n   |\n12 |   end\n   |   ^~~\n  = help: Remove this end line, or add a subgraph above it.\n  = fix: Remove the stray end line\n"
        }
        "json" => {
            "{\"version\":1,\"files\":[{\"path\":\"doc.md\",\"kind\":null,\"diagnostics\":[{\"code\":\"sequence/quote-unclosed\",\"severity\":\"warning\",\"message\":\"A participant or actor name or alias starts a quote but does not close it\",\"span\":{\"start\":52,\"end\":56},\"line\":5,\"column\":17,\"end_line\":5,\"end_column\":21,\"related\":[],\"help\":\"Close the quote: participant \\\"Bob\\\" or participant Alice as \\\"Alias\\\"\",\"fixes\":[{\"title\":\"Insert the closing quote\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":56,\"end\":56},\"new_text\":\"\\\"\"}]}]},{\"code\":\"flowchart/end-without-subgraph\",\"severity\":\"error\",\"message\":\"end appears without a matching subgraph\",\"span\":{\"start\":116,\"end\":119},\"line\":12,\"column\":3,\"end_line\":12,\"end_column\":6,\"related\":[],\"help\":\"Remove this end line, or add a subgraph above it.\",\"fixes\":[{\"title\":\"Remove the stray end line\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":114,\"end\":120},\"new_text\":\"\"}]}]}]}],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":1,\"info\":0}}\n"
        }
        "sarif" => {
            "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"emd\",\"version\":\"0.1.0\",\"rules\":[{\"id\":\"flowchart/end-without-subgraph\",\"shortDescription\":{\"text\":\"end appears without a matching subgraph\"},\"help\":{\"text\":\"Remove this end line, or add a subgraph above it.\"}},{\"id\":\"sequence/quote-unclosed\",\"shortDescription\":{\"text\":\"A participant or actor name or alias starts a quote but does not close it\"},\"help\":{\"text\":\"Close the quote: participant \\\"Bob\\\" or participant Alice as \\\"Alias\\\"\"}}]}},\"results\":[{\"ruleId\":\"sequence/quote-unclosed\",\"level\":\"warning\",\"message\":{\"text\":\"A participant or actor name or alias starts a quote but does not close it\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"doc.md\"},\"region\":{\"startLine\":5,\"startColumn\":17,\"endLine\":5,\"endColumn\":21}}}]},{\"ruleId\":\"flowchart/end-without-subgraph\",\"level\":\"error\",\"message\":{\"text\":\"end appears without a matching subgraph\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"doc.md\"},\"region\":{\"startLine\":12,\"startColumn\":3,\"endLine\":12,\"endColumn\":6}}}]}]}]}\n"
        }
        _ => {
            "::warning file=doc.md,line=5,col=17,endLine=5,endColumn=21,title=sequence/quote-unclosed::A participant or actor name or alias starts a quote but does not close it\n::error file=doc.md,line=12,col=3,endLine=12,endColumn=6,title=flowchart/end-without-subgraph::end appears without a matching subgraph\n"
        }
    }
}

#[test]
fn markdown_host_reports_match_the_go_bytes_in_all_four_formats() -> io::Result<()> {
    let scratch = Scratch::new(&[("doc.md", HOST_FIXTURE)])?;
    for format in ["text", "json", "sarif", "github"] {
        let args = [
            "lint",
            "--no-config",
            "--color",
            "never",
            "--output-format",
            format,
            "doc.md",
        ];
        expect_run(&scratch, "", &args, host_report(format), "", 1)?;
    }
    Ok(())
}

#[test]
fn markdown_host_fix_keeps_fence_edges() -> io::Result<()> {
    let scratch = Scratch::new(&[("doc.md", HOST_FIXTURE)])?;
    let path = scratch.path("doc.md");
    let safe_only = scratch.run("", &["lint", "--fix", "--no-config", &path])?;
    assert_eq!(safe_only.code, Some(1));
    assert_eq!(scratch.read("doc.md")?, HOST_FIXTURE);
    let args = ["lint", "--fix", "--unsafe-fixes", "--no-config", &path];
    expect_run(&scratch, "", &args, "", "", 0)?;
    assert_eq!(scratch.read("doc.md")?, HOST_FIXED);
    Ok(())
}

#[test]
fn stdin_diagnostics_use_the_stdin_path() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let outcome = scratch.run(ARROW, &["lint", "-"])?;
    assert_eq!(outcome.code, Some(1));
    assert!(
        outcome
            .stdout
            .starts_with("<stdin>:2:5: error[flowchart/arrow-invalid]")
    );
    expect_run(&scratch, CLEAN, &["lint", "-"], "", "", 0)?;
    let github = scratch.run(ARROW, &["lint", "--output-format", "github", "-"])?;
    assert_eq!(github.code, Some(1));
    assert!(github.stdout.starts_with(
        "::error file=<stdin>,line=2,col=5,endLine=2,endColumn=7,title=flowchart/arrow-invalid::"
    ));
    Ok(())
}

#[test]
fn fix_rewrites_files_in_place_and_keeps_their_mode() -> io::Result<()> {
    let scratch = Scratch::new(&[
        ("a.mmd", ARROW),
        ("unsafe.mmd", END),
        ("dup.mmd", DUPLICATE),
    ])?;
    let (arrow, unsafe_file, dup) = (
        scratch.path("a.mmd"),
        scratch.path("unsafe.mmd"),
        scratch.path("dup.mmd"),
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&arrow, fs::Permissions::from_mode(0o640))?;
    }
    expect_run(&scratch, "", &["lint", "--fix", &arrow], "", "", 0)?;
    assert_eq!(scratch.read("a.mmd")?, ARROW_FIXED);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(fs::metadata(&arrow)?.permissions().mode() & 0o777, 0o640);
    }
    assert_eq!(
        fs::read_dir(&scratch.0)?.count(),
        3,
        "no temporary file remains"
    );

    let kept = scratch.run("", &["lint", "--fix", &unsafe_file])?;
    assert_eq!(kept.code, Some(1));
    assert!(
        kept.stdout
            .contains("error[flowchart/end-without-subgraph]")
    );
    assert_eq!(scratch.read("unsafe.mmd")?, END);
    expect_run(
        &scratch,
        "",
        &["lint", "--fix", "--unsafe-fixes", &unsafe_file],
        "",
        "",
        0,
    )?;
    assert_eq!(scratch.read("unsafe.mmd")?, END_FIXED);

    let no_fix = scratch.run("", &["lint", "--fix", &dup])?;
    assert_eq!(no_fix.code, Some(1));
    assert!(no_fix.stdout.contains("error[flowchart/duplicate-ids]"));
    assert_eq!(scratch.read("dup.mmd")?, DUPLICATE);
    Ok(())
}

#[test]
fn exit_codes_follow_severity_and_deny_warnings() -> io::Result<()> {
    let scratch = Scratch::new(&[("beta.mmd", BETA), ("dup.mmd", DUPLICATE)])?;
    let (beta, dup) = (scratch.path("beta.mmd"), scratch.path("dup.mmd"));
    let warning = scratch.run("", &["lint", &beta])?;
    assert_eq!(warning.code, Some(0));
    assert!(
        warning
            .stdout
            .contains("warning[common/no-experimental]: block-beta is a beta diagram type")
    );
    assert_eq!(
        scratch.run("", &["lint", "--deny-warnings", &beta])?.code,
        Some(1)
    );
    assert_eq!(scratch.run("", &["lint", &dup])?.code, Some(1));
    let ignored = scratch.run("", &["lint", "--ignore", "flowchart/duplicate-ids", &dup])?;
    assert_eq!((ignored.code, ignored.stdout.as_str()), (Some(0), ""));
    Ok(())
}

#[test]
fn usage_errors_exit_two_with_the_go_messages() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let cases: [(&[&str], &str); 11] = [
        (
            &["lint", "--unsafe-fixes", "x.mmd"],
            "--unsafe-fixes requires --fix",
        ),
        (
            &["lint", "--output-format", "xml"],
            "invalid value xml for --output-format; expected one of: text, json, sarif, github",
        ),
        (
            &["lint", "--color", "sometimes"],
            "invalid value sometimes for --color; expected one of: auto, always, never",
        ),
        (
            &["lint", "--select", "nope/code"],
            "unknown diagnostic code: nope/code; use a code printed by emd check or emd lint",
        ),
        (
            &["lint", "--ignore", "flowchart/duplicate-ids,bogus"],
            "unknown diagnostic code: bogus; use a code printed by emd check or emd lint",
        ),
        (
            &["lint", "--bogus"],
            "unknown flag --bogus; run emd lint --help",
        ),
        (&["lint", "--select"], "missing value for --select"),
        (
            &["lint", "--fix=maybe"],
            "invalid value maybe for --fix; expected one of: true, false",
        ),
        (
            &["lint", "--fix", "--output-format", "json", "-"],
            "lint --fix - supports only text diagnostics; remove --output-format or pass a file path",
        ),
        (
            &["lint", "--fix", "-", "--output-format", "sarif"],
            "lint --fix - supports only text diagnostics; remove --output-format or pass a file path",
        ),
        (
            &["check", "--output-format", "xml"],
            "invalid value xml for --output-format; expected one of: text, json, sarif, github",
        ),
    ];
    for (args, message) in cases {
        expect_run(&scratch, "", args, "", &format!("{message}\n"), 2)?;
    }
    let missing = scratch.run("", &["lint", "no-such-dir-for-emd-lint"])?;
    assert_eq!(missing.code, Some(2));
    assert!(
        missing
            .stderr
            .starts_with("cannot read no-such-dir-for-emd-lint")
    );
    Ok(())
}

#[test]
fn walk_lints_supported_files_in_byte_order_and_reports_empty_scans() -> io::Result<()> {
    let host = format!("# Title\n\n```mermaid\n{CLEAN}```\n");
    let included = format!("```mermaid\n{CLEAN}```\n");
    let scratch = Scratch::new(&[
        ("a.mmd", CLEAN),
        ("sub/b.mermaid", CLEAN),
        ("c.md", &host),
        ("d.markdown", "text only\n"),
        (".hidden/e.mmd", DUPLICATE),
        ("node_modules/f.mmd", DUPLICATE),
        ("target/g.mmd", DUPLICATE),
        ("notes.txt", DUPLICATE),
        ("empty/notes.txt", "none\n"),
        ("deep/.cache/ignored.mmd", DUPLICATE),
        ("deep/visible/included.md", &included),
    ])?;
    let scan = scratch.run("", &["lint", "--output-format", "json"])?;
    assert_eq!((scan.code, scan.stderr.as_str()), (Some(0), ""));
    let paths: Vec<&str> = scan
        .stdout
        .split("\"path\":\"")
        .skip(1)
        .filter_map(|part| part.split('"').next())
        .collect();
    assert_eq!(
        paths,
        [
            "a.mmd",
            "c.md",
            "d.markdown",
            "deep/visible/included.md",
            "sub/b.mermaid"
        ]
    );
    expect_run(
        &scratch,
        "",
        &["lint", "empty"],
        "",
        "no Mermaid files found in empty\n",
        2,
    )?;
    expect_run(
        &scratch,
        "",
        &["lint", "notes.txt"],
        "",
        "no Mermaid files found in notes.txt\n",
        2,
    )?;
    let inside = scratch.0.join("empty");
    expect(
        &invoke(&inside, "", &["lint"])?,
        "",
        "no Mermaid files found in .\n",
        0,
    );
    Ok(())
}

#[test]
fn markdown_host_diagnostics_and_fixes_use_host_positions() -> io::Result<()> {
    let host = "# Title\n\ntext\n\n```mermaid\nflowchart LR\n  A -> B\n```\n\ntail\n";
    let scratch = Scratch::new(&[("doc.md", host)])?;
    let path = scratch.path("doc.md");
    let json = scratch.run("", &["lint", "--output-format", "json", &path])?;
    assert_eq!(json.code, Some(1));
    assert!(json.stdout.contains("\"code\":\"flowchart/arrow-invalid\""));
    assert!(
        json.stdout.contains("\"line\":7,\"column\":5,"),
        "{}",
        json.stdout
    );
    expect_run(&scratch, "", &["lint", "--fix", &path], "", "", 0)?;
    assert_eq!(scratch.read("doc.md")?, host.replace("A -> B", "A --> B"));
    Ok(())
}

#[test]
fn emd_json_is_found_per_input_directory_and_flags_override_it() -> io::Result<()> {
    let scratch = Scratch::new(&[
        (
            "emd.json",
            "{\"lint\":{\"ignore\":[\"flowchart/duplicate-ids\"]}}",
        ),
        ("sub/dup.mmd", DUPLICATE),
        (
            "other.json",
            "{\"lint\":{\"severity\":{\"flowchart/duplicate-ids\":\"info\"}}}",
        ),
        (
            "select/emd.json",
            "{\"lint\":{\"select\":[\"common/no-experimental\"]}}",
        ),
        ("select/dup.mmd", DUPLICATE),
    ])?;
    let dup = scratch.path("sub/dup.mmd");
    let select_dup = scratch.path("select/dup.mmd");
    expect_run(&scratch, "", &["lint", &dup], "", "", 0)?;
    let no_config = scratch.run("", &["lint", "--no-config", &dup])?;
    assert_eq!(no_config.code, Some(1));
    assert!(no_config.stdout.contains("error[flowchart/duplicate-ids]"));
    let named = scratch.run(
        "",
        &["lint", "--lint-config", &scratch.path("other.json"), &dup],
    )?;
    assert_eq!(named.code, Some(0));
    assert!(named.stdout.contains("info[flowchart/duplicate-ids]"));
    expect_run(
        &scratch,
        "",
        &["lint", "--select", "flowchart/duplicate-ids", &dup],
        "",
        "",
        0,
    )?;
    let replaced = scratch.run("", &["lint", "--ignore", "meta/unknown-rule", &dup])?;
    assert_eq!(replaced.code, Some(1));
    assert!(replaced.stdout.contains("error[flowchart/duplicate-ids]"));
    expect_run(&scratch, "", &["lint", &select_dup], "", "", 0)?;
    let flag_select = scratch.run(
        "",
        &["lint", "--select", "flowchart/duplicate-ids", &select_dup],
    )?;
    assert_eq!(flag_select.code, Some(1));
    assert!(flag_select.stdout.contains("duplicate-ids"));
    Ok(())
}

#[test]
fn emd_json_errors_name_the_file_and_stop_the_run() -> io::Result<()> {
    let scratch = Scratch::new(&[
        ("bad/emd.json", "{\"lint\":"),
        ("bad/dup.mmd", DUPLICATE),
        (
            "codes/emd.json",
            "{\"lint\":{\"select\":[\"flowchart/nope\"]}}",
        ),
        ("codes/dup.mmd", DUPLICATE),
        ("extra/emd.json", "{\"other\":1}"),
        ("extra/dup.mmd", DUPLICATE),
    ])?;
    for (name, message) in [
        ("bad", "not valid JSON"),
        ("extra", "unknown key \"other\""),
    ] {
        let config = scratch.path(&format!("{name}/emd.json"));
        let dup = scratch.path(&format!("{name}/dup.mmd"));
        let want = format!("invalid emd.json {config}: {message}\n");
        expect_run(&scratch, "", &["lint", &dup], "", &want, 2)?;
        expect_run(
            &scratch,
            "",
            &["lint", "--lint-config", &config, &dup],
            "",
            &want,
            2,
        )?;
        let skipped = scratch.run("", &["lint", "--no-config", &dup])?;
        assert_eq!(skipped.code, Some(1));
        assert!(skipped.stdout.contains("error[flowchart/duplicate-ids]"));
    }
    expect_run(
        &scratch,
        "",
        &["lint", &scratch.path("codes/dup.mmd")],
        "",
        "unknown diagnostic code: flowchart/nope; use a code printed by emd check or emd lint\n",
        2,
    )?;
    let missing = scratch.path("absent.json");
    let outcome = scratch.run(
        "",
        &[
            "lint",
            "--lint-config",
            &missing,
            &scratch.path("bad/dup.mmd"),
        ],
    )?;
    assert_eq!(outcome.code, Some(2));
    assert!(
        outcome
            .stderr
            .starts_with(&format!("cannot read {missing}: ")),
        "{}",
        outcome.stderr
    );
    Ok(())
}

#[test]
fn stdin_config_search_starts_in_the_working_directory() -> io::Result<()> {
    let scratch = Scratch::new(&[
        (
            "emd.json",
            "{\"lint\":{\"ignore\":[\"flowchart/duplicate-ids\"]}}",
        ),
        ("deep/x", ""),
    ])?;
    let deep = scratch.0.join("deep");
    expect(&invoke(&deep, DUPLICATE, &["lint", "-"])?, "", "", 0);
    let outcome = invoke(&deep, DUPLICATE, &["lint", "--no-config", "-"])?;
    assert_eq!(outcome.code, Some(1));
    assert!(
        outcome
            .stdout
            .starts_with("<stdin>:3:3: error[flowchart/duplicate-ids]")
    );
    Ok(())
}

const DUPLICATE_EXPLAIN: &str = "code: flowchart/duplicate-ids\n\
kind: flowchart\n\
severity: error\n\
fix_safety: none\n\
summary: Node id declared twice with different labels\n\
help: Give each node one label, or use a new id for the second node.\n\
rationale: Mermaid keeps one of the two declarations and drops the other, so the rendered diagram is wrong.\n\
suppression: %% emd-disable-next-line flowchart/duplicate-ids: reason\n";

const DUPLICATE_EXPLAIN_JSON: &str = "{\"code\":\"flowchart/duplicate-ids\",\"kind\":\"flowchart\",\"severity\":\"error\",\"fix_safety\":\"none\",\
\"summary\":\"Node id declared twice with different labels\",\
\"help\":\"Give each node one label, or use a new id for the second node.\",\
\"rationale\":\"Mermaid keeps one of the two declarations and drops the other, so the rendered diagram is wrong.\",\
\"suppression\":\"%% emd-disable-next-line flowchart/duplicate-ids: reason\"}\n";

#[test]
fn explain_prints_text_and_json_rows() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    expect_run(
        &scratch,
        "",
        &["explain", "flowchart/duplicate-ids"],
        DUPLICATE_EXPLAIN,
        "",
        0,
    )?;
    let json = [
        "explain",
        "flowchart/duplicate-ids",
        "--output-format",
        "json",
    ];
    expect_run(&scratch, "", &json, DUPLICATE_EXPLAIN_JSON, "", 0)?;
    let inline = ["explain", "--output-format=json", "flowchart/duplicate-ids"];
    expect_run(&scratch, "", &inline, DUPLICATE_EXPLAIN_JSON, "", 0)?;
    let alias = scratch.run("", &["explain", "flowchart/node-unclosed-bracket"])?;
    assert_eq!(alias.code, Some(0));
    assert!(alias.stdout.starts_with(
        "code: flowchart/unclosed-node-bracket\nkind: flowchart\nseverity: error\nfix_safety: unsafe\n"
    ));
    assert!(alias.stdout.ends_with(
        "suppression: %% emd-disable-next-line flowchart/unclosed-node-bracket: reason\n"
    ));
    Ok(())
}

#[test]
fn explain_kind_falls_back_to_common_and_keeps_empty_help() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    for (code, kind) in [
        ("meta/unknown-rule", "common"),
        ("config/malformed", "common"),
        ("source/invalid-utf8", "common"),
        ("common/unknown-diagram-kind", "common"),
        ("agentflow/unterminated", "agentflow"),
    ] {
        let outcome = scratch.run("", &["explain", code])?;
        assert_eq!(outcome.code, Some(0), "{code}");
        assert!(
            outcome
                .stdout
                .starts_with(&format!("code: {code}\nkind: {kind}\n")),
            "{code}"
        );
    }
    let empty = scratch.run("", &["explain", "agentflow/unterminated"])?;
    assert!(empty.stdout.contains("\nhelp: \nrationale: "));
    let off = scratch.run("", &["explain", "common/acc-title-missing"])?;
    assert!(off.stdout.contains("\nseverity: off\n"));
    Ok(())
}

#[test]
fn explain_errors_exit_two() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let cases: [(&[&str], &str); 5] = [
        (
            &["explain", "flowchart/nope"],
            "unknown diagnostic code: flowchart/nope; use a code printed by emd check or emd lint",
        ),
        (&["explain"], "missing CODE; run emd explain --help"),
        (
            &["explain", "a", "b"],
            "unexpected argument b; run emd explain --help",
        ),
        (
            &["explain", "meta/unknown-rule", "--output-format", "sarif"],
            "invalid value sarif for --output-format; expected one of: text, json",
        ),
        (
            &["explain", "--color", "never", "meta/unknown-rule"],
            "unknown flag --color; run emd explain --help",
        ),
    ];
    for (args, message) in cases {
        expect_run(&scratch, "", args, "", &format!("{message}\n"), 2)?;
    }
    Ok(())
}

#[test]
fn help_lists_lint_explain_and_check_forms() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let root = scratch.run("", &["--help"])?;
    assert_eq!(root.code, Some(0));
    assert!(
        root.stdout
            .contains("lint     Check lint rules and optionally apply fixes\n")
    );
    assert!(root.stdout.contains("explain  Explain a diagnostic code\n"));
    for (command, example) in [
        ("lint", "Example: emd lint --fix demo.mmd\n"),
        (
            "explain",
            "Example: emd explain flowchart/unexpected-token\n",
        ),
        ("check", "Example: emd check docs/\n"),
    ] {
        let help = scratch.run("", &[command, "--help"])?;
        assert_eq!(help.code, Some(0), "{command}");
        assert!(help.stdout.ends_with(example), "{command}: {}", help.stdout);
    }
    let lint = scratch.run("", &["lint", "--help"])?;
    for flag in [
        "--fix",
        "--unsafe-fixes",
        "--select CODES",
        "--ignore CODES",
        "--deny-warnings",
        "--output-format text|json|sarif|github",
        "--lint-config FILE",
        "--no-config",
        "--color auto|always|never",
    ] {
        assert!(lint.stdout.contains(flag), "lint help lacks {flag}");
    }
    let check = scratch.run("", &["check", "--help"])?;
    assert!(
        check
            .stdout
            .contains("--output-format text|json|sarif|github")
    );
    Ok(())
}

fn strip_sgr(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(ch) = chars.next() {
        if ch == '\u{1b}' {
            for skipped in chars.by_ref() {
                if skipped == 'm' {
                    break;
                }
            }
        } else {
            out.push(ch);
        }
    }
    out
}

#[test]
fn colour_applies_to_text_only() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let always = scratch.run(ARROW, &["lint", "--color", "always", "-"])?;
    assert!(always.stdout.contains("\u{1b}["), "{}", always.stdout);
    let never = scratch.run(ARROW, &["lint", "--color", "never", "-"])?;
    assert!(!never.stdout.contains('\u{1b}'));
    assert_eq!(strip_sgr(&always.stdout), never.stdout);
    for format in ["json", "sarif", "github"] {
        let machine = scratch.run(
            ARROW,
            &["lint", "--color", "always", "--output-format", format, "-"],
        )?;
        assert!(!machine.stdout.contains('\u{1b}'), "{format}");
    }
    let fixed = scratch.run(END, &["lint", "--fix", "--color", "always", "-"])?;
    assert!(fixed.stderr.contains("\u{1b}["), "{}", fixed.stderr);
    Ok(())
}

#[test]
fn meta_diagnostics_follow_the_configuration() -> io::Result<()> {
    let source = "flowchart LR\n  %% emd-disable-next-line flowchart/duplicate-ids: nothing to hide\n  A --> B\n";
    let scratch = Scratch::new(&[("u.mmd", source)])?;
    let shown = scratch.run("", &["lint", "--no-config", "u.mmd"])?;
    assert_eq!(shown.code, Some(0));
    assert!(
        shown.stdout.contains("warning[meta/unused-suppression]"),
        "{}",
        shown.stdout
    );
    let ignored = scratch.run(
        "",
        &[
            "lint",
            "--no-config",
            "--ignore",
            "meta/unused-suppression",
            "u.mmd",
        ],
    )?;
    assert_eq!((ignored.code, ignored.stdout.as_str()), (Some(0), ""));
    let denied = scratch.run("", &["lint", "--no-config", "--deny-warnings", "u.mmd"])?;
    assert_eq!(denied.code, Some(1));
    Ok(())
}

#[test]
fn file_directives_cover_every_block_and_are_reported_once() -> io::Result<()> {
    let directive = "<!-- emd-disable-file flowchart/duplicate-ids: ids -->\n";
    let block = format!("```mermaid\n{DUPLICATE}```\n");
    let covered = format!("{directive}{block}\n{block}");
    let clean = format!("{directive}```mermaid\n{CLEAN}```\n```mermaid\n{CLEAN}```\n");
    let scratch = Scratch::new(&[("covered.md", &covered), ("clean.md", &clean)])?;
    expect_run(
        &scratch,
        "",
        &["lint", "--no-config", "covered.md"],
        "",
        "",
        0,
    )?;
    let unused = scratch.run("", &["lint", "--no-config", "--color", "never", "clean.md"])?;
    assert_eq!(unused.code, Some(0));
    assert_eq!(
        unused.stdout.matches("meta/unused-suppression").count(),
        1,
        "{}",
        unused.stdout
    );
    assert!(
        unused
            .stdout
            .starts_with("clean.md:1:1: warning[meta/unused-suppression]")
    );
    Ok(())
}

#[test]
fn file_directive_tokens_and_foreign_fences_follow_the_go_grammar() -> io::Result<()> {
    let unknown =
        format!("<!-- emd-disable-file flowchart/nope: reason -->\n```mermaid\n{CLEAN}```\n");
    let foreign = format!(
        "```rust\n<!-- emd-disable-file flowchart/duplicate-ids: r -->\n```\n```mermaid\n{DUPLICATE}```\n"
    );
    let loose = format!(
        "<!-- emd-disable-file flowchart/duplicate-ids , common/no-experimental: r -->\n```mermaid\n{DUPLICATE}```\n"
    );
    let scratch = Scratch::new(&[("u.md", &unknown), ("f.md", &foreign), ("l.md", &loose)])?;
    let token = scratch.run("", &["lint", "--no-config", "--color", "never", "u.md"])?;
    assert_eq!(
        token.stdout.lines().next(),
        Some("u.md:1:23: warning[meta/unknown-rule]: unknown rule flowchart/nope")
    );
    assert!(
        !token.stdout.contains("meta/unused-suppression"),
        "{}",
        token.stdout
    );
    let kept = scratch.run("", &["lint", "--no-config", "f.md"])?;
    assert_eq!(kept.code, Some(1));
    assert!(kept.stdout.contains("error[flowchart/duplicate-ids]"));
    let malformed = scratch.run("", &["lint", "--no-config", "l.md"])?;
    assert!(
        malformed
            .stdout
            .contains("warning[meta/malformed-suppression]")
    );
    assert!(malformed.stdout.contains("error[flowchart/duplicate-ids]"));
    Ok(())
}

#[test]
fn block_directive_grammar_matches_go() -> io::Result<()> {
    let scratch = Scratch::new(&[])?;
    let src = |directive: &str| {
        format!("flowchart LR\n  A[S] --> B[E]\n  {directive}\n  A[T] --> C[E]\n")
    };
    let cases = [
        (
            "%% emd-disable-next-line flowchart/duplicate-ids,  common/no-experimental: r",
            "meta/malformed-suppression",
        ),
        (
            "%% emd-disable-next-line flowchart/node-unclosed-bracket: r",
            "meta/malformed-suppression",
        ),
        (
            "%% emd-disable-next-line flowchart/nope: r",
            "meta/unknown-rule",
        ),
    ];
    for (directive, want) in cases {
        let out = scratch.run(&src(directive), &["lint", "--no-config", "-"])?;
        assert!(out.stdout.contains(want), "{directive}: {}", out.stdout);
        assert!(
            !out.stdout.contains("meta/unused-suppression"),
            "{directive}: {}",
            out.stdout
        );
    }
    let trailing = scratch.run(
        &src("%% emd-disable-next-line flowchart/duplicate-ids: r   "),
        &["lint", "--no-config", "--output-format", "json", "-"],
    )?;
    assert_eq!(trailing.code, Some(0));
    assert_eq!(trailing.stdout.matches("\"code\":").count(), 0);
    Ok(())
}
