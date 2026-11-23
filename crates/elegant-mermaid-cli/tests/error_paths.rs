use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> io::Result<Self> {
        let root = std::env::temp_dir().join(format!("emd-error-paths-{}", std::process::id()));
        if root.exists() {
            fs::remove_dir_all(&root)?;
        }
        fs::create_dir(&root)?;
        Ok(Self(root))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn binary() -> OsString {
    std::env::var_os("EMD_BIN").unwrap_or_else(|| OsString::from(env!("CARGO_BIN_EXE_emd")))
}

struct Case {
    args: &'static [&'static str],
    stdout: &'static str,
    stderr: &'static str,
    code: i32,
}

const fn failure(args: &'static [&'static str], stderr: &'static str) -> Case {
    Case {
        args,
        stdout: "",
        stderr,
        code: 2,
    }
}

const fn refusal(args: &'static [&'static str], stderr: &'static str) -> Case {
    Case {
        args,
        stdout: "",
        stderr,
        code: 1,
    }
}

fn run(root: &Path, executable: &Path, args: &[&str]) -> io::Result<(String, String, Option<i32>)> {
    let output = Command::new(executable)
        .args(args)
        .current_dir(root)
        .stdin(std::process::Stdio::null())
        .output()?;
    Ok((
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.code(),
    ))
}

fn chain_diagram(edges: usize) -> String {
    let links: String = (0..edges)
        .map(|i| format!("n{i}[node] --> n{}\n", i + 1))
        .collect();
    format!("flowchart LR\n{links}")
}

fn write_fixtures(root: &Path) -> io::Result<()> {
    for (name, bytes) in [
        ("good.mmd", &b"flowchart LR\n A[alpha] --> B\n"[..]),
        ("broken.dump", b"{\"nope"),
        ("latin1.dump", b"\xff"),
        ("model.dump", b"{\"version\":1,\"stage\":\"model\"}"),
        ("broken.yaml", b"not: [valid"),
        ("list.yaml", b"- a\n"),
        ("seed.yaml", b"handDrawnSeed: -3\n"),
        ("latin1.yaml", b"a: \xff\n"),
        ("broken.json", b"{\"prefix\":\"x\",\"icons\":"),
        ("latin1.json", b"\xff\xfe"),
        ("cases.txt", b"1 +\n"),
        ("cases-ok.txt", b"isqrt 99 -> 9\n"),
    ] {
        fs::write(root.join(name), bytes)?;
    }
    fs::write(
        root.join("big.mmd"),
        format!(
            "---\nconfig:\n  maxEdges: 5000\n---\n{}",
            chain_diagram(2001)
        ),
    )?;
    fs::write(root.join("wide.mmd"), chain_diagram(400))?;
    fs::create_dir(root.join("dir"))
}

const CASES: &[Case] = &[
    failure(
        &["view", "missing.mmd"],
        "cannot read missing.mmd: no such file or directory\n",
    ),
    failure(&["view", "dir"], "cannot read dir: is a directory\n"),
    failure(&["view", "a", "b"], "view accepts one INPUT\n"),
    failure(
        &["view"],
        "view requires a readable file path; stdin is not supported\n",
    ),
    failure(
        &["view", "-"],
        "view requires a readable file path; stdin is not supported\n",
    ),
    failure(
        &["view", "--graphics", "bogus"],
        "view requires a readable file path; stdin is not supported\n",
    ),
    failure(
        &["view", "missing.mmd", "-t", "nope"],
        "unknown theme: nope\n",
    ),
    failure(
        &["view", "good.mmd", "--script", "missing.script"],
        "cannot read missing.script: no such file or directory\n",
    ),
    failure(
        &["view", "good.mmd", "--script", "dir"],
        "cannot read dir: is a directory\n",
    ),
    failure(
        &["layout", "--dump", "good.mmd"],
        "--dump requires --metrics\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "missing.dump"],
        "cannot read missing.dump: no such file or directory\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "dir"],
        "cannot read dir: is a directory\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "broken.dump"],
        "broken.dump: malformed layout dump: invalid JSON\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "good.mmd"],
        "good.mmd: malformed layout dump: invalid JSON\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "latin1.dump"],
        "latin1.dump: malformed layout dump: invalid UTF-8\n",
    ),
    failure(
        &["layout", "--metrics", "--dump", "model.dump"],
        "model.dump: malformed layout dump: expected version 1 layout dump\n",
    ),
    refusal(
        &["layout", "big.mmd"],
        "model exceeds the limit of 2000; actual 2002\n",
    ),
    refusal(
        &["layout", "--metrics", "big.mmd"],
        "model exceeds the limit of 2000; actual 2002\n",
    ),
    refusal(
        &["render", "big.mmd", "-e", "svg"],
        "model exceeds the limit of 2000; actual 2002\n",
    ),
    refusal(
        &["render", "big.mmd", "-e", "text"],
        "model exceeds the limit of 2000; actual 2002\n",
    ),
    refusal(
        &[
            "render", "wide.mmd", "-e", "png", "-s", "8", "-o", "out.png",
        ],
        "image is too large: 340289x544 pixels\n",
    ),
    failure(
        &["layout", "missing.mmd"],
        "cannot read missing.mmd: no such file or directory\n",
    ),
    failure(
        &["render", "missing.mmd"],
        "cannot read missing.mmd: no such file or directory\n",
    ),
    failure(&["render", "dir"], "cannot read dir: is a directory\n"),
    failure(
        &["render", "-o", "absent/out.svg", "good.mmd"],
        "cannot write absent/out.svg: no such file or directory\n",
    ),
    failure(
        &["render", "-e", "svg", "-o", "dir", "good.mmd"],
        "cannot write dir: is a directory\n",
    ),
    failure(
        &["render", "-c", "missing.yaml", "good.mmd"],
        "cannot read missing.yaml: no such file or directory\n",
    ),
    failure(
        &["render", "-c", "broken.yaml", "good.mmd"],
        "broken.yaml: invalid config: malformed config value\n",
    ),
    failure(
        &["render", "-c", "list.yaml", "good.mmd"],
        "list.yaml: invalid config: config must be a mapping\n",
    ),
    failure(
        &["render", "-c", "seed.yaml", "good.mmd"],
        "seed.yaml: invalid config: invalid config value -3 for handDrawnSeed\n",
    ),
    failure(
        &["render", "-c", "latin1.yaml", "good.mmd"],
        "latin1.yaml: invalid config: invalid UTF-8 at byte 3\n",
    ),
    failure(
        &["render", "--icon-pack", "missing.json", "good.mmd"],
        "cannot read missing.json: no such file or directory\n",
    ),
    failure(
        &["render", "--icon-pack", "broken.json", "good.mmd"],
        "broken.json: malformed icon pack: invalid JSON at byte 22: expected a value\n",
    ),
    failure(
        &["render", "--icon-pack", "latin1.json", "good.mmd"],
        "latin1.json: malformed icon pack: invalid UTF-8\n",
    ),
    failure(
        &["check", "missing.mmd"],
        "cannot read missing.mmd: no such file or directory\n",
    ),
    failure(
        &["lint", "missing.mmd"],
        "cannot read missing.mmd: no such file or directory\n",
    ),
    Case {
        args: &["kernel-eval", "-h"],
        stdout: "Usage: emd kernel-eval FILE\n",
        stderr: "",
        code: 0,
    },
    Case {
        args: &["kernel-eval", "--help"],
        stdout: "Usage: emd kernel-eval FILE\n",
        stderr: "",
        code: 0,
    },
    failure(
        &["kernel-eval", "--bogus"],
        "unknown flag --bogus; run emd kernel-eval --help\n",
    ),
    failure(
        &["kernel-eval", "a", "b"],
        "kernel-eval accepts one INPUT\n",
    ),
    failure(
        &["kernel-eval", "missing"],
        "cannot read missing: no such file or directory\n",
    ),
    failure(&["kernel-eval", "dir"], "cannot read dir: is a directory\n"),
    failure(&["kernel-eval", "cases.txt"], "bad case line 1\n"),
    Case {
        args: &["kernel-eval", "cases-ok.txt"],
        stdout: "9\n",
        stderr: "",
        code: 0,
    },
];

#[test]
fn error_paths() -> io::Result<()> {
    let scratch = Scratch::new()?;
    write_fixtures(&scratch.0)?;
    let executable = fs::canonicalize(binary())?;
    for case in CASES {
        let (stdout, stderr, code) = run(&scratch.0, &executable, case.args)?;
        assert_eq!(
            (stdout.as_str(), stderr.as_str(), code),
            (case.stdout, case.stderr, Some(case.code)),
            "{:?}",
            case.args
        );
    }
    Ok(())
}

const SCRIPTS: &[(&str, &str, &str)] = &[
    (
        "unknown verb",
        "bogus 1 2\n",
        "events.script:1: unknown verb bogus\n",
    ),
    (
        "settle argument",
        "settle now\n",
        "events.script:1: settle takes no arguments\n",
    ),
    (
        "delete argument",
        "file-delete now\n",
        "events.script:1: file-delete takes no arguments\n",
    ),
    (
        "missing source",
        "file-change\n",
        "events.script:1: missing source path\n",
    ),
    (
        "unreadable source",
        "file-change nothere.mmd\n",
        "events.script:1: cannot read nothere.mmd: no such file or directory\n",
    ),
    (
        "resize arguments",
        "resize 80\n",
        "events.script:1: expected resize W H\n",
    ),
    (
        "resize too small",
        "resize 19 24\n",
        "events.script:1: size requires W >= 20 and H >= 5\n",
    ),
    (
        "resize overflow",
        "resize 99999999999999999999 24\n",
        "events.script:1: size requires W >= 20 and H >= 5\n",
    ),
    (
        "resize not a number",
        "resize 80 x\n",
        "events.script:1: size requires W >= 20 and H >= 5\n",
    ),
    ("empty key", "key\n", "events.script:1: invalid key\n"),
    ("long key", "key ab\n", "events.script:1: invalid key\n"),
    (
        "line number",
        "\n# comment\nbogus\n",
        "events.script:3: unknown verb bogus\n",
    ),
];

const BYTE_SCRIPTS: &[(&str, &[u8], &str)] = &[
    (
        "invalid UTF-8",
        b"settle\n\xff\n",
        "events.script:2: invalid UTF-8\n",
    ),
    (
        "invalid UTF-8 in a comment",
        b"# \xc3(\nsettle\n",
        "events.script:1: invalid UTF-8\n",
    ),
    (
        "invalid UTF-8 in an argument",
        b"file-change \xff.mmd\n",
        "events.script:1: invalid UTF-8\n",
    ),
    (
        "truncated UTF-8 before CRLF",
        b"settle\r\n\xe2\x82\r\n",
        "events.script:2: invalid UTF-8\n",
    ),
    (
        "earlier error first",
        b"bogus\n\xff\n",
        "events.script:1: unknown verb bogus\n",
    ),
];

#[test]
fn view_script_errors() -> io::Result<()> {
    let scratch = Scratch::new()?;
    write_fixtures(&scratch.0)?;
    let executable = fs::canonicalize(binary())?;
    let scripts = SCRIPTS
        .iter()
        .map(|(name, script, message)| (*name, script.as_bytes(), *message))
        .chain(BYTE_SCRIPTS.iter().copied());
    for (name, script, message) in scripts {
        fs::write(scratch.0.join("events.script"), script)?;
        let (stdout, stderr, code) = run(
            &scratch.0,
            &executable,
            &["view", "good.mmd", "--script", "events.script"],
        )?;
        assert_eq!(
            (stdout.as_str(), stderr.as_str(), code),
            ("", message, Some(2)),
            "{name}"
        );
    }
    Ok(())
}

#[test]
fn view_script_quit_skips_invalid_utf8() -> io::Result<()> {
    let scratch = Scratch::new()?;
    write_fixtures(&scratch.0)?;
    fs::write(scratch.0.join("events.script"), b"settle\nkey q\n\xff\n")?;
    let executable = fs::canonicalize(binary())?;
    let (stdout, stderr, code) = run(
        &scratch.0,
        &executable,
        &["view", "good.mmd", "--script", "events.script"],
    )?;
    assert_eq!((stderr.as_str(), code), ("", Some(0)));
    assert!(!stdout.is_empty());
    Ok(())
}

#[test]
fn view_script_whitespace_is_free() -> io::Result<()> {
    let scratch = Scratch::new()?;
    write_fixtures(&scratch.0)?;
    fs::write(
        scratch.0.join("events.script"),
        "settle\nresize  40   12 \n",
    )?;
    let executable = fs::canonicalize(binary())?;
    let (stdout, stderr, code) = run(
        &scratch.0,
        &executable,
        &["view", "good.mmd", "--script", "events.script"],
    )?;
    assert_eq!((stderr.as_str(), code), ("", Some(0)));
    assert_eq!(stdout.lines().count(), 12);
    assert!(stdout.lines().all(|line| line.chars().count() == 40));
    Ok(())
}
