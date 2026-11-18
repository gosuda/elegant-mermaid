use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> io::Result<Self> {
        let root = std::env::temp_dir().join(format!("emd-flag-spelling-{}", std::process::id()));
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

type Outcome = (String, String, Option<i32>);

fn binary() -> OsString {
    std::env::var_os("EMD_BIN").unwrap_or_else(|| OsString::from(env!("CARGO_BIN_EXE_emd")))
}

fn run(root: &Path, args: &[&str]) -> io::Result<Outcome> {
    let output = Command::new(binary())
        .args(args)
        .current_dir(root)
        .stdin(Stdio::null())
        .output()?;
    Ok((
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.code(),
    ))
}

const SPELLINGS: &[&[&[&str]]] = &[
    &[
        &[
            "view",
            "good.mmd",
            "--script",
            "ok.script",
            "-t",
            "elegant-dark",
            "--color",
            "never",
            "--graphics",
            "cells",
        ],
        &[
            "view",
            "good.mmd",
            "-script=ok.script",
            "-t=elegant-dark",
            "-color=never",
            "-graphics=cells",
        ],
        &[
            "view",
            "good.mmd",
            "--script=ok.script",
            "--t=elegant-dark",
            "--color=never",
            "--graphics=cells",
        ],
        &[
            "view",
            "--script",
            "ok.script",
            "-t=elegant-dark",
            "good.mmd",
            "-color",
            "never",
            "--graphics=cells",
        ],
        &[
            "view",
            "-script",
            "ok.script",
            "--t",
            "elegant-dark",
            "-color=never",
            "-graphics",
            "cells",
            "--",
            "good.mmd",
        ],
    ],
    &[
        &[
            "render",
            "good.mmd",
            "-e",
            "text",
            "--charset",
            "ascii",
            "--width",
            "12",
            "--color",
            "never",
        ],
        &[
            "render",
            "good.mmd",
            "-e=text",
            "-charset=ascii",
            "-width=12",
            "-color=never",
        ],
        &[
            "render",
            "good.mmd",
            "--e=text",
            "--charset=ascii",
            "--width=12",
            "--color=never",
        ],
        &[
            "render", "-width", "12", "--e", "text", "good.mmd", "-charset", "ascii", "--color",
            "never",
        ],
    ],
    &[
        &[
            "check",
            "good.mmd",
            "--output-format",
            "json",
            "--color",
            "never",
        ],
        &["check", "good.mmd", "-output-format=json", "-color=never"],
        &[
            "check",
            "-output-format",
            "json",
            "good.mmd",
            "--color=never",
        ],
    ],
    &[
        &[
            "lint",
            "good.mmd",
            "--output-format",
            "json",
            "--no-config",
            "--deny-warnings",
        ],
        &[
            "lint",
            "good.mmd",
            "-output-format=json",
            "-no-config=true",
            "-deny-warnings=1",
        ],
        &[
            "lint",
            "good.mmd",
            "--output-format=json",
            "--no-config=T",
            "--deny-warnings=TRUE",
        ],
        &[
            "lint",
            "--no-config",
            "-output-format",
            "json",
            "good.mmd",
            "-deny-warnings",
        ],
    ],
    &[
        &[
            "layout",
            "good.mmd",
            "--profile",
            "cell",
            "--stage",
            "model",
        ],
        &["layout", "good.mmd", "-profile=cell", "-stage=model"],
        &["layout", "--profile=cell", "good.mmd", "--stage=model"],
        &[
            "layout", "-profile", "cell", "--stage", "model", "--", "good.mmd",
        ],
    ],
    &[
        &["layout", "--metrics", "--dump", "good.dump"],
        &["layout", "-metrics=true", "-dump=good.dump"],
        &["layout", "--metrics=1", "--dump=good.dump"],
        &["layout", "-dump", "good.dump", "--metrics"],
    ],
    &[
        &[
            "explain",
            "flowchart/unexpected-token",
            "--output-format",
            "json",
        ],
        &[
            "explain",
            "-output-format=json",
            "flowchart/unexpected-token",
        ],
        &[
            "explain",
            "--output-format=json",
            "--",
            "flowchart/unexpected-token",
        ],
    ],
];

const FAILURES: &[(&[&str], &str)] = &[
    (
        &["view", "good.mmd", "---t", "elegant-dark"],
        "unknown flag ---t; run emd view --help\n",
    ),
    (
        &["view", "good.mmd", "---script=ok.script"],
        "unknown flag ---script=ok.script; run emd view --help\n",
    ),
    (
        &["render", "good.mmd", "---width=5"],
        "unknown flag ---width=5; run emd render --help\n",
    ),
    (
        &["render", "good.mmd", "---e", "svg"],
        "unknown flag ---e; run emd render --help\n",
    ),
    (
        &["check", "good.mmd", "---color"],
        "unknown flag ---color; run emd check --help\n",
    ),
    (
        &["lint", "good.mmd", "---fix"],
        "unknown flag ---fix; run emd lint --help\n",
    ),
    (
        &["layout", "good.mmd", "---metrics"],
        "unknown flag ---metrics; run emd layout --help\n",
    ),
    (
        &[
            "explain",
            "flowchart/unexpected-token",
            "---output-format=json",
        ],
        "unknown flag ---output-format=json; run emd explain --help\n",
    ),
    (
        &["layout", "good.mmd", "-x"],
        "unknown flag -x; run emd layout --help\n",
    ),
    (&["view", "good.mmd", "--t"], "missing value for --t\n"),
    (
        &["view", "good.mmd", "-script"],
        "missing value for -script\n",
    ),
    (
        &["layout", "good.mmd", "-profile"],
        "missing value for -profile\n",
    ),
    (
        &["explain", "--output-format"],
        "missing value for --output-format\n",
    ),
    (
        &["view", "good.mmd", "--script="],
        "cannot read : no such file or directory\n",
    ),
    (
        &["view", "good.mmd", "--script", ""],
        "cannot read : no such file or directory\n",
    ),
    (
        &["lint", "good.mmd", "--fix=maybe"],
        "invalid value maybe for --fix; expected one of: true, false\n",
    ),
    (
        &["layout", "good.mmd", "-metrics=maybe"],
        "invalid value maybe for --metrics; expected one of: true, false\n",
    ),
    (
        &["layout", "good.mmd", "-profile=bogus"],
        "invalid value bogus for --profile; expected one of: vector, cell\n",
    ),
    (
        &["layout", "good.mmd", "--stage=bogus"],
        "invalid value bogus for --stage; expected one of: model, layout\n",
    ),
];

#[test]
fn flag_spellings() -> io::Result<()> {
    let scratch = Scratch::new()?;
    let root = scratch.0.as_path();
    fs::write(root.join("good.mmd"), "flowchart LR\n A[alpha] --> B\n")?;
    fs::write(root.join("ok.script"), "settle\n")?;
    let (dump, _, _) = run(root, &["layout", "good.mmd"])?;
    fs::write(root.join("good.dump"), dump)?;
    let mut failures = Vec::new();
    for group in SPELLINGS {
        let want = run(root, group[0])?;
        if want.2 != Some(0) || want.0.is_empty() {
            failures.push(format!("{:?}: {want:?}; want output and exit 0", group[0]));
        }
        for args in &group[1..] {
            let got = run(root, args)?;
            if got != want {
                failures.push(format!(
                    "{args:?}: {got:?}; want the result of {:?}",
                    group[0]
                ));
            }
        }
    }
    for (args, stderr) in FAILURES {
        let got = run(root, args)?;
        if got != (String::new(), (*stderr).to_owned(), Some(2)) {
            failures.push(format!(
                "{args:?}: {got:?}; want stderr {stderr:?} and exit 2"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}
