use std::ffi::{OsStr, OsString};
use std::path::Path;

use elegant_mermaid::geom::CaseError;

const USAGE: &str = "Usage: emd kernel-eval FILE\n";

pub(crate) struct Failure {
    pub(crate) stdout: String,
    pub(crate) error: KernelError,
}

pub(crate) enum KernelError {
    MissingFile,
    UnknownToken(String),
    Unreadable { path: String, error: String },
    BadLine(usize),
}

impl KernelError {
    pub(crate) fn message(&self) -> String {
        match self {
            KernelError::MissingFile => "missing FILE; pass a kernel case file path".to_owned(),
            KernelError::UnknownToken(token) => {
                format!("unknown flag {token}; run emd kernel-eval --help")
            }
            KernelError::Unreadable { path, error } => format!("cannot read {path}: {error}"),
            KernelError::BadLine(line) => format!("bad case line {line}"),
        }
    }
}

enum Invocation<'a> {
    Help,
    File(&'a OsStr),
}

pub(crate) fn eval_file(args: &[OsString]) -> Result<String, Failure> {
    match parse(args) {
        Ok(Invocation::Help) => Ok(USAGE.to_owned()),
        Ok(Invocation::File(path)) => run_cases(path),
        Err(error) => Err(Failure {
            stdout: String::new(),
            error,
        }),
    }
}

fn parse(args: &[OsString]) -> Result<Invocation<'_>, KernelError> {
    let mut file: Option<&OsStr> = None;
    let mut flags_open = true;
    for arg in args {
        let text = arg.to_string_lossy();
        let flag = flags_open && text.starts_with('-');
        if flag && text == "--" {
            flags_open = false;
            continue;
        }
        if flag && (text == "-h" || text == "--help") {
            return Ok(Invocation::Help);
        }
        if flag {
            return Err(KernelError::UnknownToken(text.into_owned()));
        }
        if file.is_some() {
            return Err(KernelError::UnknownToken(text.into_owned()));
        }
        file = Some(arg.as_os_str());
    }
    file.map_or(Err(KernelError::MissingFile), |path| {
        Ok(Invocation::File(path))
    })
}

fn run_cases(path: &OsStr) -> Result<String, Failure> {
    let bytes = std::fs::read(Path::new(path)).map_err(|error| Failure {
        stdout: String::new(),
        error: KernelError::Unreadable {
            path: path.to_string_lossy().into_owned(),
            error: error.to_string(),
        },
    })?;
    let mut out = String::new();
    match elegant_mermaid::geom::eval(&String::from_utf8_lossy(&bytes), &mut out) {
        Ok(()) => Ok(out),
        Err(CaseError { line }) => Err(Failure {
            stdout: out,
            error: KernelError::BadLine(line),
        }),
    }
}
