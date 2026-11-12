use std::ffi::{OsStr, OsString};
use std::io::Read;
use std::path::Path;

use elegant_mermaid::geom::CaseError;

const USAGE: &str = "Usage: emd kernel-eval FILE\n";

pub(crate) struct Failure {
    pub(crate) stdout: String,
    pub(crate) error: KernelError,
}

pub(crate) enum KernelError {
    UnknownToken(String),
    Unreadable { path: String, error: String },
    BadLine(usize),
}

impl KernelError {
    pub(crate) fn message(&self) -> String {
        match self {
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
    Stdin,
    File(&'a OsStr),
}

pub(crate) fn eval_file(args: &[OsString]) -> Result<String, Failure> {
    eval_input(args, &mut std::io::stdin().lock())
}

fn eval_input(args: &[OsString], input: &mut impl Read) -> Result<String, Failure> {
    match parse(args) {
        Ok(Invocation::Help) => Ok(USAGE.to_owned()),
        Ok(Invocation::Stdin) => {
            let mut bytes = Vec::new();
            input.read_to_end(&mut bytes).map_err(|error| Failure {
                stdout: String::new(),
                error: KernelError::Unreadable {
                    path: "-".to_owned(),
                    error: error.to_string(),
                },
            })?;
            evaluate(&bytes)
        }
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
        let flag = flags_open && text.starts_with('-') && text != "-";
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
    Ok(match file {
        None => Invocation::Stdin,
        Some(path) if path == "-" => Invocation::Stdin,
        Some(path) => Invocation::File(path),
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
    evaluate(&bytes)
}

fn evaluate(bytes: &[u8]) -> Result<String, Failure> {
    let mut out = String::new();
    match elegant_mermaid::geom::eval(&String::from_utf8_lossy(bytes), &mut out) {
        Ok(()) => Ok(out),
        Err(CaseError { line }) => Err(Failure {
            stdout: out,
            error: KernelError::BadLine(line),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stdin_forms_and_bad_lines() {
        for args in [vec![], vec![OsString::from("-")]] {
            let mut input = &b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\n"[..];
            assert!(matches!(eval_input(&args, &mut input), Ok(out) if out == "9\n2\n"));
            let mut bad = &b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\nbroken\n"[..];
            assert!(matches!(eval_input(&args, &mut bad), Err(failure)
                if failure.stdout == "9\n2\n" && failure.error.message() == "bad case line 3"));
        }
    }

    #[test]
    fn file_form_and_extra_operand() -> std::io::Result<()> {
        let path = std::env::temp_dir().join(format!("kernel-eval-{}.txt", std::process::id()));
        std::fs::write(&path, b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\n")?;
        let args = [path.clone().into_os_string()];
        assert!(matches!(eval_input(&args, &mut std::io::empty()), Ok(out) if out == "9\n2\n"));
        std::fs::write(
            &path,
            b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\nbroken\n",
        )?;
        assert!(
            matches!(eval_input(&args, &mut std::io::empty()), Err(failure)
            if failure.stdout == "9\n2\n" && failure.error.message() == "bad case line 3")
        );
        std::fs::remove_file(path)?;
        let args = [OsString::from("a"), OsString::from("b")];
        assert!(
            matches!(eval_input(&args, &mut std::io::empty()), Err(failure)
            if failure.stdout.is_empty() && failure.error.message() == "unknown flag b; run emd kernel-eval --help")
        );
        Ok(())
    }
}
