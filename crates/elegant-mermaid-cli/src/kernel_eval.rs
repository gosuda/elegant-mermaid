use std::ffi::{OsStr, OsString};
use std::io::Read;
use std::path::Path;

use elegant_mermaid::geom::CaseError;

use crate::error::{InputError, UsageError};
use crate::input;

const USAGE: &str = "Usage: emd kernel-eval FILE\n";
const COMMAND: &str = "kernel-eval";

pub(crate) struct Failure {
    pub(crate) stdout: String,
    pub(crate) error: KernelError,
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum KernelError {
    #[error(transparent)]
    Usage(#[from] UsageError),
    #[error(transparent)]
    Input(#[from] InputError),
    #[error("bad case line {0}")]
    BadLine(usize),
}

impl From<KernelError> for Failure {
    fn from(error: KernelError) -> Self {
        Self {
            stdout: String::new(),
            error,
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
    match parse(args)? {
        Invocation::Help => Ok(USAGE.to_owned()),
        Invocation::Stdin => {
            let mut bytes = Vec::new();
            input.read_to_end(&mut bytes).map_err(|source| {
                KernelError::from(input::read_error(input::STDIN_LABEL, source))
            })?;
            evaluate(&bytes)
        }
        Invocation::File(path) => run_cases(path),
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
            return Err(UsageError::UnknownFlag {
                flag: text.into_owned(),
                command: COMMAND,
            }
            .into());
        }
        if file.is_some() {
            return Err(UsageError::ExtraInput { command: COMMAND }.into());
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
    let bytes = std::fs::read(Path::new(path))
        .map_err(|source| KernelError::from(input::read_error(&path.to_string_lossy(), source)))?;
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
            let result = eval_input(&args, &mut input)
                .map_err(|failure| (failure.stdout, failure.error.to_string()));
            assert!(
                matches!(&result, Ok(out) if out == "9\n2\n"),
                "stdin kernel cases must emit both results for {args:?}: {result:?}"
            );
            let mut bad = &b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\nbroken\n"[..];
            let result = eval_input(&args, &mut bad)
                .map_err(|failure| (failure.stdout, failure.error.to_string()));
            assert!(
                matches!(&result, Err((stdout, error))
                if stdout == "9\n2\n" && error == "bad case line 3"),
                "stdin broken third case must retain prior results for {args:?}: {result:?}"
            );
        }
    }

    #[test]
    fn file_form_and_extra_operand() -> std::io::Result<()> {
        let path = std::env::temp_dir().join(format!("kernel-eval-{}.txt", std::process::id()));
        std::fs::write(&path, b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\n")?;
        let args = [path.clone().into_os_string()];
        let result = eval_input(&args, &mut std::io::empty())
            .map_err(|failure| (failure.stdout, failure.error.to_string()));
        assert!(
            matches!(&result, Ok(out) if out == "9\n2\n"),
            "file kernel cases must emit both results for {args:?}: {result:?}"
        );
        std::fs::write(
            &path,
            b"isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\nbroken\n",
        )?;
        let result = eval_input(&args, &mut std::io::empty())
            .map_err(|failure| (failure.stdout, failure.error.to_string()));
        assert!(
            matches!(&result, Err((stdout, error))
            if stdout == "9\n2\n" && error == "bad case line 3"),
            "file broken third case must retain prior results for {args:?}: {result:?}"
        );
        std::fs::remove_file(path)?;
        let args = [OsString::from("a"), OsString::from("b")];
        let result = eval_input(&args, &mut std::io::empty())
            .map_err(|failure| (failure.stdout, failure.error.to_string()));
        assert!(
            matches!(&result, Err((stdout, error))
            if stdout.is_empty() && error == "kernel-eval accepts one INPUT"),
            "extra kernel operand must be rejected without output for {args:?}: {result:?}"
        );
        Ok(())
    }
}
