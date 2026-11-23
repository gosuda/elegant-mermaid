mod config;
mod flags;
mod rewrite;
#[cfg(test)]
mod tests;

use crate::error::CliError;
use crate::view::Environment;
use crate::{check, input, options, report};
use config::Resolver;
use elegant_mermaid::{
    DiagramKind, FixSafety, LintConfig, Severity, apply_fixes, apply_host_fixes, diag,
    lint_document, lint_host, options::FixOutcome,
};
use flags::Flags;
use std::io::IsTerminal;
use std::path::Path;

const STDIN: &str = "-";

/// What one `lint` run prints and how it exits.
struct Outcome {
    stdout: String,
    stderr: String,
    code: i32,
}

struct Linted {
    path: String,
    kind: Option<DiagramKind>,
    source: String,
    diagnostics: Vec<diag::Diagnostic>,
}

pub fn run(args: &[String], environment: &Environment) -> (String, String, i32) {
    match lint_command(args, environment) {
        Ok(outcome) => (outcome.stdout, outcome.stderr, outcome.code),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}

fn lint_command(args: &[String], environment: &Environment) -> Result<Outcome, CliError> {
    let (flags, paths) = flags::parse(args)?;
    flags::validate(&flags, &paths)?;
    let inputs = check::collect(&paths)?;
    if inputs.is_empty() {
        return Ok(Outcome {
            stdout: String::new(),
            stderr: "no Mermaid files found in .\n".into(),
            code: 0,
        });
    }
    let mut resolver = Resolver::new(&flags);
    let mut files = Vec::new();
    let mut fixed_stdin = None;
    for path in &inputs {
        let mut bytes = input::read(path)?;
        let config = resolver.for_input(path)?;
        let shown = if path == STDIN { "<stdin>" } else { path };
        if flags.fix {
            let outcome = fix_source(shown, &bytes, &config, fix_limit(&flags));
            store_fixed(path, &outcome, &mut fixed_stdin)?;
            bytes = outcome.text.into_bytes();
        }
        files.push(lint_file(shown, &bytes, &config));
    }
    let code = i32::from(files.iter().any(|file| fails(&flags, file)));
    Ok(match fixed_stdin {
        Some(text) => Outcome {
            stdout: text,
            stderr: render(&files, "text", stderr_colour(&flags.color)),
            code,
        },
        None => Outcome {
            stdout: render(
                &files,
                &flags.format,
                options::colour(&flags.color, environment),
            ),
            stderr: String::new(),
            code,
        },
    })
}

/// A file fails the run with an error diagnostic, or with a warning under
/// `--deny-warnings`.
fn fails(flags: &Flags, file: &Linted) -> bool {
    file.diagnostics.iter().any(|d| {
        d.severity == Severity::Error || (flags.deny_warnings && d.severity == Severity::Warning)
    })
}

fn fix_limit(flags: &Flags) -> FixSafety {
    if flags.unsafe_fixes {
        FixSafety::Unsafe
    } else {
        FixSafety::Safe
    }
}

fn store_fixed(
    path: &str,
    outcome: &FixOutcome,
    fixed_stdin: &mut Option<String>,
) -> Result<(), CliError> {
    if path == STDIN {
        *fixed_stdin = Some(outcome.text.clone());
        return Ok(());
    }
    if outcome.applied > 0 {
        rewrite::rewrite_file(path, outcome.text.as_bytes())?;
    }
    Ok(())
}

fn lint_file(path: &str, bytes: &[u8], config: &LintConfig) -> Linted {
    if check::markdown_host(Path::new(path)) {
        let report = lint_host(bytes, config);
        return Linted {
            path: path.to_owned(),
            kind: None,
            source: report.source,
            diagnostics: report.diagnostics,
        };
    }
    let document = elegant_mermaid::parse_bytes(bytes);
    Linted {
        path: path.to_owned(),
        kind: document.kind(),
        source: document.source().to_owned(),
        diagnostics: lint_document(&document, config),
    }
}

fn fix_source(path: &str, bytes: &[u8], config: &LintConfig, limit: FixSafety) -> FixOutcome {
    if check::markdown_host(Path::new(path)) {
        apply_host_fixes(bytes, config, limit)
    } else {
        apply_fixes(bytes, config, limit)
    }
}

/// `--color auto` for the diagnostics that `--fix -` sends to stderr.
fn stderr_colour(mode: &str) -> bool {
    options::colour_enabled(mode, std::io::stderr().is_terminal(), |name| {
        std::env::var(name).unwrap_or_default()
    })
}

fn render(files: &[Linted], format: &str, colour: bool) -> String {
    let reports: Vec<report::File<'_>> = files
        .iter()
        .map(|file| report::File {
            path: &file.path,
            kind: file.kind.map(DiagramKind::id),
            source: &file.source,
            diagnostics: &file.diagnostics,
        })
        .collect();
    match format {
        "json" => report::json(&reports),
        "sarif" => report::sarif(&reports),
        "github" => report::github(&reports),
        _ => report::text(&reports, colour),
    }
}
