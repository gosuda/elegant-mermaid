//! The `flowchart` kind: its lexer, its tree, and its parser.
//!
//! The normative text is `spec/grammar/flowchart.md`.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod tokens;

#[cfg(test)]
mod tests;

use crate::diag::{Diagnostic, Severity};
use crate::source::Span;

/// Builds a diagnostic with the help text of the registry row, if the row has one.
pub(crate) fn diagnostic(
    code: &'static str,
    severity: Severity,
    message: String,
    span: Span,
) -> Diagnostic {
    Diagnostic {
        code,
        severity,
        message,
        span,
        related: Vec::new(),
        help: crate::syntax::flowchart::help_text(code),
        fixes: Vec::new(),
    }
}

fn help_text(code: &str) -> String {
    let row = crate::r#gen::diagnostics::DIAGNOSTICS
        .iter()
        .find(|row| row.code == code)
        .map(|row| row.help)
        .or_else(|| {
            crate::r#gen::lintrules::LINT_RULES
                .iter()
                .find(|row| row.code == code)
                .map(|row| row.help)
        });
    row.unwrap_or("").to_owned()
}

/// Parses `src`, skipping the removed spans that preprocessing found.
pub fn parse(src: &str, removed: &[Span]) -> parser::Parsed {
    parser::parse(src, removed)
}
