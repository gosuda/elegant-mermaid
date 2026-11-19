//! Syntax of the `kanban` kind: lexer modes, grammar, and diagnostics of
//! `spec/grammar/kanban.md`.

pub mod ast;
mod lexer;
pub mod parser;

pub use parser::{Parsed, parse};

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "kanban/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "kanban/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "kanban/unterminated";

pub(crate) fn diagnostic(
    code: &'static str,
    message: String,
    span: crate::source::Span,
) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span,
        related: Vec::new(),
        help: crate::r#gen::diagnostics::DIAGNOSTICS
            .iter()
            .find(|row| row.code == code)
            .map_or("", |row| row.help)
            .into(),
        fixes: Vec::new(),
    }
}

#[cfg(test)]
mod tests;
