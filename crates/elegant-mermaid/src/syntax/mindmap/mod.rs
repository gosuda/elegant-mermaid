//! Syntax of the `mindmap` kind: lexer modes, grammar, and diagnostics of
//! `spec/grammar/mindmap.md`.

pub mod ast;
mod lexer;
pub mod parser;

pub use parser::{Parsed, parse};

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_UNEXPECTED: &str = "mindmap/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "mindmap/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "mindmap/unterminated";

pub(crate) const C_SECOND_ROOT: &str = "mindmap/second-root";

pub(crate) const C_NO_TARGET: &str = "mindmap/decoration-target-missing";

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
