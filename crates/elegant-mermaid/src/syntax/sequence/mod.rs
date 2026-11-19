//! Syntax of the `sequence` kind: lexer modes, grammar, and diagnostics of
//! `spec/grammar/sequence.md`.

pub mod ast;
pub mod lexer;
pub mod parser;
mod quotes;

pub use parser::parse;

use crate::diag::{Diagnostic, Severity};

pub(crate) const C_NESTING: &str = "limit/nesting-depth";

pub(crate) const C_UNEXPECTED: &str = "sequence/unexpected-token";

pub(crate) const C_UNKNOWN: &str = "sequence/unknown-statement";

pub(crate) const C_UNTERMINATED: &str = "sequence/unterminated";

pub(crate) const C_QUOTE_UNCLOSED: &str = "sequence/quote-unclosed";

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
