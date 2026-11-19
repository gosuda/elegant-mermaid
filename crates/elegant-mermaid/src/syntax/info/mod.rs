//! Syntax of the `info` kind: lexer keywords, grammar, and diagnostics of
//! `spec/grammar/info.md`.

pub mod ast;
pub mod parser;

pub use parser::parse;

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests;

pub(crate) const C_UNEXPECTED: &str = "info/unexpected-token";
pub(crate) const C_UNKNOWN: &str = "info/unknown-statement";
pub(crate) const C_UNTERMINATED: &str = "info/unterminated";
