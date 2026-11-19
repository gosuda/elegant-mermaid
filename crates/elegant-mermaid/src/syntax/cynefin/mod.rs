//! Syntax of the `cynefin` kind: lexer terminals, grammar, and diagnostics of
//! `spec/grammar/cynefin.md`.

pub mod ast;
pub mod parser;

pub use parser::parse;

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests;

pub const DOMAIN_NAMES: [&str; 5] = ["complex", "complicated", "clear", "chaotic", "confusion"];

pub(crate) const C_UNEXPECTED: &str = "cynefin/unexpected-token";
pub(crate) const C_UNKNOWN: &str = "cynefin/unknown-statement";
pub(crate) const C_UNTERMINATED: &str = "cynefin/unterminated";
