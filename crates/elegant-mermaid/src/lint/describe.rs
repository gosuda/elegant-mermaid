//! Registry lookup for `emd explain` and for validating rule codes named by
//! flags and `emd.json`.

use super::ConfigError;
use crate::r#gen::diagnostics::DIAGNOSTICS;
use crate::r#gen::lintrules::{LINT_RULES, LintRule};

/// One registry row of a diagnostic code or a lint rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Described {
    pub code: &'static str,
    pub severity: &'static str,
    pub summary: &'static str,
    pub help: &'static str,
    pub rationale: &'static str,
    pub fix_safety: &'static str,
}

/// Returns the registry row of `code`. An alias gives the row of its current
/// code. A lint row wins over a syntax row of the same code.
pub fn describe(code: &str) -> Option<Described> {
    let canonical = canonical_code(code)?;
    if let Some(rule) = LINT_RULES.iter().find(|rule| rule.code == canonical) {
        return Some(from_rule(rule));
    }
    DIAGNOSTICS
        .iter()
        .find(|row| row.code == canonical)
        .map(|row| Described {
            code: row.code,
            severity: row.severity,
            summary: row.summary,
            help: row.help,
            rationale: row.rationale,
            fix_safety: row.fix_safety,
        })
}

/// Fails with `ConfigError::UnknownCode` for the first code of `codes` that
/// no registry row or alias names.
pub fn validate_codes(codes: &[String]) -> Result<(), ConfigError> {
    for code in codes {
        if canonical_code(code).is_none() {
            return Err(ConfigError::UnknownCode { code: code.clone() });
        }
    }
    Ok(())
}

/// Resolves a code or an alias to its current code. Every row's own code wins
/// over an alias of another row; among aliases the first row in registry
/// order (lint rules, then syntax rows) wins.
pub(crate) fn canonical_code(code: &str) -> Option<&'static str> {
    if let Some(rule) = LINT_RULES.iter().find(|rule| rule.code == code) {
        return Some(rule.code);
    }
    if let Some(row) = DIAGNOSTICS.iter().find(|row| row.code == code) {
        return Some(row.code);
    }
    LINT_RULES
        .iter()
        .find(|rule| rule.aliases.contains(&code))
        .map(|rule| rule.code)
        .or_else(|| {
            DIAGNOSTICS
                .iter()
                .find(|row| row.aliases.contains(&code))
                .map(|row| row.code)
        })
}

/// Whether a directive may name the code: not a `meta/*` row, not a syntax
/// error, and not an error row seeded from maid.
pub(crate) fn suppressible(canonical: &str) -> bool {
    if canonical.starts_with("meta/") {
        return false;
    }
    let syntax_error = DIAGNOSTICS
        .iter()
        .any(|row| row.code == canonical && row.severity == "error");
    if syntax_error {
        return false;
    }
    LINT_RULES
        .iter()
        .find(|rule| rule.code == canonical)
        .is_none_or(|rule| rule.severity != "error" || !rule.source.starts_with("maid:"))
}

fn from_rule(rule: &LintRule) -> Described {
    Described {
        code: rule.code,
        severity: rule.severity,
        summary: rule.summary,
        help: rule.help,
        rationale: rule.rationale,
        fix_safety: rule.fix_safety,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn describes_a_lint_rule_and_a_syntax_row() {
        let rule = describe("flowchart/duplicate-ids");
        assert_eq!(rule.map(|row| row.severity), Some("error"));
        let syntax = describe("agentflow/unterminated");
        assert_eq!(syntax.map(|row| row.help), Some(""));
    }

    #[test]
    fn an_alias_describes_its_current_code() {
        let row = describe("flowchart/node-unclosed-bracket");
        assert_eq!(
            row.map(|row| row.code),
            Some("flowchart/unclosed-node-bracket")
        );
    }

    #[test]
    fn unknown_codes_are_rejected_in_order() {
        let codes = ["flowchart/duplicate-ids", "bogus", "nope"].map(String::from);
        let error = validate_codes(&codes).err();
        assert!(matches!(error, Some(ConfigError::UnknownCode { ref code }) if code == "bogus"));
        assert!(validate_codes(&[]).is_ok());
    }
}
