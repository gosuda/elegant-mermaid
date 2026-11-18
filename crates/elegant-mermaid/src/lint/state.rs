use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::state::{Model, StatementOccurrence};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk(&model.occurrences, row, &mut out);
    out
}

fn walk(statements: &[StatementOccurrence], row: &LintRule, out: &mut Vec<Diagnostic>) {
    let mut ids = BTreeSet::new();
    let mut transitions = BTreeSet::new();
    for s in statements {
        if let Some(body) = &s.body {
            if s.statement_count == 0 && row.code == "state/empty-composite" {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    s.span,
                    Vec::new(),
                ));
            }
            walk(body, row, out);
        }
        if s.id != 0 && !ids.insert(s.id) && row.code == "state/duplicate-state" {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                s.span,
                Vec::new(),
            ));
        }
        if s.from == 0 {
            continue;
        }
        let duplicate = !transitions.insert((s.from, s.to, s.label));
        if row.code == "state/duplicate-transition" && duplicate
            || row.code == "state/self-transition" && s.from == s.to && !s.pseudostate
        {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                s.span,
                Vec::new(),
            ));
        }
    }
}
#[cfg(test)]
#[path = "state_tests.rs"]
mod tests;
