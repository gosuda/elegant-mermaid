use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::kanban::Model, source::Span};
use std::collections::BTreeSet;

pub(crate) fn no_columns(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.sections.is_empty() {
        vec![super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            Span { start: 0, end: 0 },
            Vec::new(),
        )]
    } else {
        Vec::new()
    }
}
pub(crate) fn empty_column(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let occupied: BTreeSet<_> = model.nodes.iter().filter_map(|node| node.parent).collect();
    model
        .sections
        .iter()
        .filter(|index| !occupied.contains(index))
        .filter_map(|index| model.nodes.get(*index))
        .map(|node| {
            super::common::row_diagnostic(row, row.summary.to_owned(), node.anchor, Vec::new())
        })
        .collect()
}
pub(crate) fn duplicate_column(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for node in &model.nodes {
        let duplicate = !seen.insert(node.id.as_str());
        if duplicate && node.is_section() {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                node.anchor,
                Vec::new(),
            ));
        }
    }
    out
}
pub(crate) fn duplicate_task_id(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for node in &model.nodes {
        let duplicate = !seen.insert(node.id.as_str());
        if duplicate && !node.is_section() {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                node.anchor,
                Vec::new(),
            ));
        }
    }
    out
}
#[cfg(test)]
#[path = "kanban_test.rs"]
mod tests;
