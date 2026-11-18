use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::ishikawa::Model};
use std::collections::BTreeSet;

pub(crate) fn no_causes(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.nodes.len() == 1 {
        vec![super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.nodes[0].span,
            Vec::new(),
        )]
    } else {
        Vec::new()
    }
}
pub(crate) fn empty_category(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .nodes
        .iter()
        .filter(|node| node.depth == 1 && node.children.is_empty())
        .map(|node| {
            super::common::row_diagnostic(row, row.summary.to_owned(), node.span, Vec::new())
        })
        .collect()
}
pub(crate) fn deep_nesting(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    model
        .nodes
        .iter()
        .filter(|node| node.depth >= 5)
        .map(|node| {
            super::common::row_diagnostic(row, row.summary.to_owned(), node.span, Vec::new())
        })
        .collect()
}
pub(crate) fn duplicate_sibling(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for node in &model.nodes {
        if node.parent.is_some() && !seen.insert((node.parent, node.label.as_str())) {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                node.span,
                Vec::new(),
            ));
        }
    }
    out
}
#[cfg(test)]
#[path = "ishikawa_test.rs"]
mod tests;
