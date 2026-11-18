use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::treeview::Model, source::Span};
use std::collections::BTreeSet;

pub(crate) fn no_nodes(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.nodes.len() <= 1 {
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
pub(crate) fn duplicate_sibling(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for node in &model.nodes {
        if node.parent.is_some() && !seen.insert((node.parent, node.name.as_str())) {
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
#[path = "treeview_test.rs"]
mod tests;
