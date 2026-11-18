use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::mindmap::Model;
use crate::source::Span;
use std::collections::BTreeSet;

pub(crate) fn duplicate_sibling(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for node in &model.nodes {
        if !seen.insert((node.parent, node.label.as_str())) && node.parent.is_some() {
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

pub(crate) fn no_nodes(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.nodes.is_empty() {
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

pub(crate) fn deep_nesting(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for node in &model.nodes {
        let mut depth = 1;
        let mut parent = node.parent;
        while let Some(ancestor) = parent.and_then(|index| model.nodes.get(index)) {
            depth += 1;
            parent = ancestor.parent;
            if depth > model.nodes.len() {
                break;
            }
        }
        if depth > 5 {
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
#[path = "mindmap_test.rs"]
mod tests;
