use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::gitgraph::Model;
use crate::source::Span;
use std::collections::BTreeMap;

pub(crate) fn duplicate_tag(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeMap::new();
    let mut out = Vec::new();
    for (index, commit) in model.commit_history.iter().enumerate() {
        for tag in &commit.tags {
            if seen
                .insert(tag.as_str(), index)
                .is_some_and(|prior| prior != index)
            {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    commit.span,
                    Vec::new(),
                ));
            }
        }
    }
    out
}

pub(crate) fn no_commits(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if model.commits.is_empty() {
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

#[cfg(test)]
#[path = "gitgraph_test.rs"]
mod tests;
