use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::c4::{Declaration, Model, Usage};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut names = BTreeSet::new();
    let mut out = Vec::new();
    for occurrence in &model.aliases {
        let id = match occurrence.declaration {
            Declaration::Element(index) => model.elements[index].id.as_str(),
            Declaration::Boundary(index) => model.boundaries[index].id.as_str(),
        };
        if !names.insert(id) && row.code == "c4/duplicate-id" {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                occurrence.span,
                Vec::new(),
            ));
        }
    }
    for usage in &model.usages {
        let endpoints = match (usage, row.code) {
            (Usage::Relation { index, from, to }, "c4/undefined-relationship-endpoint") => {
                let relation = &model.relations[*index];
                [
                    Some((relation.from.value.as_str(), *from)),
                    Some((relation.to.value.as_str(), *to)),
                ]
            }
            (Usage::ElementStyle(target), "c4/undefined-element-style") => {
                [Some((target.value.as_str(), target.span)), None]
            }
            (Usage::RelationStyle(from, to), "c4/undefined-relationship-style-endpoint") => [
                Some((from.value.as_str(), from.span)),
                Some((to.value.as_str(), to.span)),
            ],
            _ => [None, None],
        };
        for (value, span) in endpoints.into_iter().flatten() {
            if !names.contains(value) {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    span,
                    Vec::new(),
                ));
            }
        }
    }
    out
}

#[cfg(test)]
#[path = "c4_tests.rs"]
mod tests;
