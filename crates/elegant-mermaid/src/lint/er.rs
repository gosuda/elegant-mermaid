use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::er::Model;
use std::collections::BTreeSet;

pub(crate) fn duplicate_attribute(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for declaration in &model.declarations {
        let mut names = BTreeSet::new();
        for attr in &model.entities[declaration.entity].attributes[declaration.attributes.clone()] {
            if !names.insert(attr.name.as_str()) {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    attr.name_span,
                    Vec::new(),
                ));
            }
        }
    }
    out
}

pub(crate) fn duplicate_entity(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = vec![false; model.entities.len()];
    for declaration in &model.declarations {
        if seen[declaration.entity] {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                declaration.name_span,
                Vec::new(),
            ));
        }
        seen[declaration.entity] = true;
    }
    out
}

pub(crate) fn standalone_entity(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut related = BTreeSet::new();
    for relationship in &model.relationships {
        related.insert(relationship.from.as_str());
        related.insert(relationship.to.as_str());
    }
    for declaration in &model.declarations {
        if !related.contains(model.entities[declaration.entity].id.as_str()) {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                declaration.name_span,
                Vec::new(),
            ));
        }
    }
    out
}

#[cfg(test)]
#[path = "er_tests.rs"]
mod tests;
