use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::sequence::{Event, Model};
use crate::source::Span;
use std::collections::BTreeSet;

pub(crate) fn duplicate_participant(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for declaration in &model.declarations {
        if !seen.insert(declaration.id.as_str()) {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                declaration.span,
                Vec::new(),
            ));
        }
    }
    out
}

pub(crate) fn prefer_explicit_participants(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut seen = vec![false; model.actors.len()];
    let mut out = Vec::new();
    for event in &model.events {
        let Event::Message(message) = event else {
            continue;
        };
        for index in [message.from, message.to] {
            if seen[index] {
                continue;
            }
            seen[index] = true;
            let actor = &model.actors[index];
            let declared = model.declarations.iter().any(|declaration| {
                declaration.id == actor.id && declaration.span.start < message.span.start
            });
            if !declared {
                out.push(super::common::row_diagnostic(
                    row,
                    row.summary.to_owned(),
                    actor.span,
                    Vec::new(),
                ));
            }
        }
    }
    out
}

pub(crate) fn no_activate_without_deactivate(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut stacks: Vec<Vec<Span>> = vec![Vec::new(); model.actors.len()];
    let mut spans = Vec::new();
    for activation in &model.activation_history {
        let stack = &mut stacks[activation.actor];
        if activation.open {
            stack.push(activation.span);
        } else if stack.pop().is_none() {
            spans.push(activation.span);
        }
    }
    for stack in stacks {
        spans.extend(stack);
    }
    spans.sort_by_key(|span| span.start);
    spans
        .into_iter()
        .map(|span| super::common::row_diagnostic(row, row.summary.to_owned(), span, Vec::new()))
        .collect()
}

#[cfg(test)]
#[path = "sequence_test.rs"]
mod tests;
