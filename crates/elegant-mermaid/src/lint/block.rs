use crate::diag::Diagnostic;
use crate::r#gen::lintrules::LintRule;
use crate::model::block::Model;
use crate::source::Span;

pub(crate) fn no_blocks(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    if !model
        .root
        .children
        .iter()
        .any(|child| child.kind != "space")
    {
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
#[path = "block_test.rs"]
mod tests;
