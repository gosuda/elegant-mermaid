use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::quadrant::Model};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    match row.code {
        "quadrant/duplicate-point" => {
            let mut names = BTreeSet::new();
            for point in &model.points {
                if !names.insert(point.label_key.as_str()) {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        point.label_span,
                        Vec::new(),
                    ));
                }
            }
        }
        "quadrant/duplicate-quadrant" => {
            let mut regions = BTreeSet::new();
            for declaration in &model.quadrant_declarations {
                if !regions.insert(declaration.number) {
                    out.push(super::common::row_diagnostic(
                        row,
                        row.summary.to_owned(),
                        declaration.span,
                        Vec::new(),
                    ));
                }
            }
        }
        _ => {}
    }
    let points = !model.points.is_empty();
    if (row.code == "quadrant/no-points"
        && !points
        && (model.has_x_axis || model.has_y_axis || !model.quadrant_declarations.is_empty()))
        || (row.code == "quadrant/missing-x-axis" && points && !model.has_x_axis)
        || (row.code == "quadrant/missing-y-axis" && points && !model.has_y_axis)
    {
        out.push(super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.header_span,
            Vec::new(),
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn quadrant_rules() -> Result<(), &'static str> {
        let cases = [
            (
                "quadrant/duplicate-point",
                "A: [0.2, 0.3]\nA: [0.4, 0.5]",
                "A: [0.2, 0.3]\nB: [0.4, 0.5]",
            ),
            (
                "quadrant/no-points",
                "quadrant-1 Good",
                "quadrant-1 Good\nA: [0.2, 0.3]",
            ),
            (
                "quadrant/missing-x-axis",
                "A: [0.2, 0.3]",
                "x-axis Low --> High\nA: [0.2, 0.3]",
            ),
            (
                "quadrant/missing-y-axis",
                "A: [0.2, 0.3]",
                "y-axis Low --> High\nA: [0.2, 0.3]",
            ),
            (
                "quadrant/duplicate-quadrant",
                "quadrant-1 Good\nquadrant-1 Better",
                "quadrant-1 Good\nquadrant-2 Better",
            ),
            ("quadrant/no-points", "x-axis Low", "title Only title"),
            ("quadrant/no-points", "y-axis Low", ""),
        ];
        for (code, bad, good) in cases {
            for (body, expected) in [(bad, true), (good, false)] {
                let source = format!("quadrantChart\n{body}\n");
                let removed = crate::syntax::preprocess::preprocess(&source).removed;
                let document = crate::syntax::quadrant::parse(&source, &removed);
                assert!(
                    document.diagnostics.is_empty(),
                    "{source}: {:?}",
                    document.diagnostics
                );
                let (model, diagnostics) =
                    crate::model::quadrant::resolve(&source, &document.document);
                assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
                let row = crate::r#gen::lintrules::LINT_RULES
                    .iter()
                    .find(|row| row.code == code)
                    .ok_or("registered quadrant rule")?;
                assert_eq!(
                    super::run(&model, row).iter().any(|d| d.code == code),
                    expected,
                    "{code}: {body}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn duplicate_point_spans_follow_source_order() -> Result<(), &'static str> {
        let source = "quadrantChart\nA: [0.2, 0.3]\nA: [0.4, 0.5]\nA: [0.6, 0.7]\n";
        let removed = crate::syntax::preprocess::preprocess(source).removed;
        let parsed = crate::syntax::quadrant::parse(source, &removed);
        assert!(parsed.diagnostics.is_empty());
        let (model, diagnostics) = crate::model::quadrant::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|row| row.code == "quadrant/duplicate-point")
            .ok_or("registered rule")?;
        let spans: Vec<_> = super::run(&model, row)
            .into_iter()
            .map(|d| d.span)
            .collect();
        assert_eq!(
            spans,
            vec![
                crate::source::Span { start: 28, end: 29 },
                crate::source::Span { start: 42, end: 43 }
            ]
        );
        Ok(())
    }
}
