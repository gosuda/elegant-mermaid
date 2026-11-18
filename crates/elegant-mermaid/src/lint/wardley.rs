use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::wardley::Model};
use std::collections::BTreeSet;

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut names = BTreeSet::new();
    let used: BTreeSet<_> = model
        .references
        .iter()
        .chain(&model.pipeline_uses)
        .map(|r| model.reference_name(r))
        .collect();
    let mut scale = 0;
    for declaration in &model.declarations {
        let name = model.nodes[declaration.node].id.as_str();
        let duplicate = !names.insert(name);
        if (duplicate && row.code == "wardley/duplicate-component")
            || (!used.contains(name) && row.code == "wardley/orphan-component")
        {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                declaration.span,
                Vec::new(),
            ));
        }
        scale |= declaration.scale;
    }
    if row.code == "wardley/undefined-component" {
        for reference in model
            .references
            .iter()
            .filter(|r| !names.contains(model.reference_name(r)))
        {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.to_owned(),
                reference.span,
                Vec::new(),
            ));
        }
    }
    if (row.code == "wardley/no-components" && names.is_empty())
        || (row.code == "wardley/mixed-coordinate-scale" && scale == 3)
    {
        out.push(super::common::row_diagnostic(
            row,
            row.summary.to_owned(),
            model.header,
            Vec::new(),
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn undefined_references_keep_link_then_evolve_spans() -> Result<(), &'static str> {
        let source = "wardley-beta\nevolve Gone 0.5\nMissing -> Other\n";
        let parsed = crate::syntax::wardley::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::wardley::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "wardley/undefined-component")
            .ok_or("registered rule")?;
        let diagnostics = super::run(&model, row);
        let names: Vec<_> = diagnostics
            .iter()
            .map(|d| &source[d.span.start..d.span.end])
            .collect();
        assert_eq!(names, ["Missing", "Other", "Gone"]);
        Ok(())
    }

    #[test]
    fn wardley_rules() -> Result<(), &'static str> {
        let cases = [
            (
                "wardley/undefined-component",
                "component A [0.2, 0.3]\nA -> Missing",
                "component A [0.2, 0.3]\ncomponent B [0.4, 0.5]\nA -> B",
            ),
            (
                "wardley/orphan-component",
                "component A [0.2, 0.3]",
                "component A [0.2, 0.3]\nevolve A 0.5",
            ),
            (
                "wardley/no-components",
                "title Empty",
                "component A [0.2, 0.3]",
            ),
            (
                "wardley/mixed-coordinate-scale",
                "component A [0.2, 30.0]",
                "component A [20.0, 30.0]",
            ),
            (
                "wardley/duplicate-component",
                "component A [0.2, 0.3]\ncomponent A [0.4, 0.5]",
                "component A [0.2, 0.3]\ncomponent B [0.4, 0.5]",
            ),
            (
                "wardley/mixed-coordinate-scale",
                "component A [0.2, 30.0]\ncomponent A [20.0, 30.0]",
                "component A [0.0, 30.0]",
            ),
            (
                "wardley/undefined-component",
                "evolve Missing 0.5",
                "component A [0.2, 0.3]\nevolve A 0.5",
            ),
        ];
        for (code, bad, good) in cases {
            for (body, expected) in [(bad, true), (good, false)] {
                let source = format!("wardley-beta\n{body}\n");
                let parsed = crate::syntax::wardley::parse(&source, &[]);
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                let (model, _) = crate::model::wardley::resolve(&source, &parsed.document);
                let row = crate::r#gen::lintrules::LINT_RULES
                    .iter()
                    .find(|r| r.code == code)
                    .ok_or("registered rule")?;
                assert_eq!(
                    super::run(&model, row).iter().any(|d| d.code == code),
                    expected,
                    "{code}: {body}"
                );
            }
        }
        Ok(())
    }
}
