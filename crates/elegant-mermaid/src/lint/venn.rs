use crate::{diag::Diagnostic, r#gen::lintrules::LintRule, model::venn::Model};

pub(crate) fn run(model: &Model, row: &LintRule) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut sets = std::collections::BTreeSet::new();
    let mut unions = std::collections::BTreeSet::new();
    for declaration in &model.declarations {
        let ids = declaration
            .subset_index
            .map_or(declaration.rejected_ids.as_slice(), |index| {
                model.subsets[index].sets.as_slice()
            });
        let mut span = declaration.span;
        let mut hit = if declaration.union {
            let duplicate = !unions.insert(ids);
            (row.code == "venn/duplicate-union" && duplicate)
                || (row.code == "venn/self-union" && ids.windows(2).any(|pair| pair[0] == pair[1]))
        } else {
            let duplicate = !sets.insert(&ids[0]);
            row.code == "venn/duplicate-set" && duplicate
        };
        if row.code == "venn/non-positive-size"
            && let Some(size_span) = declaration.size_span
        {
            hit = declaration.non_positive;
            span = size_span;
        }
        if hit {
            out.push(super::common::row_diagnostic(
                row,
                row.summary.into(),
                span,
                Vec::new(),
            ));
        }
    }
    if row.code == "venn/single-set" && sets.len() == 1 {
        out.push(super::common::row_diagnostic(
            row,
            row.summary.into(),
            model.header_span,
            Vec::new(),
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn source_predicates() {
        let cases = [
            (
                "venn/duplicate-set",
                "venn-beta\nset A\nset A\n",
                "venn-beta\nset A\nset B\n",
            ),
            (
                "venn/non-positive-size",
                "venn-beta\nset A:0\n",
                "venn-beta\nset A:1\n",
            ),
            (
                "venn/single-set",
                "venn-beta\nset A\n",
                "venn-beta\nset A\nset B\n",
            ),
            (
                "venn/self-union",
                "venn-beta\nset A\nunion A,A\n",
                "venn-beta\nset A\nset B\nunion A,B\n",
            ),
            (
                "venn/duplicate-union",
                "venn-beta\nset A\nset B\nunion A,B\nunion B,A\n",
                "venn-beta\nset A\nset B\nunion A,B\n",
            ),
            (
                "venn/non-positive-size",
                "venn-beta\nset A:0.000\n",
                "venn-beta\nset A:0.0001\n",
            ),
            (
                "venn/non-positive-size",
                "venn-beta\nset A\nunion A,Z:0\n",
                "venn-beta\nset A\nunion A,Z\n",
            ),
            (
                "venn/duplicate-union",
                "venn-beta\nset A\nunion A,Z\nunion Z,A\n",
                "venn-beta\nset A\nunion A,A,Z\nunion A,Z\n",
            ),
        ];
        for (code, trigger, clean) in cases {
            for row in crate::r#gen::lintrules::LINT_RULES
                .iter()
                .filter(|r| r.code == code)
            {
                for (text, want) in [(trigger, 1), (clean, 0)] {
                    let parsed = crate::syntax::venn::parse(text, &[]);
                    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                    let (model, _) = crate::model::venn::resolve(text, &parsed.document);
                    let got = super::run(&model, row);
                    assert_eq!(got.len(), want, "{code}: {got:?}");
                    assert!(
                        got.iter().all(|d| d.code == code
                            && d.message == row.summary
                            && d.help == row.help)
                    );
                }
            }
        }
    }
}
