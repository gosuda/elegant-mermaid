use super::radar::*;
#[test]
fn no_curves_trigger_and_clear() {
    for (i, source) in ["radar-beta\naxis A\n", "radar-beta\naxis A\ncurve c {1}\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::radar::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::radar::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "radar/no-curves");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = no_curves(&model, row);
            assert_eq!(ds.len(), usize::from(i == 0));
            for d in ds {
                assert_eq!(d.code, row.code);
                assert_eq!(d.message, row.summary);
                assert_eq!(d.help, row.help);
                assert!(d.span.start <= d.span.end && d.span.end <= source.len());
            }
        }
    }
}
#[test]
fn curve_length_mismatch_trigger_and_clear() {
    for (i, source) in [
        "radar-beta\naxis A, B\ncurve c {1}\n",
        "radar-beta\naxis A, B\ncurve c {1, 2}\n",
        "radar-beta\naxis A, B\ncurve c {A: 1}\n",
        "radar-beta\naxis A, B\ncurve c {1, 2, 3}\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::radar::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::radar::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "radar/curve-length-mismatch");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = curve_length_mismatch(&model, row);
            assert_eq!(ds.len(), usize::from(i == 0 || i == 3));
            for d in ds {
                assert_eq!(d.code, row.code);
                assert_eq!(d.message, row.summary);
                assert_eq!(d.help, row.help);
                assert!(d.span.start <= d.span.end && d.span.end <= source.len());
            }
        }
    }
}
#[test]
fn duplicate_axis_trigger_and_clear() {
    for (i, source) in [
        "radar-beta\naxis A[\"same\"], B[\"same\"]\n",
        "radar-beta\naxis A, B\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::radar::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::radar::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "radar/duplicate-axis");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = duplicate_axis(&model, row);
            assert_eq!(ds.len(), usize::from(i == 0));
            for d in ds {
                assert_eq!(d.code, row.code);
                assert_eq!(d.message, row.summary);
                assert_eq!(d.help, row.help);
                assert!(d.span.start <= d.span.end && d.span.end <= source.len());
            }
        }
    }
}
