use super::xychart::*;
#[test]
fn missing_x_axis_trigger_and_clear() {
    for (i, source) in ["xychart\nbar [1]\n", "xychart\nx-axis [a]\nbar [1]\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "xychart/missing-x-axis");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = missing_x_axis(&model, row);
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
fn missing_y_axis_trigger_and_clear() {
    for (i, source) in ["xychart\nbar [1]\n", "xychart\ny-axis 0 --> 2\nbar [1]\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "xychart/missing-y-axis");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = missing_y_axis(&model, row);
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
fn no_series_trigger_and_clear() {
    for (i, source) in ["xychart\n", "xychart\nbar [1]\n"].iter().enumerate() {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "xychart/no-series");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = no_series(&model, row);
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
fn series_length_mismatch_trigger_and_clear() {
    for (i, source) in [
        "xychart\nx-axis [a, b]\nbar [1]\n",
        "xychart\nx-axis [a, b]\nbar [1, 2]\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "xychart/series-length-mismatch");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
            let ds = series_length_mismatch(&model, row);
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
fn effective_domain() {
    let row = crate::r#gen::lintrules::LINT_RULES
        .iter()
        .find(|row| row.code == "xychart/series-length-mismatch");
    assert!(row.is_some(), "missing registry row");
    let Some(row) = row else {
        return;
    };
    for (source, want) in [
        (
            "xychart\nx-axis [a, b]\nx-axis 0 --> 10\nbar [1]\nline [2]\n",
            0,
        ),
        (
            "xychart\nx-axis [a, b]\nx-axis 0 --> 10\nbar [1]\nline [2, 3]\n",
            1,
        ),
        ("xychart\nx-axis [a, b]\nx-axis \"title\"\nbar [1]\n", 1),
        ("xychart\nx-axis [a, b]\nbar [1, 2, 3]\n", 1),
        ("xychart\nbar [1]\nline [1, 2]\n", 1),
    ] {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::xychart::resolve(source, &parsed.document);
        assert_eq!(series_length_mismatch(&model, row).len(), want, "{source}");
    }
}

#[test]
fn empty_lists_are_rejected_before_lint() {
    for source in [
        "xychart\nx-axis []\nbar [1]\n",
        "xychart\nbar []\n",
        "xychart\nbar []\nline [1]\n",
    ] {
        let parsed = crate::syntax::xychart::parser::parse(source, &[]);
        assert!(
            parsed.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "xychart/unexpected-token"
                    && &source[diagnostic.span.start..diagnostic.span.end] == "]"
            }),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
}
