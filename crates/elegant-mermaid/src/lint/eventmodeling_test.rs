use super::eventmodeling::*;
#[test]
fn undefined_frame_trigger_and_clear() {
    for (i, source) in [
        "eventmodeling\ntf 1 cmd A ->> 9\n",
        "eventmodeling\ntf 9 ui A\ntf 1 cmd B ->> 9\n",
        "eventmodeling\ntf 1 cmd B ->> 9\ntf 9 ui A\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::eventmodeling::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "eventmodeling/undefined-frame");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let (model, _) = crate::model::eventmodeling::resolve(&parsed.document);
            let ds = undefined_frame(&model, row);
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
fn invalid_flow_trigger_and_clear() {
    for (i, source) in [
        "eventmodeling\ntf 1 evt A\ntf 2 cmd B ->> 1\n",
        "eventmodeling\ntf 1 ui A\ntf 2 cmd B ->> 1\n",
        "eventmodeling\ntf 1 cmd B ->> 9\n",
        "eventmodeling\ntf 1 evt A\ntf 2 cmd B\n",
        "eventmodeling\ntf 1 cmd B ->> 9\ntf 9 ui A\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::eventmodeling::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "eventmodeling/invalid-flow");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let (model, _) = crate::model::eventmodeling::resolve(&parsed.document);
            let ds = invalid_flow(&model, row);
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
fn duplicate_frames_are_required_public_errors() -> Result<(), &'static str> {
    let code = "eventmodeling/duplicate-frame-id";
    for directive in [
        "",
        "%% emd-disable-diagram eventmodeling/duplicate-frame-id: test\n",
    ] {
        let source =
            format!("eventmodeling\n{directive}tf 01 ui A\nrf 01 cmd B\ntf 1 evt C\ntf 01 evt D\n");
        let document = crate::parse(&source);
        assert!(document.has_errors());
        let findings: Vec<_> = document
            .diagnostics()
            .iter()
            .filter(|finding| finding.code == code)
            .collect();
        assert_eq!(findings.len(), 2);
        let first = source.find("tf 01").ok_or("first frame")? + 3;
        for (finding, start) in findings.iter().zip([
            source.find("rf 01").ok_or("second frame")? + 3,
            source.rfind("tf 01").ok_or("last frame")? + 3,
        ]) {
            assert_eq!(finding.severity, crate::Severity::Error);
            assert_eq!(
                finding.span,
                crate::source::Span {
                    start,
                    end: start + 2
                }
            );
            assert_eq!(finding.related.len(), 1);
            assert_eq!(
                finding.related[0].span,
                crate::source::Span {
                    start: first,
                    end: first + 2
                }
            );
            assert_eq!(finding.related[0].message, "first declared here");
        }
        for config in [
            crate::LintConfig::default(),
            crate::LintConfig {
                select: vec![code.into()],
                ..Default::default()
            },
            crate::LintConfig {
                ignore: vec![code.into()],
                off: vec![code.into()],
                severity: [(code.into(), crate::Severity::Warning)].into(),
                ..Default::default()
            },
        ] {
            let lint = crate::lint(&document, &config);
            assert!(!lint.iter().any(|finding| finding.code == code));
            let diagnostics = crate::lint_document(&document, &config);
            let errors: Vec<_> = diagnostics
                .iter()
                .filter(|finding| finding.code == code)
                .collect();
            assert_eq!(errors.len(), 2);
            assert!(
                errors
                    .iter()
                    .all(|finding| finding.severity == crate::Severity::Error)
            );
        }
    }
    let control = crate::parse("eventmodeling\ntf 01 ui A\ntf 1 cmd B\n");
    assert!(!control.has_errors(), "{:?}", control.diagnostics());
    Ok(())
}
