use super::timeline::*;
use crate::source::Span;
#[test]
fn no_entries_trigger_and_clear() {
    for (i, source) in ["timeline\n", "timeline\n2020 : event\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::timeline::parser::parse(source, &[]);
        let (model, _) = crate::model::timeline::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "timeline/no-entries");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = no_entries(&model, Span { start: 0, end: 8 }, row);
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
fn empty_section_trigger_and_clear() {
    for (i, source) in [
        "timeline\nsection A\n",
        "timeline\nsection A\n2020 : event\n",
    ]
    .iter()
    .enumerate()
    {
        let parsed = crate::syntax::timeline::parser::parse(source, &[]);
        let (model, _) = crate::model::timeline::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "timeline/empty-section");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = empty_section(&model, row);
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
fn empty_event_trigger_and_clear() {
    for (i, source) in ["timeline\n2020 :  \n", "timeline\n2020 : event\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::timeline::parser::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::timeline::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "timeline/empty-event");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = empty_event(&model, row);
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
