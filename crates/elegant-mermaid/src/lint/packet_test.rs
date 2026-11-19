use super::packet::*;
use crate::source::Span;
#[test]
fn no_fields_trigger_and_clear() {
    for (i, source) in ["packet\n", "packet\n0: \"a\"\n"].iter().enumerate() {
        let parsed = crate::syntax::packet::parser::parse(source, &[]);
        let (model, _) = crate::model::packet::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "packet/no-fields");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = no_fields(&model, Span { start: 0, end: 6 }, row);
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
fn empty_labels_trigger_and_clear() {
    for (i, source) in ["packet\n0: \"\"\n", "packet\n0: \"a\"\n"]
        .iter()
        .enumerate()
    {
        let parsed = crate::syntax::packet::parser::parse(source, &[]);
        let (model, _) = crate::model::packet::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|r| r.code == "packet/empty-labels");
        assert!(row.is_some(), "missing registry row");
        if let Some(row) = row {
            let ds = empty_labels(&model, row);
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
