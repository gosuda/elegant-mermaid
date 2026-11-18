use super::{duplicate_attribute, duplicate_entity, standalone_entity};
use crate::r#gen::lintrules::LINT_RULES;

#[test]
fn duplicate_attribute_trigger_and_clear() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "er/duplicate-attribute")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("erDiagram\nA {\nint id\nstring id\n}\n", 1),
        ("erDiagram\nA {\nint id\nstring name\n}\n", 0),
        ("erDiagram\nA {\nint id\n}\nA {\nint id\n}\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::er::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = crate::model::er::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        let got = duplicate_attribute(&model, row);
        assert_eq!(got.len(), want, "{source}");
        for diagnostic in got {
            assert_eq!(diagnostic.code, row.code);
            assert_eq!(diagnostic.message, row.summary);
            assert_eq!(diagnostic.help, row.help);
            assert!(diagnostic.span.start < diagnostic.span.end);
            assert!(diagnostic.span.end <= source.len());
        }
    }
    Ok(())
}

#[test]
fn duplicate_entity_trigger_and_clear() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "er/duplicate-entity")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("erDiagram\nA {\nint id\n}\nA {\nint name\n}\n", 1),
        ("erDiagram\nA {\nint id\n}\nB {\nint name\n}\n", 0),
        ("erDiagram\nA\nA {\n}\nA {\n}\n", 1),
        ("erDiagram\nA\nA {\n}\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::er::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = crate::model::er::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        let got = duplicate_entity(&model, row);
        assert_eq!(got.len(), want, "{source}");
        for diagnostic in got {
            assert_eq!(diagnostic.code, row.code);
            assert_eq!(diagnostic.message, row.summary);
            assert_eq!(diagnostic.help, row.help);
            assert!(diagnostic.span.start < diagnostic.span.end);
            assert!(diagnostic.span.end <= source.len());
        }
    }
    Ok(())
}

#[test]
fn standalone_entity_trigger_and_clear() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "er/standalone-entity")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("erDiagram\nA {\nint id\n}\n", 1),
        ("erDiagram\nA {\nint id\n}\nA ||--|| B : owns\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::er::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, diagnostics) = crate::model::er::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        let got = standalone_entity(&model, row);
        assert_eq!(got.len(), want, "{source}");
        for diagnostic in got {
            assert_eq!(diagnostic.code, row.code);
            assert_eq!(diagnostic.message, row.summary);
            assert_eq!(diagnostic.help, row.help);
            assert!(diagnostic.span.start < diagnostic.span.end);
            assert!(diagnostic.span.end <= source.len());
        }
    }
    Ok(())
}
