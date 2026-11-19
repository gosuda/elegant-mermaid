use super::run;
use crate::r#gen::lintrules::LINT_RULES;

#[test]
fn duplicate_class() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "class/duplicate-class")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("classDiagram\nclass A\nclass A\n", 1),
        ("classDiagram\nclass A\nclass B\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::class::parse(source, &prep.removed);
        let (model, _) = crate::model::class::resolve(source, &parsed.document);
        let got = run(&model, row);
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
fn no_duplicate_methods() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "class/no-duplicate-methods")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("classDiagram\nclass A {\n+run() void\n+run() void\n}\n", 1),
        ("classDiagram\nclass A {\n+run() void\n+stop() void\n}\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::class::parse(source, &prep.removed);
        let (model, _) = crate::model::class::resolve(source, &parsed.document);
        let got = run(&model, row);
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
