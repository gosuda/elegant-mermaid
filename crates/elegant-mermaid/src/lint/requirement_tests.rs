use super::run;
use crate::r#gen::lintrules::LINT_RULES;

#[test]
fn duplicate_name() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "requirement/duplicate-name")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        (
            "requirementDiagram\nrequirement A {\nid: 1\n}\nelement A {\ntype: \"test\"\n}\n",
            1,
        ),
        (
            "requirementDiagram\nrequirement A {\nid: 1\n}\nelement B {\ntype: \"test\"\n}\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::requirement::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::requirement::resolve(source, &parsed.document);
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
fn duplicate_id() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "requirement/duplicate-id")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        (
            "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement B {\nid: 1\n}\n",
            1,
        ),
        (
            "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement B {\nid: 2\n}\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::requirement::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::requirement::resolve(source, &parsed.document);
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
fn undefined_reference() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "requirement/undefined-reference")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        (
            "requirementDiagram\nrequirement A {\nid: 1\n}\nA - satisfies -> B\n",
            1,
        ),
        (
            "requirementDiagram\nA - satisfies -> B\nrequirement A {\nid: 1\n}\nelement B {\ntype: \"test\"\n}\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::requirement::parse(source, &prep.removed);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::requirement::resolve(source, &parsed.document);
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
