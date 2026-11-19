use super::run;
use crate::r#gen::lintrules::LINT_RULES;

#[test]
fn duplicate_id() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "c4/duplicate-id")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("C4Context\nPerson(a, \"A\")\nSystem(a, \"B\")\n", 1),
        ("C4Context\nPerson(a, \"A\")\nSystem(b, \"B\")\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::c4::parse(source, &prep.removed);
        let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
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
fn undefined_relationship_endpoint() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "c4/undefined-relationship-endpoint")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("C4Context\nPerson(a, \"A\")\nRel(a, b, \"uses\")\n", 1),
        (
            "C4Context\nRel(a, b, \"uses\")\nPerson(a, \"A\")\nSystem(b, \"B\")\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::c4::parse(source, &prep.removed);
        let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
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
fn undefined_element_style() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "c4/undefined-element-style")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("C4Context\nUpdateElementStyle(a, $bgColor=\"red\")\n", 1),
        (
            "C4Context\nUpdateElementStyle(a, $bgColor=\"red\")\nPerson(a, \"A\")\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::c4::parse(source, &prep.removed);
        let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
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
fn undefined_relationship_style_endpoint() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "c4/undefined-relationship-style-endpoint")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        (
            "C4Context\nPerson(a, \"A\")\nUpdateRelStyle(a, b, $textColor=\"red\")\n",
            1,
        ),
        (
            "C4Context\nUpdateRelStyle(a, b, $textColor=\"red\")\nPerson(a, \"A\")\nSystem(b, \"B\")\n",
            0,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::c4::parse(source, &prep.removed);
        let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
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
