use super::run;
use crate::r#gen::lintrules::LINT_RULES;

#[test]
fn duplicate_state() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "state/duplicate-state")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("stateDiagram-v2\nstate A\nstate A\n", 1),
        ("stateDiagram-v2\nstate A\nstate B\n", 0),
        (
            "stateDiagram-v2\nstate A <<choice>>\nstate A <<choice>>\n",
            0,
        ),
        (
            "stateDiagram-v2\nstate A {\n}\nstate A {\nstate B\nstate B\n}\n",
            2,
        ),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::state::parse(source, &prep.removed);
        let (model, _) = crate::model::state::resolve(source, &parsed.document);
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
fn duplicate_transition() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "state/duplicate-transition")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("stateDiagram-v2\nA --> B: go\nA --> B::go\n", 0),
        ("stateDiagram-v2\nA --> B: go\nA --> B: go\n", 1),
        ("stateDiagram-v2\nA --> B: go\nA --> B: stop\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::state::parse(source, &prep.removed);
        let (model, _) = crate::model::state::resolve(source, &parsed.document);
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
fn empty_composite() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "state/empty-composite")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("stateDiagram-v2\nstate A {\n}\n", 1),
        ("stateDiagram-v2\nstate A {\nstate B\n}\n", 0),
        ("stateDiagram-v2\nstate A {\ndirection LR\n}\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::state::parse(source, &prep.removed);
        let (model, _) = crate::model::state::resolve(source, &parsed.document);
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
fn self_transition() -> Result<(), Box<dyn std::error::Error>> {
    let row = LINT_RULES
        .iter()
        .find(|row| row.code == "state/self-transition")
        .ok_or("missing lint registry row")?;
    for (source, want) in [
        ("stateDiagram-v2\nA --> A: go\n", 1),
        ("stateDiagram-v2\nA --> B: go\n", 0),
    ] {
        let prep = crate::syntax::preprocess::preprocess(source);
        let parsed = crate::syntax::state::parse(source, &prep.removed);
        let (model, _) = crate::model::state::resolve(source, &parsed.document);
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
