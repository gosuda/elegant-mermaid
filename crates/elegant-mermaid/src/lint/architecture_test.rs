#[test]
fn consumer_rules_trigger_and_nontrigger() -> Result<(), &'static str> {
    for (code, source, expected) in [
        ("architecture/no-elements", "architecture-beta\n", 1),
        (
            "architecture/no-elements",
            "architecture-beta\nservice a(server)\n",
            0,
        ),
        (
            "architecture/no-edges",
            "architecture-beta\nservice a(server)\n",
            1,
        ),
        (
            "architecture/no-edges",
            "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n",
            0,
        ),
        (
            "architecture/duplicate-edge",
            "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\na:R -- L:b\n",
            1,
        ),
        (
            "architecture/duplicate-edge",
            "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\na:L -- R:b\n",
            0,
        ),
        (
            "architecture/no-elements",
            "architecture-beta\nservice a(server) in missing\n",
            0,
        ),
        (
            "architecture/no-edges",
            "architecture-beta\nservice a(server) in missing\n",
            1,
        ),
        (
            "architecture/no-edges",
            "architecture-beta\nservice a(server)\na:R -- L:missing\n",
            0,
        ),
        (
            "architecture/duplicate-edge",
            "architecture-beta\na:R -- L:b\na:R -- L:b\n",
            1,
        ),
        (
            "architecture/duplicate-edge",
            "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\nb:L -- R:a\n",
            0,
        ),
    ] {
        let parsed = crate::syntax::architecture::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (model, _) = crate::model::architecture::resolve(source, &parsed.document);
        let row = crate::r#gen::lintrules::LINT_RULES
            .iter()
            .find(|row| row.code == code)
            .ok_or("registered rule")?;
        let findings = match code {
            "architecture/no-elements" => super::no_elements(&model, row),
            "architecture/no-edges" => super::no_edges(&model, row),
            "architecture/duplicate-edge" => super::duplicate_edge(&model, row),
            _ => unreachable!(),
        };
        assert_eq!(findings.len(), expected, "{code} on {source:?}");
        for diagnostic in findings {
            assert!(!diagnostic.message.is_empty() && !diagnostic.help.is_empty());
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len()
            );
            if code == "architecture/duplicate-edge" {
                assert_eq!(Some(diagnostic.span.start), source.rfind("a:R -- L:b"));
            } else {
                assert_eq!(diagnostic.span, parsed.document.header.span);
            }
        }
    }
    Ok(())
}
