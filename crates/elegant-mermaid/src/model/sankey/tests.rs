use super::{Value, ValueKind, parse_value, resolve};

#[test]
fn sankey_numeric_prefix_and_rounding() {
    let finite = [
        ("1.2345tail", 1235),
        ("-0.0005", -1),
        ("1e-3", 1),
        ("1e+broken", 1000),
        ("0x10", 0),
        (".5", 500),
        ("2147483.647", 2147483647),
        ("1e-999999999", 0),
    ];
    for (source, thousandths) in finite {
        assert_eq!(
            parse_value(source),
            Value {
                kind: ValueKind::Finite,
                thousandths
            },
            "{source}"
        );
    }
    assert_eq!(parse_value("2147483.6475").kind, ValueKind::Overflow);
    assert_eq!(parse_value("1e999999999").kind, ValueKind::Overflow);
    for source in ["", "Infinity", "-Infinity", "NaN", "."] {
        assert_eq!(parse_value(source).kind, ValueKind::NonFinite, "{source}");
    }
}

#[test]
fn sankey_records_preserve_empty_ids_and_declaration_order() {
    let source = "sankey\n,b,1\n\"b\",\"\",2\nb,b,0\n,,";
    let (document, diagnostics) = crate::syntax::sankey::parse(source, &[]);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (model, diagnostics) = resolve(source, &document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["", "b"]
    );
    assert_eq!(
        model
            .links
            .iter()
            .map(|link| (link.source, link.target))
            .collect::<Vec<_>>(),
        [(0, 1), (1, 0), (1, 1), (0, 0)]
    );
    assert_eq!(model.links[3].value.kind, ValueKind::NonFinite);
}

#[test]
fn sankey_bad_record_recovers_without_phantom_nodes() {
    let source = "sankey\na,b\nc,d,1,e\nf,g,2";
    let (document, diagnostics) = crate::syntax::sankey::parse(source, &[]);
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(
        diagnostics[0].message,
        "unexpected \n, expected one of: COMMA"
    );
    assert_eq!(
        diagnostics[1].message,
        "unexpected ,, expected one of: EOF, NEWLINE"
    );
    let (model, _) = resolve(source, &document);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["f", "g"]
    );
    assert_eq!(model.links.len(), 1);
}

#[test]
fn sankey_unterminated_quote_has_one_diagnostic() {
    let source = "sankey\n\"broken";
    let (_, diagnostics) = crate::syntax::sankey::parse(source, &[]);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "sankey/unterminated");
    assert_eq!(diagnostics[0].span.start, 7);
    assert_eq!(diagnostics[0].span.end, source.len());
}
