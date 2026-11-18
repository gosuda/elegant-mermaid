use super::*;

#[test]
fn tab_in_indentation_span() {
    let src = "a: 1\n\tb: 2\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "tab in indentation",
        Span { start: 5, end: 6 },
    );
}

#[test]
fn block_sequence_scalar() {
    let (value, ds) = parse_config_yaml("- x\n", 0, 4);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(
        value,
        ConfigValue::Sequence(vec![ConfigValue::String("x".into())])
    );
}

#[test]
fn complex_key_span() {
    let (_, ds) = parse_config_yaml("? x\n", 0, 4);
    check(
        &ds,
        C_MALFORMED,
        "complex keys are not supported",
        Span { start: 0, end: 1 },
    );
}

#[test]
fn multi_document_marker_span() {
    let src = "---\na: 1\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "multi-document streams are not supported",
        Span { start: 0, end: 3 },
    );
    let src = "...\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "multi-document streams are not supported",
        Span { start: 0, end: 3 },
    );
}

#[test]
fn block_header_digit_span() {
    let src = "a: |2\n  x\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "block scalar indentation indicator is not supported",
        Span { start: 4, end: 5 },
    );
}

#[test]
fn invalid_escape_span() {
    let src = "a: \"x\\q\"\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "invalid escape",
        Span { start: 5, end: 7 },
    );
}

#[test]
fn yaml_surrogate_escape_span() {
    let src = "a: \"\\uD800\"\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "invalid unicode escape",
        Span { start: 4, end: 10 },
    );
}

#[test]
fn json_surrogate_pair_forms_one_char() {
    let src = "{\"a\": \"\\uD83D\\uDE00\"}";
    let (v, ds) = parse_config_json(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    let m = mapping(v);
    let [e] = m.as_slice() else {
        unreachable!("expected [e]; observed {:?}", m.as_slice())
    };
    assert_eq!(e.key, "a");
    assert_eq!(text(e.value.clone()), "\u{1F600}");
}

#[test]
fn json_surrogate_failures() {
    let src = "{\"a\": \"\\uDC00\"}";
    let (_, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "invalid unicode escape",
        Span { start: 7, end: 13 },
    );
    let src = "{\"a\": \"\\uD800x\"}";
    let (_, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "invalid unicode escape",
        Span { start: 7, end: 13 },
    );
}

#[test]
fn duplicate_key_later_wins_at_first_position() {
    let src = "a: 1\nb: 2\na: 3\n";
    let (v, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "duplicate key",
        Span { start: 10, end: 11 },
    );
    let m = mapping(v);
    let [a, b] = m.as_slice() else {
        unreachable!("expected [a, b]; observed {:?}", m.as_slice())
    };
    assert_eq!(a.key, "a");
    assert_eq!(a.key_span, Span { start: 0, end: 1 });
    assert_eq!(int_text(&a.value), "3");
    assert_eq!(b.key, "b");
    assert_eq!(int_text(&b.value), "2");
}

#[test]
fn json_duplicate_key_follows_same_rule() {
    let src = "{\"a\": 1, \"a\": 2}";
    let (v, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "duplicate key",
        Span { start: 9, end: 12 },
    );
    let m = mapping(v);
    let [a] = m.as_slice() else {
        unreachable!("expected [a]; observed {:?}", m.as_slice())
    };
    assert_eq!(int_text(&a.value), "2");
}

#[test]
fn malformed_config_value_token_spans() {
    let cases = [
        ("a: @x\n", 3, 5),
        ("a: [1,]\n", 6, 7),
        ("a: {b 1}\n", 7, 8),
        ("a: [1,,2]\n", 6, 9),
        ("a: 1\n    b: 2\n", 9, 11),
        ("a: [\n1]\n", 5, 7),
    ];
    for (src, start, end) in cases {
        let (_, ds) = parse_config_yaml(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start, end },
        );
    }
}

#[test]
fn anchor_and_tag_spans() {
    let src = "a: &x 1\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        "config/unsupported-anchor",
        "anchors and aliases are not supported",
        Span { start: 3, end: 5 },
    );
    let src = "a: !x 1\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        "config/unsupported-tag",
        "tags are not supported",
        Span { start: 3, end: 5 },
    );
    let src = "a: *y\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        "config/unsupported-anchor",
        "anchors and aliases are not supported",
        Span { start: 3, end: 5 },
    );
}

#[test]
fn nesting_depth_at_level_65() {
    let src = format!("k: {}", "[".repeat(65));
    let (_, ds) = parse_config_yaml(&src, 0, src.len());
    check(
        &ds,
        "limit/nesting-depth",
        "nesting depth exceeds 64",
        Span { start: 66, end: 67 },
    );
}

#[test]
fn json_grammar_failures() {
    let src = "{a: 1}";
    let (_, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 1, end: 3 },
    );

    let src = "{} x";
    let (_, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 3, end: 4 },
    );

    let src = "{\"a\": \"x'y\"}";
    let (_, ds) = parse_config_json(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 9, end: 12 },
    );
}

#[test]
fn json_literal_fails_at_first_rejected_byte() {
    for (src, start, end) in [
        ("{\"a\": truBe}", 9, 12),
        ("{\"a\": tru}", 9, 10),
        ("{\"a\": nulx}", 9, 11),
        ("{\"a\": fals}", 10, 11),
        ("{\"a\": True}", 6, 11),
        ("{\"a\": x}", 6, 8),
    ] {
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start, end },
        );
    }
}

#[test]
fn json_number_fails_at_first_rejected_byte() {
    for (src, start, end) in [
        ("{\"a\": -}", 7, 8),
        ("{\"a\": -x}", 7, 9),
        ("{\"a\": 1.}", 8, 9),
        ("{\"a\": 1.x}", 8, 10),
        ("{\"a\": 1e}", 8, 9),
        ("{\"a\": 1e+}", 9, 10),
        ("{\"a\": 1.5e-x}", 11, 13),
        ("{\"a\": 1.\n}", 8, 9),
    ] {
        let (_, ds) = parse_config_json(src, 0, src.len());
        check(
            &ds,
            C_MALFORMED,
            "malformed config value",
            Span { start, end },
        );
    }
}

#[test]
fn root_plain_scalar_continues_at_column_zero() {
    let src = "a\nb\n\nc\n";
    let (v, ds) = parse_config_yaml(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("a b\nc")));
    let src = "   a\nb\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 5, end: 6 },
    );
}

#[test]
fn quoted_colon_line_is_a_scalar() {
    for quote in ["\"", "'"] {
        for (name, src, want) in [
            ("next line", "a:\n  Qx: yQ\n", "x: y"),
            ("plain continuation", "a: v\n  Qx: yQ\n", "v Qx: yQ"),
        ] {
            let src = src.replace('Q', quote);
            let want = want.replace('Q', quote);
            assert_eq!(text(entry_value(&src, "a")), want, "{name}");
        }
        let item = format!("a:\n  - {quote}x: y{quote}\n");
        assert_eq!(
            sequence(entry_value(&item, "a")),
            vec![ConfigValue::String(String::from("x: y"))]
        );
        let root = format!("{quote}a: b{quote}\n");
        assert_eq!(parse_top(&root), ConfigValue::String(String::from("a: b")));
    }
}
