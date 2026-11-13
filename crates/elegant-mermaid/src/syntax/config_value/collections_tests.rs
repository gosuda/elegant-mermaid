use super::*;

#[test]
fn plain_scalar_resolution_order() {
    assert_eq!(entry_value("k: null\n", "k"), ConfigValue::Null);
    assert_eq!(entry_value("k: ~\n", "k"), ConfigValue::Null);
    assert_eq!(entry_value("k: True\n", "k"), ConfigValue::Bool(true));
    assert_eq!(entry_value("k: FALSE\n", "k"), ConfigValue::Bool(false));
    assert_eq!(int_text(&entry_value("k: 007\n", "k")), "007");
    assert_eq!(int_text(&entry_value("k: +3\n", "k")), "+3");
    assert_eq!(dec_text(&entry_value("k: 1.25\n", "k")), "1.25");
    assert_eq!(
        entry_value("k: .inf\n", "k"),
        ConfigValue::String(String::from(".inf"))
    );
    assert_eq!(
        entry_value("k: 0x1F\n", "k"),
        ConfigValue::String(String::from("0x1F"))
    );
    assert_eq!(
        entry_value("k: hello world\n", "k"),
        ConfigValue::String(String::from("hello world"))
    );
}

#[test]
fn quoted_scalars_decode() {
    assert_eq!(text(entry_value("a: 'it''s'\n", "a")), "it's");
    assert_eq!(text(entry_value("a: \"n\\tt\\u0041\"\n", "a")), "n\ttA");
    assert_eq!(text(entry_value("a: \"\"\n", "a")), "");
    let (_, ds) = parse_config_yaml("a: 'x\\y'\n", 0, 9);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
}

#[test]
fn flow_collections() {
    let s = sequence(entry_value("a: [1, \"x y\", {b: 2}]\n", "a"));
    assert_eq!(s.len(), 3);
    assert_eq!(int_text(&s[0]), "1");
    assert_eq!(text(s[1].clone()), "x y");
    let m = mapping(s[2].clone());
    let [b] = m.as_slice() else {
        unreachable!("expected [b]; observed {:?}", m.as_slice())
    };
    assert_eq!(b.key, "b");
    assert_eq!(int_text(&b.value), "2");

    assert!(
        sequence(entry_value("a: []\n", "a")).is_empty(),
        "expected sequence(entry_value(\"a: []\\n\", \"a\")).is_empty(); observed sequence(entry_value(\"a: []\\n\", \"a\")).is_empty()={:?}",
        sequence(entry_value("a: []\n", "a")).is_empty()
    );
    assert!(
        mapping(entry_value("a: {}\n", "a")).is_empty(),
        "expected mapping(entry_value(\"a: {{}}\\n\", \"a\")).is_empty(); observed mapping(entry_value(\"a: {{}}\\n\", \"a\")).is_empty()={:?}",
        mapping(entry_value("a: {}\n", "a")).is_empty()
    );

    let s = sequence(entry_value("a: [\n  1,\n  2]\n", "a"));
    assert_eq!(s.len(), 2);
    assert_eq!(int_text(&s[1]), "2");

    let (_, ds) = parse_config_yaml("k: # note\nz: 1\n", 0, 15);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
}

#[test]
fn nested_maps() {
    let m = mapping(entry_value("a:\n  b: 1\n  c: 2\nd: x\n", "a"));
    let [b, c] = m.as_slice() else {
        unreachable!("expected [b, c]; observed {:?}", m.as_slice())
    };
    assert_eq!(b.key, "b");
    assert_eq!(int_text(&b.value), "1");
    assert_eq!(c.key, "c");
    assert_eq!(int_text(&c.value), "2");

    assert_eq!(mapping(parse_top("  a: 1\n  b: 2\n")).len(), 2);
    assert_eq!(text(entry_value("a:\n  b: 1\nd: x\n", "d")), "x");
}

#[test]
fn roots_allow_scalar_flow_and_map() {
    let (v, ds) = parse_config_yaml("hello world\n", 0, 12);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("hello world")));
    let (v, ds) = parse_config_yaml("[1, 2]\n", 0, 7);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(sequence(v).len(), 2);
    let (v, ds) = parse_config_yaml("\"abc\"\n", 0, 6);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("abc")));
    let (v, ds) = parse_config_yaml("true\n", 0, 5);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Bool(true));
    let (v, ds) = parse_config_yaml("abc", 2, 2);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Mapping(Vec::new()));
    let (_, ds) = parse_config_yaml("hello # c\n", 0, 10);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
}

#[test]
fn literal_block_chomping() {
    assert_eq!(block_value("a: |\n  x\n  y\nz: 1\n"), "x\ny\n");
    assert_eq!(block_value("a: |-\n  x\n  y\n"), "x\ny");
    assert_eq!(block_value("a: |+\n  x\n\n\nz: 1\n"), "x\n\n\n");
    assert_eq!(block_value("a: |\n\n  x\n"), "\nx\n");
    assert_eq!(block_value("a: |+\n\n\nz: 1\n"), "\n\n");
    assert_eq!(block_value("a: |-\n\n\nz: 1\n"), "");
    assert_eq!(block_value("a: |\n  x\n\n  y\n"), "x\n\ny\n");
}

#[test]
fn folded_block_chomping() {
    assert_eq!(block_value("a: >\n  x\n  y\n"), "x y\n");
    assert_eq!(block_value("a: >\n  x\n\n  y\n"), "x\ny\n");
    assert_eq!(block_value("a: >\n  x\n   z\n  y\n"), "x\n z\ny\n");
    assert_eq!(block_value("a: >-\n  x\n  y\n"), "x y");
}

#[test]
fn thousandths_examples() {
    let cases = [
        ("0.75", Some(750)),
        ("0.0005", Some(1)),
        ("1", Some(1000)),
        ("2.5", Some(2500)),
        ("-1.5", Some(-1500)),
        ("0", Some(0)),
        ("-0", Some(0)),
        ("0.0004", Some(0)),
        ("-0.0005", Some(-1)),
        ("9999999999999", None),
        ("2147483", Some(2147483000)),
        ("2147484", None),
        ("0.0075", Some(8)),
        ("1e3", Some(1000000)),
    ];
    for (t, want) in cases {
        let v = if t.contains('.') {
            ConfigValue::Decimal(String::from(t))
        } else {
            ConfigValue::Integer(String::from(t))
        };
        assert_eq!(thousandths(&v), want, "value {t}");
    }
    assert_eq!(thousandths(&ConfigValue::Null), None);
    assert_eq!(thousandths(&ConfigValue::Bool(true)), None);
    assert_eq!(thousandths(&ConfigValue::String(String::from("1"))), None);
}

#[test]
fn json_numbers_and_rewrite() {
    let src = "{\"a\": 1, \"b\": 2.5, \"c\": -3, \"d\": 1e2}";
    let (v, ds) = parse_config_json(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    let m = mapping(v);
    let [a, b, c, d] = m.as_slice() else {
        unreachable!("expected [a, b, c, d]; observed {:?}", m.as_slice())
    };
    assert_eq!(int_text(&a.value), "1");
    assert_eq!(dec_text(&b.value), "2.5");
    assert_eq!(int_text(&c.value), "-3");
    assert_eq!(dec_text(&d.value), "1e2");

    let src = "{'theme': 'dark'}";
    let (v, ds) = parse_config_json(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    let m = mapping(v);
    let [t] = m.as_slice() else {
        unreachable!("expected [t]; observed {:?}", m.as_slice())
    };
    assert_eq!(t.key, "theme");
    assert_eq!(text(t.value.clone()), "dark");
}

#[test]
fn range_clamps_and_empty_range() {
    let (v, ds) = parse_config_yaml("a: 1", 0, 100);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(int_text(&entry_of(&mapping(v), "a").value), "1");
    let (v, ds) = parse_config_yaml("abc", 2, 2);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Mapping(Vec::new()));
    let (v, ds) = parse_config_json("", 0, 0);
    assert!(
        !ds.is_empty(),
        "expected !ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Null);
}

#[test]
fn config_root_flow_trailing_tab_is_not_indentation() {
    let (value, diagnostics) = parse_config_yaml("{}\t", 0, 3);
    assert_eq!(value, ConfigValue::Mapping(Vec::new()));
    assert!(
        diagnostics.is_empty(),
        "expected diagnostics.is_empty(); observed diagnostics={:?}",
        diagnostics
    );
}

#[test]
fn config_root_flow_stop_reports_only_first_error() {
    let (_, diagnostics) = parse_config_yaml("[:", 0, 2);
    check(
        &diagnostics,
        C_MALFORMED,
        "malformed config value",
        Span { start: 1, end: 2 },
    );
}
