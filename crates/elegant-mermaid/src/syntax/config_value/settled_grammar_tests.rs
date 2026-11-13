use super::*;

#[test]
fn settled_root_forms() {
    let (_, ds) = parse_config_yaml("|", 0, 1);
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 0, end: 1 },
    );
    let src = "  >\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 2, end: 3 },
    );
    let (v, ds) = parse_config_yaml("  c0\n", 0, 5);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("c0")));
    let (v, ds) = parse_config_yaml("  ---\n", 0, 6);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("---")));
    let (v, ds) = parse_config_yaml("a:b\n", 0, 4);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("a:b")));
    let (v, ds) = parse_config_yaml("a :b\n", 0, 5);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("a :b")));
}

#[test]
fn settled_root_indicator_forms() {
    let (v, ds) = parse_config_yaml("-", 0, 1);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Sequence(vec![ConfigValue::Null]));
    let (v, ds) = parse_config_yaml("-42", 0, 3);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Integer(String::from("-42")));
    let (v, ds) = parse_config_yaml("-word", 0, 5);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("-word")));
    let (v, ds) = parse_config_yaml("?", 0, 1);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("?")));
    let (v, ds) = parse_config_yaml("  --- x\n", 0, 8);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::String(String::from("--- x")));
}

#[test]
fn settled_marker_column_zero_only() {
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
fn settled_map_colon_rules() {
    let (v, ds) = parse_config_yaml("a:", 0, 2);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    let m = mapping(v);
    let [a] = m.as_slice() else {
        unreachable!("expected [a]; observed {:?}", m.as_slice())
    };
    assert_eq!(a.key, "a");
    assert_eq!(a.value, ConfigValue::Null);

    let m = mapping(parse_top("k :\tv\n"));
    let [k] = m.as_slice() else {
        unreachable!("expected [k]; observed {:?}", m.as_slice())
    };
    assert_eq!(k.key, "k");
    assert_eq!(text(k.value.clone()), "v");

    let m = mapping(parse_top("-x:\n"));
    let [x] = m.as_slice() else {
        unreachable!("expected [x]; observed {:?}", m.as_slice())
    };
    assert_eq!(x.key, "-x");

    let m = mapping(parse_top("-c0>\t0[#}20:"));
    let [w] = m.as_slice() else {
        unreachable!("expected [w]; observed {:?}", m.as_slice())
    };
    assert_eq!(w.key, "-c0>\t0[#}20");

    let m = mapping(parse_top("\"a: b\": 1\n"));
    let [q] = m.as_slice() else {
        unreachable!("expected [q]; observed {:?}", m.as_slice())
    };
    assert_eq!(q.key, "a: b");
    assert_eq!(int_text(&q.value), "1");

    let src = ": v\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 0, end: 1 },
    );

    let src = "\"k\":v\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 3, end: 5 },
    );

    let src = "k: :\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 3, end: 4 },
    );

    let m = mapping(parse_top("a{b: 1\n"));
    let [k] = m.as_slice() else {
        unreachable!("expected [k]; observed {:?}", m.as_slice())
    };
    assert_eq!(k.key, "a{b");
    assert_eq!(int_text(&k.value), "1");

    let m = mapping(parse_top("a\"b: 1\n"));
    let [k2] = m.as_slice() else {
        unreachable!("expected [k2]; observed {:?}", m.as_slice())
    };
    assert_eq!(k2.key, "a\"b");

    let src = "|x: 1\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 0, end: 3 },
    );

    let src = "#x: 1\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
}

#[test]
fn settled_flow_reports_first_rejected_byte() {
    let src = "a: [1, @]\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 7, end: 9 },
    );

    let src = "{#x: 1}";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 1, end: 4 },
    );

    let src = "a: [\n\t1]\n";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "tab in indentation",
        Span { start: 5, end: 6 },
    );
}

#[test]
fn settled_blank_range_is_empty_mapping() {
    let (v, ds) = parse_config_yaml("", 0, 0);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Mapping(Vec::new()));

    let src = "\n  \n# c\n";
    let (v, ds) = parse_config_yaml(src, 0, src.len());
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(v, ConfigValue::Mapping(Vec::new()));
}

#[test]
fn settled_flow_hash_is_text() {
    let (v, ds) = parse_config_yaml("[a #b]", 0, 6);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(sequence(v), vec![ConfigValue::String("a #b".to_string())]);

    let (v, ds) = parse_config_yaml("[a\t#b]", 0, 6);
    assert!(
        ds.is_empty(),
        "expected ds.is_empty(); observed ds={:?}",
        ds
    );
    assert_eq!(sequence(v), vec![ConfigValue::String("a\t#b".to_string())]);
}

#[test]
fn settled_header_line_in_block_map_fails() {
    let src = "2|200-:\n>";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 8, end: 9 },
    );
}

#[test]
fn settled_malformed_uses_token_span() {
    let src = "-|\\}!\"]:\n[{b:{b!{0\"\\} \t|\\0- !";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 9, end: 21 },
    );
}

#[test]
fn settled_flow_continuation_column() {
    let src = "{\\\n\nc:0b'\t'\n!#\"# \\#!{->':*{1,-, \t&\t-";
    let (_, ds) = parse_config_yaml(src, 0, src.len());
    check(
        &ds,
        C_MALFORMED,
        "malformed config value",
        Span { start: 4, end: 9 },
    );
}

#[test]
fn random_spans_stay_in_range() {
    for i in 0u32..2000 {
        let s = random_case(i);
        let (v, ds) = parse_config_yaml(&s, 0, s.len());
        let _ = v;
        for d in &ds {
            assert!(
                in_bounds(&s, d.span),
                "yaml case {i} span {:?} src {s:?}",
                d.span
            );
        }
        let (jv, jd) = parse_config_json(&s, 0, s.len());
        let _ = jv;
        for d in &jd {
            assert!(
                in_bounds(&s, d.span),
                "json case {i} span {:?} src {s:?}",
                d.span
            );
        }
    }
}
