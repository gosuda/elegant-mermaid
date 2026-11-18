use super::*;

#[test]
fn yaml_extensions_flow_multiline_values() {
    let src = "flow: [first\n  second, 'third\n  fourth']\n";
    let (value, diagnostics) = parse_config_yaml(src, 0, src.len());
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(
        mapping(value)[0].value,
        ConfigValue::Sequence(vec![
            ConfigValue::String("first second".into()),
            ConfigValue::String("third fourth".into()),
        ])
    );
}

#[test]
fn yaml_extensions_sequence_nodes_and_compact_collections() {
    let src = "items:\n  - 12\n  - [true, null]\n  -\n  - name: café\n    enabled: false\n  - - inner\n    - outer\n";
    let (value, diagnostics) = parse_config_yaml(src, 0, src.len());
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let entries = mapping(value);
    let items = sequence(entries[0].value.clone());
    assert_eq!(items[0], ConfigValue::Integer("12".into()));
    assert_eq!(
        items[1],
        ConfigValue::Sequence(vec![ConfigValue::Bool(true), ConfigValue::Null])
    );
    assert_eq!(items[2], ConfigValue::Null);
    assert_eq!(
        mapping(items[3].clone())[0].value,
        ConfigValue::String("café".into())
    );
    assert_eq!(
        items[4],
        ConfigValue::Sequence(vec![
            ConfigValue::String("inner".into()),
            ConfigValue::String("outer".into())
        ])
    );
}

#[test]
fn yaml_extensions_multiline_folding_and_escaped_breaks() {
    for ending in ["\n", "\r\n", "\r"] {
        let src = "plain: 12\n  34\nsingle: 'one\n  \n  two'\ndouble: \"one \\\n  two\"\nomitted:\n  text\n  continued\nbacktick: first line\n  `subroutine` remains plain\nquote: first line\n  'neo' remains plain\ndescription:\n  first long line\n  second longer line\n  size.\n".replace('\n', ending);
        let (value, diagnostics) = parse_config_yaml(&src, 0, src.len());
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let entries = mapping(value);
        assert_eq!(entries[0].value, ConfigValue::String("12 34".into()));
        assert_eq!(entries[1].value, ConfigValue::String("one\ntwo".into()));
        assert_eq!(entries[2].value, ConfigValue::String("one two".into()));
        assert_eq!(
            entries[3].value,
            ConfigValue::String("text continued".into())
        );
        assert_eq!(
            entries[4].value,
            ConfigValue::String("first line `subroutine` remains plain".into())
        );
        assert_eq!(
            entries[5].value,
            ConfigValue::String("first line 'neo' remains plain".into())
        );
        assert_eq!(
            entries[6].value,
            ConfigValue::String("first long line second longer line size.".into())
        );
    }
}

#[test]
fn yaml_extensions_depth_and_original_spans() {
    let accepted = format!("{}x\n", "- ".repeat(64));
    let (_, diagnostics) = parse_config_yaml(&accepted, 0, accepted.len());
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let src = format!("{}x\n", "- ".repeat(65));
    let (_, diagnostics) = parse_config_yaml(&src, 0, src.len());
    assert_eq!(diagnostics[0].code, C_DEPTH);
    assert_eq!(
        diagnostics[0].span,
        Span {
            start: 128,
            end: 129
        }
    );
    let src = "é:\n  - ok\n  - &anchor\n";
    let (_, diagnostics) = parse_config_yaml(src, 0, src.len());
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, C_ANCHOR);
    let span = diagnostics[0].span;
    assert_eq!(&src[span.start..span.end], "&anchor");
}

#[test]
fn yaml_extensions_do_not_extend_json_or_implicit_keys() {
    for src in ["{\"key\":\"one\n  two\"}", "{\"key\": - item}"] {
        let (_, diagnostics) = parse_config_json(src, 0, src.len());
        assert!(
            !diagnostics.is_empty(),
            "expected !diagnostics.is_empty(); observed diagnostics={:?}",
            diagnostics
        );
    }
    for src in ["'one\n  two': value\n", "{\"one\n  two\": value}\n"] {
        let (_, diagnostics) = parse_config_yaml(src, 0, src.len());
        assert!(
            !diagnostics.is_empty(),
            "expected !diagnostics.is_empty(); observed diagnostics={:?}",
            diagnostics
        );
    }
}

#[test]
fn yaml_extensions_compact_duplicate_preserves_key_span() {
    let src = "- café: first\n  café: second\n";
    let (value, diagnostics) = parse_config_yaml(src, 0, src.len());
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].message, "duplicate key");
    let entries = mapping(sequence(value).remove(0));
    assert_eq!(entries[0].key_span, Span { start: 2, end: 7 });
    assert_eq!(entries[0].value, ConfigValue::String("second".into()));
    let span = diagnostics[0].span;
    assert_eq!(&src[span.start..span.end], "café");
}

#[test]
fn config_quoted_gantt_frontmatter() -> Result<(), &'static str> {
    let src = include_str!("../../../../../corpus/gantt/mermaid/gantt~0011.mmd");
    let start = src.find('\n').ok_or("missing opening fence newline")? + 1;
    let end = start + src[start..].find("---").ok_or("missing closing fence")?;
    let (value, diagnostics) = parse_config_yaml(src, start, end);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let config = mapping(mapping(value)[2].value.clone());
    assert_eq!(config[0].value, ConfigValue::String(" // YAML supports multiline strings using a newline markers: \n #item36 { fill: CadetBlue }       \n\n// Custom marker workaround CSS from forum (below)    \n rect[id^=workaround] { height: calc(100% - 50px) ; transform: translate(9px, 25px); y: 0; width: 1.5px; stroke: none; fill: red; }   \n text[id^=workaround] { fill: red; y: 100%; font-size: 15px;} ".into()));
    Ok(())
}

#[test]
fn config_quoted_closing_line() {
    for quote in ["\"", "'"] {
        for (text, want) in [
            ("  key: Qone\n  two\n  Q", "one two "),
            ("  key: Qone\n two\n Q", "one two "),
            ("  key: Qone\n\ttwo\nQ", "one two "),
            ("key: Qone \n  two\n\n  three\nQ", "one two\nthree "),
            ("key: Q#{}[],:;\n---x\nQ", "#{}[],:; ---x "),
        ] {
            let src = text.replace('Q', quote);
            let (value, diagnostics) = parse_config_yaml(&src, 0, src.len());
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            assert_eq!(mapping(value)[0].value, ConfigValue::String(want.into()));
        }
    }
}

#[test]
fn config_quoted_unterminated_continuation() {
    let src = "key: \"one\nsecond";
    let (_, diagnostics) = parse_config_yaml(src, 0, src.len());
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, C_MALFORMED);
    assert_eq!(
        diagnostics[0].span,
        Span {
            start: src.len(),
            end: src.len()
        }
    );
}

#[test]
fn config_quoted_document_marker() {
    for marker in ["---", "..."] {
        let src = format!("key: \"one\n{marker}\n two\"");
        let (_, diagnostics) = parse_config_yaml(&src, 0, src.len());
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, C_MALFORMED);
        assert_eq!(diagnostics[0].message, "malformed config value");
        assert_eq!(diagnostics[0].span, Span { start: 10, end: 13 });
    }
}
