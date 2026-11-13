use super::*;

fn check(ds: &[Diagnostic], code: &str, msg: &str, span: Span) {
    let [d] = ds else {
        unreachable!("expected [d]; observed {:?}", ds)
    };
    assert_eq!(d.code, code);
    assert_eq!(d.message, msg);
    assert_eq!(d.span, span);
    assert_eq!(d.severity, Severity::Error);
    assert!(
        d.help.is_empty(),
        "expected d.help.is_empty(); observed d.help={:?}",
        d.help
    );
}

fn sequence(v: ConfigValue) -> Vec<ConfigValue> {
    let ConfigValue::Sequence(s) = v else {
        unreachable!("expected ConfigValue::Sequence(s); observed {:?}", v)
    };
    s
}

fn same_shape(a: &ConfigValue, b: &ConfigValue) -> bool {
    match (a, b) {
        (ConfigValue::Mapping(ma), ConfigValue::Mapping(mb)) => {
            ma.len() == mb.len()
                && ma
                    .iter()
                    .zip(mb)
                    .all(|(x, y)| x.key == y.key && same_shape(&x.value, &y.value))
        }
        (ConfigValue::Sequence(sa), ConfigValue::Sequence(sb)) => {
            sa.len() == sb.len() && sa.iter().zip(sb).all(|(x, y)| same_shape(x, y))
        }
        _ => a == b,
    }
}

fn cfg_of(p: &Preprocessed) -> ConfigValue {
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    let Some(c) = &f.config else {
        unreachable!("expected Some(c); observed {:?}", &f.config)
    };
    c.clone()
}

fn str_map(pairs: &[(&str, &str)]) -> Vec<Entry> {
    pairs
        .iter()
        .map(|(k, v)| Entry {
            key: String::from(*k),
            key_span: Span { start: 0, end: 0 },
            value: ConfigValue::String(String::from(*v)),
        })
        .collect()
}

#[test]
fn no_fence_and_unterminated_fence() {
    let p = preprocess("flowchart TD\n");
    assert!(
        p.frontmatter.is_none(),
        "expected p.frontmatter.is_none(); observed p.frontmatter={:?}",
        p.frontmatter
    );
    assert!(
        p.removed.is_empty(),
        "expected p.removed.is_empty(); observed p.removed={:?}",
        p.removed
    );
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    let p = preprocess("---\na: 1\n");
    assert!(
        p.frontmatter.is_none(),
        "expected p.frontmatter.is_none(); observed p.frontmatter={:?}",
        p.frontmatter
    );
    assert!(
        p.removed.is_empty(),
        "expected p.removed.is_empty(); observed p.removed={:?}",
        p.removed
    );
    let p = preprocess("--- x\na: 1\n");
    assert!(
        p.frontmatter.is_none(),
        "expected p.frontmatter.is_none(); observed p.frontmatter={:?}",
        p.frontmatter
    );
    let p = preprocess("----\na: 1\n");
    assert!(
        p.frontmatter.is_none(),
        "expected p.frontmatter.is_none(); observed p.frontmatter={:?}",
        p.frontmatter
    );
}

#[test]
fn fence_shapes_and_line_endings() {
    let p = preprocess("---\nconfig:\n  theme: dark\n---\nA");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(f.body, Span { start: 4, end: 26 });
    assert!(
        same_shape(
            &cfg_of(&p),
            &ConfigValue::Mapping(str_map(&[("theme", "dark")]))
        ),
        "expected same_shape( &cfg_of(&p), &ConfigValue::Mapping(str_map(&[(\"theme\", \"dark\")])) ); observed p={:?}",
        p
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 30 }]);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );

    let p = preprocess("  --- \na: 1\n  ---\nB");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(f.body, Span { start: 7, end: 12 });
    assert_eq!(p.removed, vec![Span { start: 0, end: 18 }]);

    let p = preprocess("---\r\nconfig: {a: 1}\r\n---\r\nA");
    let want = ConfigValue::Mapping(vec![Entry {
        key: String::from("a"),
        key_span: Span { start: 0, end: 0 },
        value: ConfigValue::Integer(String::from("1")),
    }]);
    assert!(
        same_shape(&cfg_of(&p), &want),
        "expected same_shape(&cfg_of(&p), &want); observed p={:?}",
        p
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 26 }]);

    let p = preprocess("---\ra: 1\r---\rB");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(f.body, Span { start: 4, end: 9 });
    assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
}

#[test]
fn frontmatter_roots_without_config() {
    let p = preprocess("---\nhello\n---\nA");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(f.value, ConfigValue::String(String::from("hello")));
    assert!(
        f.config.is_none(),
        "expected f.config.is_none(); observed f.config={:?}",
        f.config
    );
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );

    let p = preprocess("---\n[1, 2]\n---\nA");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(sequence(f.value.clone()).len(), 2);
    assert!(
        f.config.is_none(),
        "expected f.config.is_none(); observed f.config={:?}",
        f.config
    );
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );

    let p = preprocess("---\n---\nA");
    let Some(f) = &p.frontmatter else {
        unreachable!("expected Some(f); observed {:?}", &p.frontmatter)
    };
    assert_eq!(f.body, Span { start: 4, end: 4 });
    assert_eq!(f.value, ConfigValue::Mapping(Vec::new()));
    assert!(
        f.config.is_none(),
        "expected f.config.is_none(); observed f.config={:?}",
        f.config
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 8 }]);
}

#[test]
fn frontmatter_config_must_be_mapping_span() {
    let p = preprocess("---\nconfig: 42\n---\nA\n");
    check(
        &p.diagnostics,
        C_MALFORMED,
        "frontmatter config must be a mapping",
        Span { start: 12, end: 14 },
    );
    assert!(
        p.frontmatter.as_ref().is_none_or(|f| f.config.is_none()),
        "non-mapping frontmatter config must not be retained; observed frontmatter {:?}",
        p.frontmatter
    );
}

#[test]
fn unknown_directives_removed_silently() {
    let p = preprocess("%%{foo bar}%%\nA\n");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert!(
        p.directives.is_empty(),
        "expected p.directives.is_empty(); observed p.directives={:?}",
        p.directives
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);

    let p = preprocess("%%{}%%\nA");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert!(
        p.directives.is_empty(),
        "expected p.directives.is_empty(); observed p.directives={:?}",
        p.directives
    );

    let p = preprocess("%%{initx: 1}%%\nA");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert!(
        p.directives.is_empty(),
        "expected p.directives.is_empty(); observed p.directives={:?}",
        p.directives
    );
}

#[test]
fn malformed_directive_forms() {
    let p = preprocess("%%{init x}%%\n");
    check(
        &p.diagnostics,
        C_MALFORMED,
        "malformed directive",
        Span { start: 0, end: 3 },
    );
    assert!(
        p.directives.is_empty(),
        "expected p.directives.is_empty(); observed p.directives={:?}",
        p.directives
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 12 }]);

    let p = preprocess("%%{init: {\n");
    check(
        &p.diagnostics,
        C_MALFORMED,
        "malformed directive",
        Span { start: 0, end: 3 },
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 11 }]);

    let p = preprocess("%%{wrap: x}%%\n");
    check(
        &p.diagnostics,
        C_MALFORMED,
        "wrap takes no body",
        Span { start: 0, end: 3 },
    );
    assert!(
        p.directives.is_empty(),
        "expected p.directives.is_empty(); observed p.directives={:?}",
        p.directives
    );
    assert!(!p.wrap, "expected !p.wrap; observed !p.wrap={:?}", !p.wrap);
    assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);

    let p = preprocess("%%{init: 1}%%\n");
    check(
        &p.diagnostics,
        C_MALFORMED,
        "directive body must be a JSON object",
        Span { start: 9, end: 10 },
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);
}

#[test]
fn known_directives_without_effect() {
    let p = preprocess("%%{init}%%\n");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    let [d] = p.directives.as_slice() else {
        unreachable!("expected [d]; observed {:?}", p.directives.as_slice())
    };
    assert_eq!(d.name, "init");
    assert!(
        d.init.is_none(),
        "expected d.init.is_none(); observed d.init={:?}",
        d.init
    );
    assert!(!d.wrap, "expected !d.wrap; observed !d.wrap={:?}", !d.wrap);
    assert_eq!(p.removed, vec![Span { start: 0, end: 10 }]);

    let p = preprocess("%%{init: }%%\n");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    let [d] = p.directives.as_slice() else {
        unreachable!("expected [d]; observed {:?}", p.directives.as_slice())
    };
    assert!(
        d.init.is_none(),
        "expected d.init.is_none(); observed d.init={:?}",
        d.init
    );
    assert_eq!(d.body, Span { start: 8, end: 9 });

    let p = preprocess("%%{initialize}%%\nA");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    let [d] = p.directives.as_slice() else {
        unreachable!("expected [d]; observed {:?}", p.directives.as_slice())
    };
    assert_eq!(d.name, "initialize");
}

#[test]
fn wrap_directive_sets_flag() {
    let p = preprocess("%%{wrap}%%\nB");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert!(p.wrap, "expected p.wrap; observed p.wrap={:?}", p.wrap);
    let [d] = p.directives.as_slice() else {
        unreachable!("expected [d]; observed {:?}", p.directives.as_slice())
    };
    assert_eq!(d.name, "wrap");
    assert!(d.wrap, "expected d.wrap; observed d.wrap={:?}", d.wrap);
    assert_eq!(d.body, Span { start: 7, end: 7 });
    assert_eq!(p.removed, vec![Span { start: 0, end: 10 }]);
}

#[test]
fn init_bodies_merge_to_depth_two() {
    let src = "%%{init: {'a': {'x': 1, 'y': 2}}}%%%%{init: {'a': {'y': 3}, 'b': 4}}%%\nZ";
    let p = preprocess(src);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert_eq!(p.directives.len(), 2);
    let Some(merged) = &p.init_config else {
        unreachable!("expected Some(merged); observed {:?}", &p.init_config)
    };
    let want = ConfigValue::Mapping(vec![
        Entry {
            key: String::from("a"),
            key_span: Span { start: 0, end: 0 },
            value: ConfigValue::Mapping(vec![
                Entry {
                    key: String::from("x"),
                    key_span: Span { start: 0, end: 0 },
                    value: ConfigValue::Integer(String::from("1")),
                },
                Entry {
                    key: String::from("y"),
                    key_span: Span { start: 0, end: 0 },
                    value: ConfigValue::Integer(String::from("3")),
                },
            ]),
        },
        Entry {
            key: String::from("b"),
            key_span: Span { start: 0, end: 0 },
            value: ConfigValue::Integer(String::from("4")),
        },
    ]);
    assert!(
        same_shape(merged, &want),
        "expected same_shape(merged, &want); observed merged={:?}, want={:?}",
        merged,
        want
    );
}

#[test]
fn init_config_key_stays_ordinary() {
    let src = "%%{init: {'config': {'x': 1}}}%%\n";
    let p = preprocess(src);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    let Some(merged) = &p.init_config else {
        unreachable!("expected Some(merged); observed {:?}", &p.init_config)
    };
    let ConfigValue::Mapping(m) = merged else {
        unreachable!("expected ConfigValue::Mapping(m); observed {:?}", merged)
    };
    assert_eq!(m.len(), 1);
    assert_eq!(m[0].key, "config");
}

#[test]
fn comment_lines_removed_and_directives_inside_them_apply() {
    let p = preprocess("%% hi\nA\n");
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert_eq!(p.removed, vec![Span { start: 0, end: 6 }]);

    let src = "%% x %%{init: {'t': 1}}%%\nA\n";
    let p = preprocess(src);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert_eq!(p.directives.len(), 1);
    assert_eq!(p.removed, vec![Span { start: 0, end: 26 }]);
}

#[test]
fn frontmatter_removed_before_directive_scan() {
    let src = "---\n# not scanned: %%{init: 1}%%\n---\n%%{wrap}%%\nA\n";
    let p = preprocess(src);
    assert!(p.wrap, "expected p.wrap; observed p.wrap={:?}", p.wrap);
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert_eq!(p.directives.len(), 1);
    assert!(
        !p.removed.iter().any(|s| s.start == 4),
        "expected !p.removed.iter().any(|s| s.start == 4); observed !p.removed.iter().any(|s| s.start == 4)={:?}",
        !p.removed.iter().any(|s| s.start == 4)
    );
}

#[test]
fn preprocess_unclosed_unknown_directives_are_ignored() {
    for src in ["%%{", "%%{\n", "%%{ini\tt"] {
        let p = preprocess(src);
        assert!(
            p.diagnostics.is_empty(),
            "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
            p.diagnostics
        );
        assert_eq!(
            p.removed,
            vec![Span {
                start: 0,
                end: src.len()
            }]
        );
    }
}

#[test]
fn preprocess_frontmatter_closing_newline_at_source_end() {
    let src = "---\nconfig: {}\n---\n";
    let p = preprocess(src);
    assert!(
        p.frontmatter.is_some(),
        "expected p.frontmatter.is_some(); observed p.frontmatter={:?}",
        p.frontmatter
    );
    assert!(
        p.diagnostics.is_empty(),
        "expected p.diagnostics.is_empty(); observed p.diagnostics={:?}",
        p.diagnostics
    );
    assert_eq!(
        p.removed,
        vec![Span {
            start: 0,
            end: src.len()
        }]
    );
}

#[test]
fn removed_spans_stay_sorted_and_disjoint() {
    let src = "---\n%% x\n---\n%% y\n%%{wrap}%%\nA\n";
    let p = preprocess(src);
    assert!(p.wrap, "expected p.wrap; observed p.wrap={:?}", p.wrap);
    let starts: Vec<usize> = p.removed.iter().map(|s| s.start).collect();
    let mut sorted = starts.clone();
    sorted.sort();
    assert_eq!(starts, sorted);
    for w in p.removed.windows(2) {
        assert!(w[1].start >= w[0].end, "overlap {w:?}");
    }
}

#[test]
fn diagnostics_propagate_from_frontmatter_body() {
    let src = "---\n\ta: 1\n---\nA\n";
    let p = preprocess(src);
    check(
        &p.diagnostics,
        C_MALFORMED,
        "tab in indentation",
        Span { start: 4, end: 5 },
    );
}

#[path = "preprocess/span_tests.rs"]
mod span_tests;
