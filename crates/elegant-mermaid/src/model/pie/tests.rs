use super::{Model, OVERFLOW, resolve, thousandths};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::pie::parse;
use crate::syntax::preprocess::preprocess;

fn resolved(text: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(text).removed;
    let parsed = parse(text, &removed);
    resolve(text, &parsed.document)
}

fn pairs(model: &Model) -> Vec<(String, i64, usize)> {
    model
        .sections
        .iter()
        .map(|s| (s.label.clone(), s.value, s.index))
        .collect()
}

fn pair(label: &str, value: i64, index: usize) -> (String, i64, usize) {
    (label.to_owned(), value, index)
}

#[test]
fn sections_keep_declaration_order_and_thousandths() {
    let (model, diagnostics) = resolved(
        "pie showData\n\"B\" : 5\n\"A\" : 42.96\n\"C\" : 0\n\"D\" : 0.0005\n\"E\" : 1.2345\n",
    );
    assert!(diagnostics.is_empty());
    assert!(model.show_data);
    assert_eq!(
        pairs(&model),
        vec![
            pair("B", 5000, 0),
            pair("A", 42960, 1),
            pair("C", 0, 2),
            pair("D", 1, 3),
            pair("E", 1235, 4)
        ]
    );
}

#[test]
fn duplicate_label_keeps_first_value_and_position() {
    let (model, diagnostics) = resolved("pie\n\"a\" : 1\n\"b\" : 2\n\"a\" : 9\n\"c\" : 3\n");
    assert!(diagnostics.is_empty());
    assert_eq!(
        pairs(&model),
        vec![pair("a", 1000, 0), pair("b", 2000, 1), pair("c", 3000, 3)]
    );
}

#[test]
fn negative_values_are_rejected_before_duplicate_elimination() {
    let (model, diagnostics) =
        resolved("pie\n\"a\" : 1\n\"a\" : -2\n\"b\" : -0.0004\n\"c\" : -0\n\"d\" : -0.0\n");
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].code, "pie/negative-value");
    assert_eq!(diagnostics[0].message, "slice a has negative value -2");
    assert_eq!(diagnostics[0].span, Span { start: 18, end: 20 });
    assert_eq!(diagnostics[1].message, "slice b has negative value -0.0004");
    assert_eq!(
        pairs(&model),
        vec![pair("a", 1000, 0), pair("c", 0, 3), pair("d", 0, 4)]
    );
}

#[test]
fn overflowing_value_saturates_for_the_layout_to_reject() {
    let (model, diagnostics) = resolved("pie\n\"a\" : 99999999999\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].value, OVERFLOW);
}

#[test]
fn labels_decode_entities_and_escapes() {
    let (model, diagnostics) = resolved("pie\n\"a #35; b #amp; #zzz; #0;\" : 1\n\"q\\\"r\" : 2\n");
    assert!(diagnostics.is_empty());
    assert_eq!(model.sections[0].label, "a # b & #zzz; #0;");
    assert_eq!(model.sections[1].label, "q\"r");
}

#[test]
fn last_metadata_wins_and_empty_is_ignored() {
    let (model, _) = resolved(
        "pie\ntitle One\ntitle Two\naccTitle: t1\naccTitle: t2\naccDescr: d1\naccDescr: d2\n",
    );
    assert_eq!(model.title, "Two");
    assert_eq!(model.acc_title, "t2");
    assert_eq!(model.acc_descr, "d2");
    let (model, _) = resolved("pie\ntitle One\ntitle\naccTitle: t\naccTitle:\n");
    assert!(model.title.is_empty());
    assert!(model.acc_title.is_empty());
}

#[test]
fn frontmatter_title_is_overridden_by_body_title() {
    assert_eq!(
        resolved("---\ntitle: Front\n---\npie\n\"a\" : 1\n").0.title,
        "Front"
    );
    assert_eq!(
        resolved("---\ntitle: Front\n---\npie\ntitle Body\n")
            .0
            .title,
        "Body"
    );
    assert_eq!(
        resolved("---\ntitle: Front\n---\npie\ntitle\n").0.title,
        "Front"
    );
}

#[test]
fn honoured_config() {
    type ConfigCase<'a> = (&'a str, &'a str, Vec<(&'a str, i64)>);
    let cases: [ConfigCase<'_>; 9] = [
        ("none", "pie\n", vec![]),
        (
            "frontmatter",
            "---\nconfig:\n  pie:\n    textPosition: 0.5\n    donutHole: 0.4\n---\npie\n",
            vec![("donutHole", 400), ("textPosition", 500)],
        ),
        (
            "directive",
            "%%{init: {\"pie\": {\"textPosition\": 0.9}}}%%\npie\n",
            vec![("textPosition", 900)],
        ),
        (
            "directive overrides frontmatter",
            "---\nconfig:\n  pie:\n    textPosition: 0.2\n---\n%%{init: {\"pie\": {\"textPosition\": 0.3}}}%%\npie\n",
            vec![("textPosition", 300)],
        ),
        (
            "out of range is ignored",
            "---\nconfig:\n  pie:\n    textPosition: 1.5\n    donutHole: 0.95\n---\npie\n",
            vec![],
        ),
        (
            "negative is ignored",
            "---\nconfig:\n  pie:\n    donutHole: -0.1\n---\npie\n",
            vec![],
        ),
        (
            "not a number is ignored",
            "---\nconfig:\n  pie:\n    donutHole: wide\n---\npie\n",
            vec![],
        ),
        (
            "ignored keys are not kept",
            "---\nconfig:\n  pie:\n    legendPosition: bottom\n    highlightSlice: hover\n---\npie\n",
            vec![],
        ),
        (
            "zero is kept",
            "---\nconfig:\n  pie:\n    textPosition: 0\n---\npie\n",
            vec![("textPosition", 0)],
        ),
    ];
    for (name, source, want) in cases {
        let (model, _) = resolved(source);
        let got: Vec<(&str, i64)> = model.config.iter().map(|(k, v)| (k.as_str(), *v)).collect();
        assert_eq!(got, want, "{name}");
    }
}

#[test]
fn thousandths_rounding_and_sign() {
    for (literal, value, negative) in [
        ("0", 0, false),
        ("10", 10000, false),
        ("0.0005", 1, false),
        ("0.0004", 0, false),
        ("1.9995", 2000, false),
        ("-0", 0, false),
        ("-0.000", 0, false),
        ("-0.0004", 0, true),
        ("-7", 7000, true),
        ("+2.5", 2500, false),
    ] {
        assert_eq!(thousandths(literal), (value, negative), "{literal}");
    }
}
