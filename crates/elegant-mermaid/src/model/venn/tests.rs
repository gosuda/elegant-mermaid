use super::{Model, parse_and_resolve, thousandths};
use crate::diag::Diagnostic;
use crate::scene::DumpValue;
use crate::syntax::preprocess::preprocess;

fn resolve_text(text: &str) -> (Model, Vec<Diagnostic>) {
    let removed = preprocess(text).removed;
    parse_and_resolve(text, &removed)
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
    diagnostics.iter().map(|d| d.code).collect()
}

#[test]
fn thousandths_rounds_half_away_from_zero() {
    for (literal, want) in [
        ("1", 1000),
        ("0.0005", 1),
        ("0.0004", 0),
        ("-0.0005", -1),
        ("2.5", 2500),
        (".5", 500),
        ("007", 7000),
    ] {
        assert_eq!(thousandths(literal), want, "{literal}");
    }
}

#[test]
fn sets_keep_first_span_and_last_value() {
    let (model, diagnostics) =
        resolve_text("venn-beta\n  set A:2\n  set B\n  set A[\"Again\"]:3\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let sets = model.sets();
    assert_eq!(sets.len(), 2);
    assert_eq!(sets[0].display, "Again");
    assert_eq!(sets[0].size, 3000);
    assert_eq!(sets[0].span.start, 12);
}

#[test]
fn default_sizes_follow_the_set_count() {
    let (model, _) = resolve_text("venn-beta\n  set A\n  set B\n  union A,B\n");
    let sizes: Vec<i64> = model.subsets.iter().map(|s| s.size).collect();
    assert_eq!(sizes, [10000, 10000, 2500]);
}

#[test]
fn indented_text_attaches_to_the_latest_subset() {
    let (model, diagnostics) =
        resolve_text("venn-beta\n  set A\n    text one\n  set B\n    text two\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.texts.len(), 2);
    assert_eq!(model.texts[0].sets, ["A"]);
    assert_eq!(model.texts[1].sets, ["B"]);
}

#[test]
fn explicit_text_sorts_its_targets() {
    let (model, diagnostics) =
        resolve_text("venn-beta\n  set A\n  set B\n  title t\n  text B,A hello\n");
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.texts[0].sets, ["A", "B"]);
}

#[test]
fn set_count_diagnostics() {
    let (_, none) = resolve_text("venn-beta\n");
    assert_eq!(codes(&none), ["venn/no-sets"]);
    let (_, many) = resolve_text("venn-beta\n  set A\n  set B\n  set C\n  set D\n");
    assert_eq!(codes(&many), ["venn/too-many-sets"]);
    assert_eq!(many[0].span.start, 36);
}

#[test]
fn union_rules() {
    let (_, short) = resolve_text("venn-beta\n  set A\n  union A\n");
    assert_eq!(codes(&short), ["venn/union-requires-multiple-identifiers"]);
    let (_, unknown) = resolve_text("venn-beta\n  set A\n  union A,B,C\n");
    assert_eq!(codes(&unknown), ["venn/unknown-set-identifier"]);
    assert_eq!(unknown[0].related.len(), 1);
    assert_eq!(unknown[0].message, "unknown set identifier: B, C");
}

#[test]
fn indented_text_before_any_set_is_an_unexpected_token() {
    let (_, diagnostics) = resolve_text("venn-beta\n    text one\n  set A\n");
    assert_eq!(codes(&diagnostics), ["venn/unexpected-token"]);
}

#[test]
fn title_and_config_are_read() {
    let src = "---\ntitle: Front #amp;\nconfig:\n  venn:\n    width: 400\n---\nvenn-beta\n  title Inline\n  set A\n";
    let (model, diagnostics) = resolve_text(src);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.title, "Inline");
    assert_eq!(model.config.get("width"), Some(&DumpValue::Integer(400)));
}

#[test]
fn entities_decode_in_labels() {
    let (model, _) = resolve_text("venn-beta\n  set A[\"a #38; b\"]\n");
    assert_eq!(model.sets()[0].display, "a & b");
}

#[test]
fn style_entries_keep_the_last_value() {
    let (model, _) = resolve_text("venn-beta\n  set A\n  style A fill:#ff0000, fill:#00ff00\n");
    assert_eq!(model.styles[0].entries.len(), 1);
    assert_eq!(model.styles[0].entries[0].value, "#00ff00");
}
