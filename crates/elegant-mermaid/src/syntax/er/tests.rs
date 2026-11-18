use super::lexer::lex;
use crate::source::Span;

#[test]
fn er_attribute_generics_greed_and_multiline_backticks() -> Result<(), &'static str> {
    let tokens = lex("erDiagram\nA { List~T~ value\n`line\r\nname` item }", &[]);
    let words: Vec<_> = tokens
        .iter()
        .filter(|t| t.kind == "ATTRIBUTE_WORD")
        .map(|t| t.text.as_ref())
        .collect();
    assert_eq!(words, ["List~T~", "value", "line\r\nname", "item"]);
    let quoted = tokens
        .iter()
        .find(|t| t.text == "line\r\nname")
        .ok_or("backtick token")?;
    assert_eq!(quoted.span, Span { start: 28, end: 40 });
    Ok(())
}

#[test]
fn er_cardinality_spellings_follow_ordered_rules() -> Result<(), &'static str> {
    for (text, expected) in [
        ("one or zero", "ZERO_OR_ONE"),
        ("one or more", "ONE_OR_MORE"),
        ("one or many", "ONE_OR_MORE"),
        ("1+", "ONE_OR_MORE"),
        ("|o", "ZERO_OR_ONE"),
        ("zero or one", "ZERO_OR_ONE"),
        ("zero or more", "ZERO_OR_MORE"),
        ("zero or many", "ZERO_OR_MORE"),
        ("0+", "ZERO_OR_MORE"),
        ("}o", "ZERO_OR_MORE"),
        ("many(0)", "ZERO_OR_MORE"),
        ("many(1)", "ONE_OR_MORE"),
        ("many", "ZERO_OR_MORE"),
        ("}|", "ONE_OR_MORE"),
        ("one", "ONLY_ONE"),
        ("only one", "ONLY_ONE"),
        ("||", "ONLY_ONE"),
        ("o|", "ZERO_OR_ONE"),
        ("o{", "ZERO_OR_MORE"),
        ("|{", "ONE_OR_MORE"),
    ] {
        let tokens = lex(text, &[]);
        let token = tokens.first().ok_or("cardinality token")?;
        assert_eq!(
            (token.kind, token.text.as_ref(), token.span),
            (
                expected,
                text,
                Span {
                    start: 0,
                    end: text.len()
                }
            )
        );
    }
    Ok(())
}

#[test]
fn er_numeric_entity_one_uses_non_consuming_lookahead() -> Result<(), &'static str> {
    let tokens = lex("1\n1 A\n1 2\n1--\n1..\n1.-\n1-.\n1.25\n12", &[]);
    let numbers: Vec<_> = tokens
        .iter()
        .filter(|t| matches!(t.kind, "ONLY_ONE" | "ENTITY_ONE" | "NUM" | "DECIMAL_NUM"))
        .map(|t| (t.kind, t.text.as_ref()))
        .collect();
    assert_eq!(
        numbers,
        [
            ("ONLY_ONE", "1"),
            ("ONLY_ONE", "1"),
            ("ONLY_ONE", "1"),
            ("NUM", "2"),
            ("ONLY_ONE", "1"),
            ("ONLY_ONE", "1"),
            ("ONLY_ONE", "1"),
            ("ONLY_ONE", "1"),
            ("DECIMAL_NUM", "1.25"),
            ("ENTITY_ONE", "1"),
            ("NUM", "2"),
        ]
    );
    assert!(
        tokens
            .iter()
            .any(|t| t.kind == "UNICODE_TEXT" && t.text == "A"),
        "cardinality lookahead must leave the following entity token unconsumed: {tokens:?}"
    );
    Ok(())
}

#[test]
fn er_removed_spans_are_skipped_without_rebasing() -> Result<(), &'static str> {
    let source = "ignored\nerDiagram\rA";
    let tokens = lex(source, &[Span { start: 0, end: 8 }]);
    let header = tokens.first().ok_or("header")?;
    assert_eq!(
        (header.kind, header.span),
        ("ER_DIAGRAM", Span { start: 8, end: 17 })
    );
    assert!(
        tokens
            .iter()
            .all(|t| source.is_char_boundary(t.span.start) && source.is_char_boundary(t.span.end)),
        "skipping removed text must preserve UTF-8-aligned source spans: {tokens:?}"
    );
    Ok(())
}

#[test]
fn er_single_mode_key_and_keyword_prefix_precedence() -> Result<(), &'static str> {
    let tokens = lex(
        "erDiagram\nA { PKfoo id FK,UK\n}\nstyleNode fill:red\n",
        &[],
    );
    let fields: Vec<_> = tokens
        .iter()
        .filter(|token| matches!(token.kind, "ATTRIBUTE_WORD" | "ATTRIBUTE_KEY"))
        .map(|token| (token.kind, token.text.as_ref()))
        .collect();
    assert_eq!(
        fields,
        [
            ("ATTRIBUTE_WORD", "PKfoo"),
            ("ATTRIBUTE_WORD", "id"),
            ("ATTRIBUTE_KEY", "FK"),
            ("ATTRIBUTE_KEY", "UK"),
        ]
    );
    assert!(
        tokens
            .iter()
            .any(|token| token.kind == "STYLE" && token.text == "style"),
        "the style keyword must match before the longer entity-name rule: {tokens:?}"
    );
    assert!(
        tokens
            .iter()
            .any(|token| token.kind == "STYLE_TEXT" && token.text == "Node"),
        "matching the style prefix must leave its suffix in style mode: {tokens:?}"
    );
    Ok(())
}

#[test]
fn er_textual_relationship_operators_do_not_split_identifiers() -> Result<(), &'static str> {
    let tokens = lex("TOP to optionally to to_customer to9 today", &[]);
    assert_eq!(
        tokens
            .iter()
            .map(|token| (token.kind, token.text.as_ref()))
            .collect::<Vec<_>>(),
        [
            ("UNICODE_TEXT", "TOP"),
            ("IDENTIFYING", "to"),
            ("NON_IDENTIFYING", "optionally to"),
            ("UNICODE_TEXT", "to_customer"),
            ("UNICODE_TEXT", "to9"),
            ("UNICODE_TEXT", "today"),
            ("EOF", ""),
        ]
    );
    assert_eq!(
        tokens.first().ok_or("TOP token")?.span,
        Span { start: 0, end: 3 }
    );
    Ok(())
}
