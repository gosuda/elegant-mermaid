use super::ast::{Expression, MetaKind, Notation};
use super::lexer::lex;
use super::parse;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

fn kinds(source: &str, notation: Notation) -> Vec<String> {
    lex(source, &[], notation)
        .into_iter()
        .map(|token| token.kind)
        .collect()
}

#[test]
fn notation_follows_the_header_with_case_folding() {
    let cases = [
        ("railroad-beta\n", Notation::Constructor),
        ("RAILROAD-EBNF-BETA\n", Notation::Ebnf),
        ("  \n\tRailroad-Abnf-Beta\n", Notation::Abnf),
        ("railroad-peg-beta", Notation::Peg),
        ("flowchart\n", Notation::Constructor),
    ];
    for (source, want) in cases {
        assert_eq!(parse(source, &[]).document.notation, want, "{source:?}");
    }
}

#[test]
fn constructor_tokens() {
    assert_eq!(
        kinds(
            "railroad-beta\nr = optional(terminal(\"a\")) ;",
            Notation::Constructor
        ),
        [
            "HEADER", "ID", "=", "optional", "(", "terminal", "(", "STRING", ")", ")", ";", "EOF"
        ]
    );
}

#[test]
fn keyword_prefix_is_an_identifier() {
    assert_eq!(
        kinds("railroad-beta\nsequencex = x ;", Notation::Constructor),
        ["HEADER", "ID", "=", "ID", ";", "EOF"]
    );
}

#[test]
fn ebnf_special_needs_a_closing_question_mark_before_the_semicolon() {
    assert_eq!(
        kinds("railroad-ebnf-beta\nr = ? x ? ;", Notation::Ebnf),
        ["HEADER", "ID", "=", "SPECIAL", ";", "EOF"]
    );
    assert_eq!(
        kinds("railroad-ebnf-beta\nr = a ? ;", Notation::Ebnf),
        ["HEADER", "ID", "=", "ID", "?", ";", "EOF"]
    );
}

#[test]
fn abnf_numeric_values_and_repeats() {
    assert_eq!(
        kinds("railroad-abnf-beta\nr = 1*3a %x41-5A 2b ;", Notation::Abnf),
        [
            "HEADER",
            "ID",
            "=",
            "REPEAT",
            "ID",
            "NUMVAL",
            "EXACT_REPEAT",
            "ID",
            ";",
            "EOF"
        ]
    );
}

#[test]
fn peg_comment_and_operators() {
    assert_eq!(
        kinds("railroad-peg-beta\nr <- &a b? # c\n ;", Notation::Peg),
        ["HEADER", "ID", "<-", "&", "ID", "ID", "?", ";", "EOF"]
    );
}

#[test]
fn unterminated_openers_become_one_token_to_the_end() -> Result<(), &'static str> {
    let source = "railroad-beta\nr = terminal(\"abc";
    let tokens = lex(source, &[], Notation::Constructor);
    let last = tokens
        .iter()
        .rev()
        .nth(1)
        .ok_or("no token before the end marker")?;
    assert_eq!(last.kind, "UNTERMINATED");
    assert_eq!(last.text, "\"");
    assert_eq!(
        last.span,
        Span {
            start: source.find('"').unwrap_or(0),
            end: source.len()
        }
    );
    Ok(())
}

#[test]
fn rule_and_header_spans() -> Result<(), &'static str> {
    let source = "railroad-beta\nr = terminal(\"a\") ;\n";
    let document = parse(source, &[]).document;
    assert_eq!(document.header.span, Span { start: 0, end: 13 });
    assert_eq!(
        document.span,
        Span {
            start: 0,
            end: source.len()
        }
    );
    let [rule] = document.rules.as_slice() else {
        return Err("expected one rule");
    };
    assert_eq!(rule.name.text, "r");
    assert_eq!(rule.index, 0);
    assert_eq!(rule.span, Span { start: 14, end: 33 });
    let Expression::RailroadTerminal(terminal) = &rule.body else {
        return Err("body is not a terminal");
    };
    assert_eq!(terminal.value.text, "a");
    assert_eq!(terminal.span, Span { start: 18, end: 31 });
    Ok(())
}

#[test]
fn meta_statements_precede_rules() {
    let source = "railroad-beta\ntitle T\naccTitle: A\naccDescr: D\nr = terminal(\"a\") ;\n";
    let document = parse(source, &[]).document;
    let got: Vec<(MetaKind, &str)> = document
        .meta
        .iter()
        .map(|meta| (meta.kind, meta.value.as_str()))
        .collect();
    assert_eq!(
        got,
        [
            (MetaKind::Title, "T"),
            (MetaKind::AccTitle, "A"),
            (MetaKind::AccDescr, "D")
        ]
    );
}

#[test]
fn removed_spans_are_blank_to_the_lexer_and_cut_from_token_text() {
    let source = "railroad-beta\n%%{init: {}}%%\nr = terminal(\"a\") ;\n";
    let prep = preprocess(source);
    let parsed = parse(source, &prep.removed);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.rules.len(), 1);
}

#[test]
fn recovery_continues_after_a_broken_rule() {
    let source = "railroad-beta\nbad = sequence( ;\nr = terminal(\"a\") ;\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.document.rules.len(), 1);
    assert_eq!(parsed.document.rules[0].name.text, "r");
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, "railroad/unexpected-token");
}

#[test]
fn spans_stay_on_character_boundaries_for_multibyte_text() {
    let source = "railroad-beta\nr = terminal(\"é\u{1F600}\") ; ü\n";
    let parsed = parse(source, &[]);
    for diagnostic in &parsed.diagnostics {
        assert!(source.is_char_boundary(diagnostic.span.start));
        assert!(source.is_char_boundary(diagnostic.span.end));
    }
    assert_eq!(parsed.document.rules.len(), 1);
}
