use super::ast::{Start, StatementKind};
use super::parse;
use crate::source::Span;
use crate::syntax::preprocess::preprocess;

type Check = Result<(), &'static str>;

fn parse_text(text: &str) -> super::parser::Parsed {
    let removed = preprocess(text).removed;
    parse(text, &removed)
}

fn statements(start: &Start) -> Vec<&StatementKind> {
    start
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref().map(|s| &s.kind))
        .collect()
}

#[test]
fn full_statements() -> Check {
    let src = "venn-beta\n  title Overlap\n  set A[\"Alpha\"]:20\n    text \"x\"\n  set B\n  union A,B[\"AB\"]:3\n  style A fill:#ff6b6b, color:rgb(1, 2, 3)\n";
    let parsed = parse_text(src);
    assert!(parsed.diagnostics.is_empty());
    let kinds = statements(&parsed.document);
    assert_eq!(kinds.len(), 6);
    let StatementKind::Title(title) = kinds[0] else {
        return Err("not a title");
    };
    assert_eq!(title.token.text, "title Overlap");
    let StatementKind::Set(set) = kinds[1] else {
        return Err("not a set");
    };
    assert_eq!(set.id.text, "A");
    assert_eq!(set.label.as_ref().map(|l| l.text.as_str()), Some("Alpha"));
    assert_eq!(set.size.as_ref().map(|n| n.text.as_str()), Some("20"));
    let StatementKind::IndentedText(text) = kinds[2] else {
        return Err("not an indented text");
    };
    assert_eq!(text.tail.id.text, "\"x\"");
    let StatementKind::Union(union) = kinds[4] else {
        return Err("not a union");
    };
    assert_eq!(union.ids.ids.len(), 2);
    let StatementKind::Style(style) = kinds[5] else {
        return Err("not a style");
    };
    assert_eq!(style.styles.fields.len(), 2);
    let first = style.styles.fields[0]
        .value
        .tokens
        .as_ref()
        .ok_or("no tokens")?;
    assert_eq!(first.tokens[0].text, "#ff6b6b");
    let second = style.styles.fields[1]
        .value
        .tokens
        .as_ref()
        .ok_or("no tokens")?;
    assert_eq!(second.tokens[0].text, "rgb(1, 2, 3)");
    Ok(())
}

#[test]
fn title_ends_at_every_line_ending() -> Check {
    for eol in ["\n", "\r\n", "\r"] {
        let src = format!("venn-beta{eol}  title Overlap{eol}  set A{eol}  set B{eol}");
        let parsed = parse_text(&src);
        assert!(parsed.diagnostics.is_empty(), "{eol:?}");
        let kinds = statements(&parsed.document);
        assert_eq!(kinds.len(), 3, "{eol:?}");
        let StatementKind::Title(title) = kinds[0] else {
            return Err("not a title");
        };
        assert_eq!(title.token.text, "title Overlap", "{eol:?}");
    }
    Ok(())
}

#[test]
fn several_statements_share_a_line() {
    let parsed = parse_text("venn-beta set A set B union A,B\n");
    assert!(parsed.diagnostics.is_empty());
    assert_eq!(statements(&parsed.document).len(), 3);
}

#[test]
fn keywords_require_a_word_boundary() {
    for src in [
        "venn-beta\n  setA\n",
        "venn-beta\n  set A\n  stylea fill:red\n",
        "venn-beta\n  set A\n  set B\n  unionA,B\n",
    ] {
        let parsed = parse_text(src);
        assert_eq!(
            parsed.diagnostics.first().map(|d| d.code),
            Some("venn/unknown-statement"),
            "{src}"
        );
    }
}

#[test]
fn indented_text_needs_indent_mode() -> Check {
    let parsed = parse_text("venn-beta\n  set A\n  text x\n\n  text y\n");
    assert!(parsed.diagnostics.is_empty());
    let kinds = statements(&parsed.document);
    assert_eq!(kinds.len(), 3);
    assert!(matches!(kinds[2], StatementKind::IndentedText(_)));
    let parsed = parse_text("venn-beta\n  set A\n  style A fill:red\n  text A x\n");
    assert!(parsed.diagnostics.is_empty());
    let StatementKind::Text(explicit) = statements(&parsed.document)[2] else {
        return Err("not an explicit text");
    };
    assert_eq!(explicit.id.text, "x");
    Ok(())
}

#[test]
fn comments_inside_statements() {
    let parsed = parse_text("venn-beta\n  set A %% note\n%% whole line\n  text x\n");
    assert!(parsed.diagnostics.is_empty());
    assert_eq!(statements(&parsed.document).len(), 2);
    assert!(
        !parse_text("venn-beta\n  set A%% note\n")
            .diagnostics
            .is_empty()
    );
}

#[test]
fn bracket_labels_are_trimmed_or_quoted() -> Check {
    let parsed = parse_text("venn-beta\n  set A[ one two ]\n  set B[\"  two ]\"]\n");
    assert!(parsed.diagnostics.is_empty());
    let kinds = statements(&parsed.document);
    let (StatementKind::Set(a), StatementKind::Set(b)) = (kinds[0], kinds[1]) else {
        return Err("not sets");
    };
    assert_eq!(a.label.as_ref().map(|l| l.text.as_str()), Some("one two"));
    assert_eq!(b.label.as_ref().map(|l| l.text.as_str()), Some("  two ]"));
    Ok(())
}

#[test]
fn diagnostics() {
    let rows: &[(&str, &str, &str, &str, usize, usize)] = &[
        (
            "missing identifier",
            "venn-beta\n  set",
            "venn/unexpected-token",
            "unexpected end of input, expected one of: IDENTIFIER, STRING",
            15,
            15,
        ),
        (
            "missing size",
            "venn-beta\n  set A:",
            "venn/unexpected-token",
            "unexpected end of input, expected one of: NUMERIC",
            18,
            18,
        ),
        (
            "unknown",
            "venn-beta\n  foo bar\n  set A\n",
            "venn/unknown-statement",
            "unknown statement foo",
            12,
            19,
        ),
        (
            "open label",
            "venn-beta\n  set A[\"x\n",
            "venn/unterminated",
            "unterminated [",
            17,
            21,
        ),
        (
            "open string",
            "venn-beta\n  set \"abc\n",
            "venn/unterminated",
            "unterminated \"",
            16,
            21,
        ),
        (
            "text id",
            "venn-beta\n  set A\n  style A fill:red\n  text x\n",
            "venn/unexpected-token",
            "unexpected \n, expected one of: COMMA, IDENTIFIER, NUMERIC, STRING",
            45,
            46,
        ),
        (
            "style value",
            "venn-beta\n  set A\n  style A fill:,\n",
            "venn/unexpected-token",
            "unexpected ,, expected one of: HEXCOLOR, IDENTIFIER, NUMERIC, RGBACOLOR, RGBCOLOR, STRING",
            33,
            34,
        ),
        (
            "invalid byte",
            "venn-beta\n  set A;\n",
            "venn/unknown-statement",
            "unknown statement ;",
            17,
            18,
        ),
    ];
    for (name, src, code, message, start, end) in rows {
        let parsed = parse_text(src);
        let first = parsed.diagnostics.first();
        assert_eq!(first.map(|d| d.code), Some(*code), "{name}");
        assert_eq!(first.map(|d| d.message.as_str()), Some(*message), "{name}");
        assert_eq!(
            first.map(|d| d.span),
            Some(Span {
                start: *start,
                end: *end
            }),
            "{name}"
        );
    }
}

#[test]
fn recovery_continues_after_an_unexpected_token() {
    let parsed = parse_text("venn-beta\n  set\n  set A\n");
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(statements(&parsed.document).len(), 1);
}

#[test]
fn removed_spans_are_invisible_to_the_lexer() {
    let parsed =
        parse_text("---\ntitle: front\n---\nvenn-beta\n  set A\n  %%{init: {}}%%\n  text x\n");
    assert!(parsed.diagnostics.is_empty());
    assert_eq!(statements(&parsed.document).len(), 2);
}
