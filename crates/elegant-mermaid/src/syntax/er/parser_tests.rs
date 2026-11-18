use super::{
    ast::*,
    lexer::{MODES, lex},
    parse,
};
use crate::source::Span;

fn statements<'p, 'a>(parsed: &'p super::parser::Parsed<'a>) -> Vec<&'p Statement<'a>> {
    parsed
        .document
        .document
        .lines
        .iter()
        .filter_map(|line| line.statement.as_ref())
        .collect()
}

#[test]
fn er_header_empty_document_and_adjacent_declarations() -> Result<(), &'static str> {
    let empty = parse("erDiagram", &[]);
    assert!(
        empty.diagnostics.is_empty(),
        "an EOF-only header must parse: {:?}",
        empty.diagnostics
    );
    assert_eq!(empty.document.span, Span { start: 0, end: 9 });
    assert_eq!(empty.document.document.span, Span { start: 9, end: 9 });
    assert!(
        empty.document.document.lines.is_empty(),
        "an empty document must not synthesize lines: {:?}",
        empty.document.document.lines
    );
    let parsed = parse("erDiagram\nA B C{}", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 3);
    assert_eq!(nodes.first().ok_or("A")?.span, Span { start: 10, end: 11 });
    let StatementKind::Entity {
        attributes: Some(attributes),
        delimiters: Some((open, close)),
        ..
    } = &nodes.get(2).ok_or("C")?.kind
    else {
        return Err("empty block entity");
    };
    assert!(
        attributes.attributes.is_empty(),
        "an empty block must retain zero attributes: {:?}",
        attributes.attributes
    );
    assert_eq!(
        (*open, *close),
        (Span { start: 15, end: 16 }, Span { start: 16, end: 17 })
    );
    Ok(())
}

#[test]
fn er_alias_and_inline_classes_preserve_borrowed_identity() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA[\"é\"]:::red,blue {}", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Entity {
        name,
        alias: Some(alias),
        classes: Some(classes),
        attributes: Some(_),
        ..
    } = &nodes.first().ok_or("entity")?.kind
    else {
        return Err("entity with alias and classes");
    };
    assert_eq!(name.name, "A");
    assert_eq!(
        (alias.name.as_ref(), alias.span),
        ("é", Span { start: 12, end: 16 })
    );
    assert_eq!(
        classes
            .names
            .iter()
            .map(|t| t.text.as_ref())
            .collect::<Vec<_>>(),
        ["red", "blue"]
    );
    Ok(())
}

#[test]
fn er_attribute_modes_nullable_keys_and_comments() -> Result<(), &'static str> {
    let source = "erDiagram\nA {\n`custom type`? `first name` pk, FK,uk \"é\"\nint second\n}";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Entity {
        attributes: Some(attributes),
        ..
    } = &nodes.first().ok_or("entity")?.kind
    else {
        return Err("attribute block");
    };
    assert_eq!(attributes.attributes.len(), 2);
    let attribute = attributes.attributes.first().ok_or("attribute")?;
    assert_eq!(attribute.attribute_type.word.text, "custom type");
    assert_eq!(attribute.attribute_type.span, Span { start: 14, end: 28 });
    assert_eq!(attribute.name.word.text, "first name");
    assert_eq!(
        attribute
            .keys
            .as_ref()
            .ok_or("keys")?
            .keys
            .iter()
            .map(|k| k.value)
            .collect::<Vec<_>>(),
        ["PK", "FK", "UK"]
    );
    assert_eq!(attribute.comment.as_ref().ok_or("comment")?.text, "é");
    assert_eq!(
        MODES,
        [
            "INITIAL",
            "block",
            "block_bq",
            "acc_title",
            "acc_descr",
            "acc_descr_multiline",
            "style"
        ]
    );
    Ok(())
}

#[test]
fn er_relationship_retains_each_marker_class_and_line_kind() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA:::red ||..o{ B:::blue: \"has many\"", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Relationship {
        from,
        relation,
        to,
        role,
        from_classes: Some(_),
        to_classes: Some(_),
        ..
    } = &nodes.first().ok_or("relationship")?.kind
    else {
        return Err("relationship");
    };
    assert_eq!(
        (from.name.as_ref(), to.name.as_ref(), role.label.as_ref()),
        ("A", "B", "has many")
    );
    assert_eq!(
        (relation.left.kind, relation.right.kind),
        (CardinalityKind::OnlyOne, CardinalityKind::ZeroOrMore)
    );
    assert!(
        !relation.relation_type.identifying,
        "a dotted relationship must remain non-identifying: {:?}",
        relation.relation_type
    );
    assert_eq!(relation.span, Span { start: 18, end: 24 });
    Ok(())
}

#[test]
fn er_line_spellings_and_parent_marker_parse() -> Result<(), &'static str> {
    for line in ["..", "--", "to", "optionally to", ".-", "-."] {
        let source = format!("erDiagram\nA ||{line}|| B: r");
        let parsed = parse(&source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let nodes = statements(&parsed);
        let StatementKind::Relationship { relation, .. } = &nodes.first().ok_or("relation")?.kind
        else {
            return Err("relationship");
        };
        assert_eq!(relation.left.kind, CardinalityKind::OnlyOne);
        assert_eq!(
            relation.relation_type.identifying,
            matches!(line, "--" | "to")
        );
    }
    Ok(())
}

#[test]
fn er_direction_consumes_prefix_suffix_with_tb_precedence() -> Result<(), &'static str> {
    let source =
        "erDiagram\nnoise direction LR then direction TB suffix\rtrailingdirection BTsuffix\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Direction(direction) = &nodes.first().ok_or("direction")?.kind else {
        return Err("direction");
    };
    assert_eq!(
        (direction.value, direction.span),
        ("TB", Span { start: 10, end: 53 })
    );
    assert_eq!(nodes.len(), 2);
    Ok(())
}

#[test]
fn er_style_directives_keep_components_and_semicolon_mode() -> Result<(), &'static str> {
    let source = "erDiagram\nclassDef red,blue fill:#abc,color:red;\nclass A,B red,blue\nstyle A,B stroke:#123\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 3);
    let StatementKind::ClassDef(definition) = &nodes.first().ok_or("classdef")?.kind else {
        return Err("classdef");
    };
    assert_eq!(definition.ids.names.len(), 2);
    assert_eq!(definition.styles.styles.len(), 2);
    assert_eq!(
        definition
            .styles
            .styles
            .first()
            .ok_or("style")?
            .components
            .iter()
            .map(|c| c.token.text.as_ref())
            .collect::<Vec<_>>(),
        ["fill", ":", "#", "abc"]
    );
    let tokens = lex("style A fill:red;class B red\nC", &[]);
    assert!(
        tokens
            .iter()
            .any(|t| t.kind == "STYLE_TEXT" && t.text == "class"),
        "semicolon must retain style mode for the following class spelling: {tokens:?}"
    );
    assert!(
        tokens
            .iter()
            .any(|t| t.kind == "UNICODE_TEXT" && t.text == "C"),
        "newline must restore INITIAL mode for the following entity: {tokens:?}"
    );
    Ok(())
}

#[test]
fn er_accessibility_single_multiline_and_empty() -> Result<(), &'static str> {
    let source = "erDiagram\raccTitle: é\r\naccDescr: d\naccDescr {first\rsecond}\naccDescr {}";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let values: Vec<_> = nodes
        .iter()
        .filter_map(|s| match &s.kind {
            StatementKind::Accessibility { title, value } => Some((*title, value.text.as_ref())),
            _ => None,
        })
        .collect();
    assert_eq!(
        values,
        [
            (true, "é"),
            (false, "d"),
            (false, "first\rsecond"),
            (false, "")
        ]
    );
    assert_eq!(
        nodes.first().ok_or("title")?.span,
        Span { start: 10, end: 22 }
    );
    Ok(())
}

#[test]
fn er_nested_and_empty_subgraphs_retain_titles_and_documents() -> Result<(), &'static str> {
    let parsed = parse(
        "erDiagram\nsubgraph Outer[First Second]\nsubgraph Empty\nend\nA[Alias]\nend\nB",
        &[],
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 2);
    let StatementKind::Subgraph {
        header, document, ..
    } = &nodes.first().ok_or("outer")?.kind
    else {
        return Err("subgraph");
    };
    assert_eq!(
        header
            .title
            .as_ref()
            .ok_or("title")?
            .parts
            .iter()
            .map(|p| p.name.as_ref())
            .collect::<Vec<_>>(),
        ["First", "Second"]
    );
    let children: Vec<_> = document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(children.len(), 2);
    let StatementKind::Subgraph { document, .. } = &children.first().ok_or("empty")?.kind else {
        return Err("nested subgraph");
    };
    assert!(
        document.lines.is_empty(),
        "an empty nested subgraph must retain zero body lines: {:?}",
        document.lines
    );
    Ok(())
}

#[test]
fn er_unknown_statement_recovers_at_physical_lines() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\n@ junk\r\nB\rC", &[]);
    let error = parsed.diagnostics.first().ok_or("unknown error")?;
    assert_eq!(
        (error.code, error.message.as_str(), error.span),
        (
            "er/unknown-statement",
            "unknown statement @",
            Span { start: 10, end: 16 }
        )
    );
    assert_eq!(statements(&parsed).len(), 2);
    Ok(())
}

#[test]
fn er_bad_relationship_recovers_without_alias_endpoint() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA ||--|| B[Alias]: r\nC", &[]);
    let error = parsed.diagnostics.first().ok_or("unexpected error")?;
    assert_eq!(
        (error.code, error.message.as_str(), error.span),
        (
            "er/unexpected-token",
            "unexpected [, expected one of: COLON",
            Span { start: 20, end: 21 }
        )
    );
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 1);
    let StatementKind::Entity { name, .. } = &nodes.first().ok_or("surviving entity")?.kind else {
        return Err("entity");
    };
    assert_eq!(name.name, "C");
    Ok(())
}

#[test]
fn er_bad_attribute_recovers_inside_block_and_preserves_close() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA {\nint @\nstring good\n}\nB", &[]);
    let error = parsed.diagnostics.first().ok_or("attribute error")?;
    assert_eq!(
        (error.code, error.message.as_str(), error.span),
        (
            "er/unexpected-token",
            "unexpected @, expected one of: ATTRIBUTE_WORD",
            Span { start: 18, end: 19 }
        )
    );
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 2);
    let StatementKind::Entity {
        attributes: Some(attributes),
        ..
    } = &nodes.first().ok_or("entity")?.kind
    else {
        return Err("entity block");
    };
    assert_eq!(attributes.attributes.len(), 1);
    assert_eq!(
        attributes
            .attributes
            .first()
            .ok_or("good attribute")?
            .name
            .word
            .text,
        "good"
    );
    Ok(())
}

#[test]
fn er_unterminated_openers_report_one_exact_diagnostic() -> Result<(), &'static str> {
    for (source, start, message) in [
        ("erDiagram\n\"é", 10, "unterminated \""),
        ("erDiagram\nA { `é", 14, "unterminated `"),
        ("erDiagram\nA { int id", 12, "unterminated {"),
        ("erDiagram\nA { int id \"é", 21, "unterminated \""),
        ("erDiagram\naccDescr {é", 19, "unterminated {"),
        ("erDiagram\nsubgraph S\nA", 10, "unterminated subgraph"),
    ] {
        let parsed = parse(source, &[]);
        assert_eq!(
            parsed.diagnostics.len(),
            1,
            "{source}: {:?}",
            parsed.diagnostics
        );
        let error = parsed.diagnostics.first().ok_or("unterminated")?;
        assert_eq!(
            (error.code, error.message.as_str(), error.span),
            (
                "er/unterminated",
                message,
                Span {
                    start,
                    end: source.len()
                }
            )
        );
    }
    Ok(())
}

#[test]
fn er_level_sixty_five_stops_with_shared_limit() -> Result<(), &'static str> {
    let mut source = String::from("erDiagram\n");
    for _ in 0..65 {
        source.push_str("subgraph S\n");
    }
    for _ in 0..65 {
        source.push_str("end\n");
    }
    let parsed = parse(&source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let error = parsed.diagnostics.first().ok_or("limit diagnostic")?;
    assert_eq!(
        (error.code, error.message.as_str(), error.span),
        (
            "limit/nesting-depth",
            "nesting depth exceeds 64",
            Span {
                start: 714,
                end: 722
            }
        )
    );
    Ok(())
}

#[test]
fn er_parent_cardinality_uses_only_punctuation_lookahead() -> Result<(), &'static str> {
    for line in ["..", "--", ".-", "-."] {
        let source = format!("erDiagram\nA u{line}|| B: r");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let nodes = statements(&parsed);
        let StatementKind::Relationship { relation, .. } =
            &nodes.first().ok_or("relationship")?.kind
        else {
            return Err("relationship");
        };
        assert_eq!(relation.left.kind, CardinalityKind::MdParent);
        assert_eq!(relation.left.span, Span { start: 12, end: 13 });
    }
    let tokens = lex("user u|", &[]);
    assert_eq!(tokens.first().ok_or("user")?.kind, "UNICODE_TEXT");
    assert_eq!(tokens.get(1).ok_or("parent")?.kind, "MD_PARENT");
    Ok(())
}

#[test]
fn er_style_statement_spans_omit_terminating_separator() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nstyle A fill:red;\nclassDef red color:blue", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let first = nodes.first().ok_or("style")?;
    let StatementKind::Style(style) = &first.kind else {
        return Err("style");
    };
    assert_eq!(first.span, Span { start: 10, end: 26 });
    assert_eq!(style.span, first.span);
    let second = nodes.get(1).ok_or("classdef")?;
    let StatementKind::ClassDef(definition) = &second.kind else {
        return Err("classdef");
    };
    assert_eq!(second.span, Span { start: 28, end: 51 });
    assert_eq!(definition.span, second.span);
    Ok(())
}

#[test]
fn er_invalid_first_attribute_recovers_to_next_line() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA {\n@ bad\nint good\n}", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let error = parsed.diagnostics.first().ok_or("error")?;
    assert_eq!(
        (error.message.as_str(), error.span),
        (
            "unexpected @, expected one of: ATTRIBUTE_WORD",
            Span { start: 14, end: 15 },
        )
    );
    let nodes = statements(&parsed);
    let StatementKind::Entity {
        attributes: Some(attributes),
        ..
    } = &nodes.first().ok_or("entity")?.kind
    else {
        return Err("attribute block");
    };
    assert_eq!(attributes.attributes.len(), 1);
    assert_eq!(
        attributes
            .attributes
            .first()
            .ok_or("attribute")?
            .name
            .word
            .text,
        "good"
    );
    Ok(())
}

#[test]
fn er_bad_relationship_preserves_enclosing_subgraph_close() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nsubgraph S\nA ||-- end\nB", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let error = parsed.diagnostics.first().ok_or("error")?;
    assert_eq!(
        (error.code, error.message.as_str(), error.span),
        (
            "er/unexpected-token",
            "unexpected end\n, expected one of: MD_PARENT, ONE_OR_MORE, ONLY_ONE, ZERO_OR_MORE, ZERO_OR_ONE",
            Span { start: 28, end: 32 },
        )
    );
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 2);
    let StatementKind::Subgraph { document, .. } = &nodes.first().ok_or("scope")?.kind else {
        return Err("subgraph");
    };
    assert!(
        document.lines.iter().all(|line| line.statement.is_none()),
        "a malformed relationship must not leave a partial statement in its subgraph: {:?}",
        document.lines
    );
    Ok(())
}

#[test]
fn er_quoted_empty_role_and_quote_rule_precedence() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\nA ||--|| B: \"\"", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Relationship { role, .. } = &nodes.first().ok_or("relationship")?.kind
    else {
        return Err("relationship");
    };
    assert_eq!(
        (role.label.as_ref(), role.span),
        ("", Span { start: 22, end: 24 })
    );
    let tokens = lex("\"clean\" \"has%percent\" \"\"", &[]);
    assert_eq!(
        tokens.iter().map(|token| token.kind).collect::<Vec<_>>(),
        ["ENTITY_NAME", "WORD", "WORD", "EOF"]
    );
    Ok(())
}

#[test]
fn er_numeric_entity_names_and_adjacent_attribute_records_keep_text() -> Result<(), &'static str> {
    let parsed = parse("erDiagram\n1 ||--|| 42: r\n2.5 {int x string? y}\n1", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let nodes = statements(&parsed);
    let StatementKind::Relationship { from, to, .. } = &nodes.first().ok_or("relationship")?.kind
    else {
        return Err("relationship");
    };
    assert_eq!((from.name.as_ref(), to.name.as_ref()), ("1", "42"));
    assert_eq!(from.token.kind, "ENTITY_ONE");
    let StatementKind::Entity {
        name,
        attributes: Some(attributes),
        ..
    } = &nodes.get(1).ok_or("decimal entity")?.kind
    else {
        return Err("decimal entity");
    };
    assert_eq!(name.name, "2.5");
    assert_eq!(attributes.attributes.len(), 2);
    assert_eq!(
        attributes
            .attributes
            .get(1)
            .ok_or("nullable")?
            .attribute_type
            .question
            .as_ref()
            .ok_or("question")?
            .span,
        Span { start: 42, end: 43 }
    );
    Ok(())
}

#[test]
fn er_to_prefixed_subgraph_id_remains_whole_in_relationships() -> Result<(), &'static str> {
    let source = "erDiagram\nsubgraph TOP\nend\nA ||--|| TOP : links\nTOP ||--|| B : links";
    let parsed = parse(source, &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "a TO-prefixed subgraph id must remain an entity-name token: {:?}",
        parsed.diagnostics
    );
    let nodes = statements(&parsed);
    assert_eq!(nodes.len(), 3);
    let StatementKind::Subgraph { header, .. } = &nodes.first().ok_or("subgraph")?.kind else {
        return Err("subgraph");
    };
    assert_eq!(
        (header.id.name.as_ref(), header.id.span),
        ("TOP", Span { start: 19, end: 22 })
    );
    let StatementKind::Relationship {
        from,
        to,
        relation,
        role,
        ..
    } = &nodes.get(1).ok_or("incoming relationship")?.kind
    else {
        return Err("incoming relationship");
    };
    assert_eq!(
        (from.name.as_ref(), to.name.as_ref(), role.label.as_ref()),
        ("A", "TOP", "links")
    );
    assert_eq!(to.span, Span { start: 36, end: 39 });
    assert_eq!(
        (relation.left.kind, relation.right.kind),
        (CardinalityKind::OnlyOne, CardinalityKind::OnlyOne)
    );
    let StatementKind::Relationship { from, to, .. } =
        &nodes.get(2).ok_or("outgoing relationship")?.kind
    else {
        return Err("outgoing relationship");
    };
    assert_eq!((from.name.as_ref(), to.name.as_ref()), ("TOP", "B"));
    assert_eq!(from.span, Span { start: 48, end: 51 });
    Ok(())
}
