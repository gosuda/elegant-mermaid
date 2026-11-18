use super::{
    ast::*,
    lexer::{MODES, lex},
    parse,
};
use crate::source::Span;

#[test]
fn header_eof_has_no_synthetic_body() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.header.span, Span { start: 0, end: 12 });
    assert_eq!(parsed.document.line_end.span, Span { start: 12, end: 12 });
    assert!(
        parsed.document.lines.is_empty(),
        "expected no lines, got {:?}",
        parsed.document.lines
    );
    Ok(())
}

#[test]
fn token_order_preserves_keywords_longer_alternatives_and_operators() -> Result<(), &'static str> {
    let tokens = lex(
        "actor actorX classDef Include includeX 1mg 1.5px --var --o <-- --|> ..> \\,",
        &[],
    );
    let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
    assert_eq!(
        kinds,
        [
            "ACTOR",
            "IDENTIFIER",
            "CLASS_DEF",
            "INCLUDE",
            "IDENTIFIER",
            "IDENTIFIER",
            "NUMBER",
            "MARKERLESS_SOLID",
            "IDENTIFIER",
            "FORWARD_CIRCLE",
            "BACKWARD_SOLID",
            "GENERALIZATION",
            "DEPENDENCY_ARROW",
            "CSS_ESCAPED_COMMA"
        ]
    );
    assert_eq!(tokens.get(6).ok_or("number")?.text, "1.5px");
    assert_eq!(
        tokens.get(6).ok_or("number")?.span,
        Span { start: 43, end: 48 }
    );
    Ok(())
}

#[test]
fn removed_spans_and_mixed_line_ends_keep_byte_offsets() -> Result<(), &'static str> {
    let source = "xxxx\r\nusecase-beta\ractor A(é)\r\nB[界]\n";
    let tokens = lex(source, &[Span { start: 0, end: 6 }]);
    let header = tokens.first().ok_or("header")?;
    assert_eq!(header.span, Span { start: 6, end: 18 });
    let symbols: Vec<_> = tokens
        .iter()
        .filter(|t| t.kind == "LABEL_SYMBOL")
        .map(|t| (t.text.as_ref(), t.span))
        .collect();
    assert_eq!(
        symbols,
        [
            ("é", Span { start: 27, end: 29 }),
            ("界", Span { start: 34, end: 37 })
        ]
    );
    let parsed = parse(source, &[Span { start: 0, end: 6 }]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.lines.len(), 2);
    Ok(())
}

#[test]
fn declarations_keep_labels_suffixes_and_original_bytes() -> Result<(), &'static str> {
    let source = "usecase-beta\nactor A(Hello  世界)@{business:true} << Staff >>:::staff,admin\nU[\"Quoted\"]\n\"`**Named**`\"\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let LineKind::Statement(statement) = &parsed.document.lines.first().ok_or("actor line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::Actor(actor) = &statement.kind else {
        return Err("actor");
    };
    assert_eq!(actor.items.len(), 1);
    let item = actor.items.first().ok_or("first actor")?;
    let label = item.name.label.as_ref().ok_or("label")?;
    assert_eq!(label.text, "Hello  世界");
    assert_eq!(label.content_span, Span { start: 21, end: 34 });
    assert_eq!(
        item.classes
            .as_ref()
            .ok_or("classes")?
            .classes
            .iter()
            .map(|t| t.text.as_ref())
            .collect::<Vec<_>>(),
        ["staff", "admin"]
    );
    assert_eq!(
        item.stereotype.as_ref().ok_or("stereotype")?.content.text,
        " Staff "
    );
    Ok(())
}

#[test]
fn every_statement_form_retains_ordered_production_nodes() -> Result<(), &'static str> {
    let source = "usecase-beta\naccTitle: Caption\naccDescr {first\nsecond}\ndirection TD\nactor A, B\nU(Use case)\nU --> V\nU@{business:true}\nnote for U \"memo\"\njson J@{\"b\":[1,{\"a\":true}],\"a\":null}:::data\nclassDef hot,cold fill:#abc,stroke-width:2px\nclass U,V hot,cold\nstyle U stroke:rgb(1\\,2\\,3),opacity:.5\nsystemBoundary S[System]@{type:package}:::box\nactor C\nX(Inside)\n\n%% comment\nend\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statements: Vec<_> = parsed
        .document
        .lines
        .iter()
        .filter_map(|l| match &l.kind {
            LineKind::Statement(s) => Some(&s.kind),
            _ => None,
        })
        .collect();
    assert_eq!(statements.len(), 13);
    let StatementKind::Json(json) = statements.get(8).ok_or("json")? else {
        return Err("json node");
    };
    assert_eq!(json.id.text, "J");
    assert_eq!(
        json.object
            .properties
            .iter()
            .map(|p| p.key.text.as_ref())
            .collect::<Vec<_>>(),
        ["\"b\"", "\"a\""]
    );
    let StatementKind::SystemBoundary(boundary) = statements.last().ok_or("boundary")? else {
        return Err("boundary node");
    };
    assert_eq!(boundary.content.elements.len(), 4);
    assert_eq!(boundary.close.text, "end");
    assert_eq!(MODES, ["defaultMode", "jsonBody", "stereotype"]);
    Ok(())
}

#[test]
fn all_association_forms_and_semantic_arrows_keep_labels() -> Result<(), &'static str> {
    let source = "usecase-beta\nA --> B\nA <-- B\nA -- B\nA --o B\nA o-- B\nA --x B\nA x-- B\nA -- yes --> B\nA -- yes -- B\nA -- yes --o B\nA -- yes --x B\nA <-- yes -- B\nA o-- yes -- B\nA x-- yes -- B\nA e@..>:Include B\nA --|> B\nactor User --> B\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.lines.len(), 17);
    let LineKind::Statement(statement) = &parsed
        .document
        .lines
        .get(7)
        .ok_or("labeled association")?
        .kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &statement.kind else {
        return Err("entity");
    };
    let relation = entity.relation.as_ref().ok_or("relation")?;
    let ArrowKind::MarkerlessSolid(arrow) = &relation.arrow.kind else {
        return Err("markerless opener");
    };
    assert_eq!(arrow.label.as_ref().ok_or("label")?.label.text, "yes");
    assert_eq!(
        arrow.right.as_ref().ok_or("right operator")?.kind,
        "FORWARD_SOLID"
    );
    Ok(())
}

#[test]
fn markdown_json_and_stereotype_modes_do_not_split_internal_delimiters() -> Result<(), &'static str>
{
    let source =
        "usecase-beta\nA(\"`a\r\nb`\") <<Core>>\njson J@{\"brace\":\"}\\\"{\",\"nested\":{}}\n";
    let tokens = lex(source, &[]);
    let markdown = tokens
        .iter()
        .find(|t| t.kind == "MARKDOWN_STRING")
        .ok_or("markdown")?;
    assert_eq!(markdown.text, "\"`a\r\nb`\"");
    assert_eq!(markdown.span, Span { start: 15, end: 23 });
    let object = tokens
        .iter()
        .find(|t| t.kind == "JSON_OBJECT_LITERAL")
        .ok_or("json object")?;
    assert_eq!(object.text, "{\"brace\":\"}\\\"{\",\"nested\":{}}");
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    Ok(())
}

#[test]
fn unknown_plantuml_and_semicolon_statements_recover_without_phantom_nodes()
-> Result<(), &'static str> {
    let source = "usecase-beta\nPACKAGE box\nA;\nB\n";
    let parsed = parse(source, &[]);
    let first = parsed.diagnostics.first().ok_or("unknown diagnostic")?;
    assert_eq!(first.code, "usecase/unknown-statement");
    assert_eq!(first.message, "unknown statement PACKAGE");
    assert_eq!(first.span, Span { start: 13, end: 24 });
    let second = parsed.diagnostics.get(1).ok_or("semicolon diagnostic")?;
    assert_eq!(second.code, "usecase/unexpected-token");
    assert_eq!(second.span, Span { start: 26, end: 27 });
    assert_eq!(
        parsed
            .document
            .lines
            .iter()
            .filter(|l| matches!(l.kind, LineKind::Statement(_)))
            .count(),
        1
    );
    Ok(())
}

#[test]
fn invalid_direction_has_sorted_expected_kinds_and_recovers() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta\ndirection UP\nB\n", &[]);
    let error = parsed.diagnostics.first().ok_or("direction diagnostic")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(error.code, "usecase/unexpected-token");
    assert_eq!(
        error.message,
        "unexpected UP, expected one of: BT, LR, RL, TB, TD"
    );
    assert_eq!(error.span, Span { start: 23, end: 25 });
    let LineKind::Statement(statement) =
        &parsed.document.lines.last().ok_or("surviving line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &statement.kind else {
        return Err("entity");
    };
    assert_eq!(entity.name.id.text, "B");
    Ok(())
}

#[test]
fn metadata_assignment_never_becomes_an_entity_declaration() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta\nA@{\n business:true,\n}\n", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let LineKind::Statement(statement) =
        &parsed.document.lines.first().ok_or("assignment line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::MetadataAssignment(assignment) = &statement.kind else {
        return Err("metadata assignment");
    };
    assert_eq!(assignment.target.token.text, "A");
    let property = assignment.metadata.properties.first().ok_or("property")?;
    assert_eq!(property.key_content_span, Span { start: 18, end: 26 });
    assert_eq!(property.value_content_span, Span { start: 27, end: 31 });
    Ok(())
}

#[test]
fn boundary_disallows_relationships_and_preserves_its_end() -> Result<(), &'static str> {
    let source = "usecase-beta\nsystemBoundary S\nA --> B\nC\nend\nD\n";
    let parsed = parse(source, &[]);
    let error = parsed.diagnostics.first().ok_or("boundary diagnostic")?;
    assert_eq!(error.code, "usecase/unexpected-token");
    assert_eq!(error.message, "unexpected -->, expected one of: NEWLINE");
    assert_eq!(error.span, Span { start: 32, end: 35 });
    let LineKind::Statement(statement) = &parsed.document.lines.first().ok_or("boundary")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::SystemBoundary(boundary) = &statement.kind else {
        return Err("boundary");
    };
    assert_eq!(boundary.content.elements.len(), 1);
    assert_eq!(boundary.close.span, Span { start: 40, end: 43 });
    Ok(())
}

#[test]
fn unfinished_delimiters_emit_one_error_through_eof() -> Result<(), &'static str> {
    for (body, start, token) in [
        ("A(", 14, "("),
        ("A[", 14, "["),
        ("A@{", 14, "@{"),
        ("A <<", 15, "<<"),
        ("A(\"unfinished", 15, "\"unfinished"),
        ("A(\"`unfinished", 15, "\"`unfinished"),
        ("json J@{", 20, "{"),
        ("accDescr {", 13, "accDescr {"),
        ("systemBoundary S\nA\n", 13, "systemBoundary"),
    ] {
        let source = format!("usecase-beta\n{body}");
        let parsed = parse(&source, &[]);
        assert_eq!(
            parsed.diagnostics.len(),
            1,
            "{body}: {:?}",
            parsed.diagnostics
        );
        let error = parsed.diagnostics.first().ok_or("unfinished diagnostic")?;
        assert_eq!(error.code, "usecase/unterminated", "{body}");
        assert_eq!(error.message, format!("unterminated {token}"), "{body}");
        assert_eq!(
            error.span,
            Span {
                start,
                end: source.len()
            },
            "{body}"
        );
    }
    Ok(())
}

#[test]
fn strict_json_rejects_trailing_commas_without_discarding_next_statement()
-> Result<(), &'static str> {
    let parsed = parse("usecase-beta\njson J@{\"x\":1,}\nB\n", &[]);
    let error = parsed.diagnostics.first().ok_or("json diagnostic")?;
    assert_eq!(error.code, "usecase/invalid-json");
    assert_eq!(error.message, "invalid JSON object: unexpected token");
    assert_eq!(error.span, Span { start: 27, end: 28 });
    let LineKind::Statement(statement) =
        &parsed.document.lines.last().ok_or("recovered line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &statement.kind else {
        return Err("entity");
    };
    assert_eq!(entity.name.id.text, "B");
    Ok(())
}

#[test]
fn json_nesting_rejects_level_sixty_five_at_opening_bracket() -> Result<(), &'static str> {
    let mut source = String::from("usecase-beta\njson J@{\"x\":");
    source.push_str(&"[".repeat(64));
    source.push('0');
    source.push_str(&"]".repeat(64));
    source.push('}');
    let parsed = parse(&source, &[]);
    let error = parsed.diagnostics.first().ok_or("nesting diagnostic")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(error.code, "limit/nesting-depth");
    assert_eq!(error.message, "nesting depth exceeds 64");
    assert_eq!(error.span, Span { start: 88, end: 89 });
    Ok(())
}

#[test]
fn escaped_html_stereotypes_in_upstream_rejections_are_not_stereotype_tokens()
-> Result<(), &'static str> {
    for source in [
        include_str!(
            "../../../../../corpus/usecase/mermaid/usecase~nightly-check~09-business-and-stereotypes.mmd"
        ),
        include_str!(
            "../../../../../corpus/usecase/mermaid/usecase~nightly-check~20-full-featured-order-system.mmd"
        ),
        include_str!(
            "../../../../../corpus/usecase/mermaid/usecase~pr-check~complete-hand-drawn-rendering-contract.mmd"
        ),
        include_str!(
            "../../../../../corpus/usecase/mermaid/usecase~pr-check~small-representative-visual-snapshot.mmd"
        ),
    ] {
        let end = source.find("\n---\n").ok_or("frontmatter close")? + 5;
        let parsed = parse(source, &[Span { start: 0, end }]);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|d| d.code == "usecase/unexpected-token"),
            "missing unexpected-token for {source:?}: {:?}",
            parsed.diagnostics
        );
        let error = parsed
            .diagnostics
            .iter()
            .find(|d| d.code == "usecase/unexpected-token")
            .ok_or("escaped stereotype diagnostic")?;
        assert_eq!(source.get(error.span.start..error.span.end), Some("&"));
    }
    Ok(())
}

#[test]
fn invalid_stereotype_line_recovers_before_the_next_declaration() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta\nA <<unfinished\nB\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let error = parsed.diagnostics.first().ok_or("stereotype diagnostic")?;
    assert_eq!(error.code, "usecase/unexpected-token");
    assert_eq!(
        error.message,
        "unexpected unfinished, expected one of: STEREOTYPE_TEXT"
    );
    assert_eq!(error.span, Span { start: 17, end: 27 });
    let LineKind::Statement(statement) = &parsed
        .document
        .lines
        .last()
        .ok_or("surviving declaration")?
        .kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &statement.kind else {
        return Err("entity");
    };
    assert_eq!(entity.name.id.text, "B");
    Ok(())
}

#[test]
fn label_requires_content_and_note_requires_a_label() -> Result<(), &'static str> {
    for source in ["usecase-beta\nA()\n", "usecase-beta\nnote for A"] {
        let parsed = parse(source, &[]);
        assert_eq!(parsed.diagnostics.len(), 1);
        let error = parsed
            .diagnostics
            .first()
            .ok_or("missing label diagnostic")?;
        assert_eq!(error.code, "usecase/unexpected-token");
        assert!(
            error
                .message
                .ends_with("expected one of: LABEL_TEXT, MARKDOWN_STRING, PLAIN_STRING"),
            "unexpected message {:?}",
            error.message
        );
    }
    Ok(())
}

#[test]
fn association_label_cannot_mix_quoted_and_unquoted_productions() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta\nA -- \"yes\" extra --> B\nC\n", &[]);
    let error = parsed.diagnostics.first().ok_or("mixed label diagnostic")?;
    assert_eq!(error.code, "usecase/unexpected-token");
    assert_eq!(
        error.message,
        "unexpected extra, expected one of: FORWARD_CIRCLE, FORWARD_CROSS, FORWARD_SOLID, MARKERLESS_SOLID"
    );
    assert_eq!(error.span, Span { start: 24, end: 29 });
    assert_eq!(
        parsed
            .document
            .lines
            .iter()
            .filter(|l| matches!(l.kind, LineKind::Statement(_)))
            .count(),
        1
    );
    Ok(())
}

#[test]
fn json_identifier_span_does_not_alias_the_json_keyword() -> Result<(), &'static str> {
    let parsed = parse("usecase-beta\njson json@{}\n", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let LineKind::Statement(statement) = &parsed.document.lines.first().ok_or("json line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::Json(json) = &statement.kind else {
        return Err("json statement");
    };
    assert_eq!(json.id.text, "json");
    assert_eq!(json.id.span, Span { start: 18, end: 22 });
    assert_eq!(json.object.span, Span { start: 23, end: 25 });
    Ok(())
}

#[test]
fn strict_json_preserves_scalar_lexemes_and_property_order() -> Result<(), &'static str> {
    let source = "usecase-beta\njson J@{\"z\":-1.25e+2,\"a\":\"\\u0041\",\"z\":false}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let LineKind::Statement(statement) = &parsed.document.lines.first().ok_or("json line")?.kind
    else {
        return Err("statement");
    };
    let StatementKind::Json(json) = &statement.kind else {
        return Err("json statement");
    };
    assert_eq!(
        json.object
            .properties
            .iter()
            .map(|p| p.key.text.as_ref())
            .collect::<Vec<_>>(),
        ["\"z\"", "\"a\"", "\"z\""]
    );
    let first = json.object.properties.first().ok_or("number property")?;
    let JsonValueKind::Scalar(token) = &first.value.kind else {
        return Err("scalar value");
    };
    assert_eq!(token.kind, "JSON_NUMBER");
    assert_eq!(token.text, "-1.25e+2");
    Ok(())
}

#[test]
fn closed_invalid_constructs_at_eof_are_not_reported_as_unterminated() -> Result<(), &'static str> {
    for source in [
        "usecase-beta\nA()",
        "usecase-beta\nA << >>",
        "usecase-beta\nA@{x:[]}",
    ] {
        let parsed = parse(source, &[]);
        assert_eq!(
            parsed.diagnostics.len(),
            1,
            "{source}: {:?}",
            parsed.diagnostics
        );
        let error = parsed
            .diagnostics
            .first()
            .ok_or("closed invalid construct diagnostic")?;
        assert_eq!(error.code, "usecase/unexpected-token");
    }
    Ok(())
}

#[test]
fn quoted_name_and_markdown_label_content_spans_exclude_only_delimiters() -> Result<(), &'static str>
{
    let source = "usecase-beta\n\"é 名\"\nA(\"`**bold**`\")\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let LineKind::Statement(first) = &parsed
        .document
        .lines
        .first()
        .ok_or("quoted declaration")?
        .kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &first.kind else {
        return Err("entity");
    };
    assert_eq!(entity.name.id.span, Span { start: 13, end: 21 });
    assert_eq!(entity.name.id_content_span, Span { start: 14, end: 20 });
    let LineKind::Statement(second) = &parsed
        .document
        .lines
        .get(1)
        .ok_or("markdown declaration")?
        .kind
    else {
        return Err("statement");
    };
    let StatementKind::Entity(entity) = &second.kind else {
        return Err("entity");
    };
    let label = entity.name.label.as_ref().ok_or("markdown label")?;
    assert_eq!(label.kind, LabelKind::Markdown);
    assert_eq!(label.text, "**bold**");
    assert_eq!(label.content_span, Span { start: 26, end: 34 });
    Ok(())
}
