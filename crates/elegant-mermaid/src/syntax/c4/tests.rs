use super::{
    ast::*,
    lexer::{MACROS, MODES, lex},
    parse,
};
use crate::source::Span;

#[test]
fn c4_headers_retain_selected_type_and_call_span() -> Result<(), &'static str> {
    for header in [
        "C4Context",
        "C4Container",
        "C4Component",
        "C4Dynamic",
        "C4Deployment",
    ] {
        let source = format!("{header}\nPerson(a,\"A\")\n");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let StartKind::MermaidDoc(doc) = parsed.document.kind else {
            return Err("document");
        };
        assert_eq!(doc.graph_config.header.text, header);
        let statement = doc.graph_config.statements.items.first().ok_or("call")?;
        assert_eq!(
            statement.span(),
            Span {
                start: header.len() + 1,
                end: header.len() + 14
            }
        );
    }
    Ok(())
}

#[test]
fn c4_all_macro_modes_keep_full_name_boundaries() -> Result<(), &'static str> {
    for &(name, kind, mode) in MACROS {
        let source = format!("{name}(a,\"A\")");
        let tokens = lex(&source, &[]);
        let token = tokens.first().ok_or("macro token")?;
        assert_eq!((token.kind, token.text.as_ref()), (kind, name));
        assert_eq!(
            token.span,
            Span {
                start: 0,
                end: name.len()
            }
        );
        assert!(MODES.contains(&mode), "unexpected lexer mode {mode:?}");
        assert_eq!(tokens.get(1).map(|t| t.kind), Some("LPAREN"));
        assert_eq!(tokens.iter().rev().nth(1).map(|t| t.kind), Some("RPAREN"));
    }
    Ok(())
}

#[test]
fn c4_attributes_keep_empty_named_and_utf8_values() -> Result<(), &'static str> {
    let source = "C4Context\nPerson(a,\"é\",,\"\",$tags=\" x \" )\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(
        parsed.diagnostics.first().map(|d| d.code),
        Some("c4/unterminated")
    );
    let source = "C4Context\nPerson(a,\"é\",,\"\",$tags=\" x \")\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    let Statement::Diagram(statement) = doc.graph_config.statements.items.first().ok_or("call")?
    else {
        return Err("diagram");
    };
    let DiagramStatementKind::Call { attributes, .. } = &statement.kind else {
        return Err("call");
    };
    assert_eq!(attributes.span, Span { start: 16, end: 40 });
    assert_eq!(attributes.items.len(), 5);
    let AttributeKind::Positional(label) = &attributes.items.get(1).ok_or("label")?.kind else {
        return Err("positional");
    };
    assert_eq!(
        (label.text.as_ref(), label.span),
        ("é", Span { start: 19, end: 23 })
    );
    let named = attributes.items.last().ok_or("named")?;
    let AttributeKind::Named { key, value } = &named.kind else {
        return Err("named attribute");
    };
    assert_eq!((key.text.as_ref(), value.text.as_ref()), ("tags", "x"));
    assert_eq!(
        source.get(named.span.start..named.span.end),
        Some("$tags=\" x \"")
    );
    Ok(())
}

#[test]
fn c4_boundaries_accept_three_brace_arrangements() -> Result<(), &'static str> {
    for (prefix, suffix) in [(" {\n", "\n}"), ("\n{", "}"), ("\n{\n", "\n}")] {
        let source = format!("C4Deployment\nNode_L(n,\"N\"){prefix}Person(a,\"A\"){suffix}\n");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let StartKind::MermaidDoc(doc) = parsed.document.kind else {
            return Err("document");
        };
        let Statement::Diagram(statement) = doc
            .graph_config
            .statements
            .items
            .first()
            .ok_or("boundary")?
        else {
            return Err("diagram");
        };
        let DiagramStatementKind::Boundary(boundary) = &statement.kind else {
            return Err("boundary");
        };
        assert_eq!(boundary.start.start.macro_token.text, "Node_L");
        assert_eq!(boundary.body.items.len(), 1);
        assert_eq!(boundary.stop.close.text, "}");
        assert_eq!(
            source.get(boundary.span.start..boundary.span.end),
            source
                .strip_prefix("C4Deployment\n")
                .and_then(|s| s.strip_suffix('\n'))
        );
    }
    Ok(())
}

#[test]
fn c4_element_relation_and_update_families_accept_named_arguments() -> Result<(), &'static str> {
    let source = "C4Component\nContainerDb_Ext(a,\"A\",\"SQL\",$descr=\"store\")\nRel_Right(a,b,\"go\",$techn=\"HTTP\")\nBiRel(a,b,\"two\")\nRel_Back(b,a,\"back\")\nRelIndex(1,a,b,\"indexed\")\nUpdateElementStyle(a,$bgColor=\"blue\")\nUpdateRelStyle(a,b,$offsetX=\"-2px\")\nUpdateLayoutConfig($c4ShapeInRow=\"3\",$c4BoundaryInRow=\"2\")\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.statements.items.len(), 8);
    let Statement::Diagram(statement) =
        doc.graph_config.statements.items.get(1).ok_or("relation")?
    else {
        return Err("diagram");
    };
    let DiagramStatementKind::Call {
        macro_token,
        attributes,
    } = &statement.kind
    else {
        return Err("call");
    };
    assert_eq!(macro_token.kind, "REL_R");
    assert_eq!(attributes.items.len(), 4);
    Ok(())
}

#[test]
fn c4_metadata_comments_removed_spans_and_line_endings() -> Result<(), &'static str> {
    let source = "---\r\nC4Context\r\ntitle Demo\raccTitle: é\r\naccDescription Long\raccDescr: text\raccDescr { one\r\ntwo }\r%% comment\rPerson(a,\"A\")\r";
    let parsed = parse(source, &[Span { start: 0, end: 5 }]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.header.span, Span { start: 5, end: 14 });
    let items = &doc.graph_config.statements.items;
    assert_eq!(items.len(), 6);
    let Statement::Other(statement) = items.get(1).ok_or("title")? else {
        return Err("metadata");
    };
    assert_eq!(
        (statement.form, statement.value.text.as_ref()),
        ("acc_title", "é")
    );
    let Statement::Other(statement) = items.get(4).ok_or("block")? else {
        return Err("metadata");
    };
    assert_eq!(statement.value.text, "one\r\ntwo");
    assert_eq!(
        source.get(statement.span.start..statement.span.end),
        Some("accDescr { one\r\ntwo }")
    );
    Ok(())
}

#[test]
fn c4_unicode_metadata_separators_preserve_values_and_source_spans() -> Result<(), &'static str> {
    let source =
        "C4Context\ntitle\u{00a0} \tDemo  \naccDescription\u{2003}\t Details \t\nSystem(a,\"A\")\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = crate::model::c4::resolve(source, &parsed.document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.acc_title, "Demo");
    assert_eq!(model.acc_descr, "Details");
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    for (index, raw) in [(0, " \tDemo  "), (1, "\t Details \t")] {
        let Statement::Other(statement) = doc
            .graph_config
            .statements
            .items
            .get(index)
            .ok_or("metadata")?
        else {
            return Err("metadata statement");
        };
        let span = statement.value.span;
        assert!(
            source.is_char_boundary(span.start),
            "metadata {index} start {} is not a UTF-8 boundary",
            span.start
        );
        assert!(
            source.is_char_boundary(span.end),
            "metadata {index} end {} is not a UTF-8 boundary",
            span.end
        );
        assert_eq!(source.get(span.start..span.end), Some(raw));
        assert_eq!(statement.value.text, raw);
    }
    Ok(())
}

#[test]
fn c4_direction_first_match_precedes_header_and_macros() -> Result<(), &'static str> {
    let parsed = parse("noise direction LR suffix direction TB end", &[]);
    assert!(
        parsed.diagnostics.is_empty(),
        "unexpected diagnostics {:?}",
        parsed.diagnostics
    );
    let StartKind::Direction(direction) = parsed.document.kind else {
        return Err("direction");
    };
    assert_eq!(direction.direction.kind, "direction_tb");
    assert_eq!(direction.span, Span { start: 0, end: 42 });
    Ok(())
}

#[test]
fn c4_unknown_statement_recovers_before_enclosing_close() -> Result<(), &'static str> {
    let source = "C4Context\nBoundary(b,\"B\") {\nPerson(a,\"A\")\nwrong stuff}\nPerson(z,\"Z\")\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = parsed.diagnostics.first().ok_or("unknown")?;
    assert_eq!(diagnostic.code, "c4/unknown-statement");
    assert_eq!(diagnostic.message, "unknown statement wrong");
    assert_eq!(diagnostic.span, Span { start: 42, end: 53 });
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.statements.items.len(), 2);
    Ok(())
}

#[test]
fn c4_empty_calls_and_named_values_recover_to_next_statement() -> Result<(), &'static str> {
    let parsed = parse("C4Context\nPerson()\nPerson(a,\"A\")\n", &[]);
    let diagnostic = parsed.diagnostics.first().ok_or("empty call")?;
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(diagnostic.code, "c4/unexpected-token");
    assert_eq!(
        diagnostic.message,
        "unexpected ), expected one of: ATTRIBUTE_EMPTY, STR, STR_KEY"
    );
    assert_eq!(diagnostic.span, Span { start: 17, end: 18 });
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.statements.items.len(), 1);
    let parsed = parse("C4Context\nPerson(a,$tags=\"\")\nPerson(b,\"B\")\n", &[]);
    let diagnostic = parsed.diagnostics.first().ok_or("empty named value")?;
    assert_eq!(
        diagnostic.message,
        "unexpected ), expected one of: STR_VALUE"
    );
    assert_eq!(diagnostic.span, Span { start: 27, end: 28 });
    Ok(())
}

#[test]
fn c4_unterminated_delimiters_report_opening_through_eof() -> Result<(), &'static str> {
    for (source, start, text) in [
        ("C4Context\nPerson(", 16, "("),
        ("C4Context\nPerson(a,\"é", 19, "\"é"),
        ("C4Context\nPerson(a,$tags=\"x", 19, "$tags=\"x"),
        ("C4Context\naccDescr {x", 19, "{x"),
        ("C4Context\nBoundary(b,\"B\") {\nPerson(a,\"A\")", 26, "{"),
    ] {
        let parsed = parse(source, &[]);
        let diagnostic = parsed.diagnostics.last().ok_or("unterminated")?;
        assert_eq!(diagnostic.code, "c4/unterminated");
        assert_eq!(
            diagnostic.span,
            Span {
                start,
                end: source.len()
            }
        );
        assert_eq!(diagnostic.message, format!("unterminated {text}"));
    }
    Ok(())
}

#[test]
fn c4_bare_arguments_keep_parentheses_and_quotes_do_not_escape() -> Result<(), &'static str> {
    let tokens = lex("Person(a,raw)more,\"x\\\")", &[]);
    let bare = tokens
        .iter()
        .find(|t| t.text == "raw)more")
        .ok_or("bare STR")?;
    assert_eq!(bare.kind, "STR");
    assert_eq!(bare.span, Span { start: 9, end: 17 });
    let quoted = tokens
        .iter()
        .find(|t| t.text == "x\\")
        .ok_or("literal backslash")?;
    assert_eq!(quoted.kind, "STR");
    assert_eq!(tokens.iter().rev().nth(1).map(|t| t.kind), Some("RPAREN"));
    Ok(())
}

#[test]
fn c4_depth_sixty_five_stops_at_opening_brace() -> Result<(), &'static str> {
    let mut source = String::from("C4Context\n");
    for _ in 0..65 {
        source.push_str("Boundary(b,\"B\") {\n");
    }
    let parsed = parse(&source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = parsed.diagnostics.first().ok_or("nesting limit")?;
    assert_eq!(diagnostic.code, "limit/nesting-depth");
    assert_eq!(diagnostic.message, "nesting depth exceeds 64");
    assert_eq!(
        diagnostic.span,
        Span {
            start: 1178,
            end: 1179
        }
    );
    Ok(())
}

#[test]
fn c4_missing_header_newline_and_empty_body_are_rejected() -> Result<(), &'static str> {
    let parsed = parse("C4Context Person(a,\"A\")", &[]);
    let diagnostic = parsed.diagnostics.first().ok_or("missing separator")?;
    assert_eq!(
        diagnostic.message,
        "unexpected Person, expected one of: NEWLINE"
    );
    assert_eq!(diagnostic.span, Span { start: 10, end: 16 });
    let parsed = parse("C4Context\n", &[]);
    let diagnostic = parsed.diagnostics.first().ok_or("empty document")?;
    assert_eq!(
        diagnostic.message,
        "unexpected , expected one of: diagramStatement, otherStatement"
    );
    assert_eq!(diagnostic.span, Span { start: 10, end: 10 });
    Ok(())
}

#[test]
fn c4_empty_boundary_is_not_retained_as_a_cluster() -> Result<(), &'static str> {
    let parsed = parse("C4Context\nBoundary(b,\"B\") {\n}\nPerson(a,\"A\")\n", &[]);
    let diagnostic = parsed.diagnostics.first().ok_or("empty boundary")?;
    assert_eq!(diagnostic.code, "c4/unexpected-token");
    assert_eq!(
        diagnostic.message,
        "unexpected }, expected one of: diagramStatement"
    );
    assert_eq!(diagnostic.span, Span { start: 28, end: 29 });
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.statements.items.len(), 1);
    Ok(())
}

#[test]
fn c4_boundary_macros_preserve_spelling_and_child_order() -> Result<(), &'static str> {
    for name in [
        "Boundary",
        "Enterprise_Boundary",
        "System_Boundary",
        "Container_Boundary",
        "Deployment_Node",
        "Node",
        "Node_L",
        "Node_R",
    ] {
        let source =
            format!("C4Context\n{name}(b,\"B\") {{\nPerson(a,\"A\")\nRel(a,b,\"go\")\n}}\n");
        let parsed = parse(&source, &[]);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let StartKind::MermaidDoc(doc) = parsed.document.kind else {
            return Err("document");
        };
        let Statement::Diagram(statement) = doc
            .graph_config
            .statements
            .items
            .first()
            .ok_or("boundary")?
        else {
            return Err("diagram");
        };
        let DiagramStatementKind::Boundary(boundary) = &statement.kind else {
            return Err("boundary");
        };
        assert_eq!(boundary.start.start.macro_token.text, name);
        assert_eq!(boundary.body.items.len(), 2);
    }
    Ok(())
}

#[test]
fn c4_semicolon_tail_and_unmatched_close_do_not_create_nodes() -> Result<(), &'static str> {
    let parsed = parse("C4Context\nPerson(a,\"A\");\n}\nPerson(b,\"B\")\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 2);
    let first = parsed.diagnostics.first().ok_or("semicolon")?;
    assert_eq!(
        first.message,
        "unexpected ;, expected one of: EOF, NEWLINE, RBRACE"
    );
    assert_eq!(first.span, Span { start: 23, end: 24 });
    let second = parsed.diagnostics.get(1).ok_or("unmatched close")?;
    assert_eq!(second.message, "unexpected }, expected one of: EOF");
    assert_eq!(second.span, Span { start: 25, end: 26 });
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    assert_eq!(doc.graph_config.statements.items.len(), 1);
    Ok(())
}

#[test]
fn c4_leading_empty_slot_uses_its_comma_span() -> Result<(), &'static str> {
    let parsed = parse("C4Context\nPerson(,\"\")\n", &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let StartKind::MermaidDoc(doc) = parsed.document.kind else {
        return Err("document");
    };
    let Statement::Diagram(statement) = doc.graph_config.statements.items.first().ok_or("call")?
    else {
        return Err("diagram");
    };
    let DiagramStatementKind::Call { attributes, .. } = &statement.kind else {
        return Err("call");
    };
    assert_eq!(attributes.span, Span { start: 16, end: 21 });
    assert_eq!(attributes.items.len(), 2);
    assert_eq!(
        attributes.items.first().map(|a| a.span),
        Some(Span { start: 17, end: 18 })
    );
    assert_eq!(
        attributes.items.get(1).map(|a| a.span),
        Some(Span { start: 18, end: 20 })
    );
    Ok(())
}

#[test]
fn c4_all_standalone_directions_keep_exact_tokens() -> Result<(), &'static str> {
    for (source, kind) in [
        ("direction TB", "direction_tb"),
        ("direction BT", "direction_bt"),
        ("direction RL", "direction_rl"),
        ("direction LR", "direction_lr"),
    ] {
        let parsed = parse(source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "unexpected diagnostics for {source:?}: {:?}",
            parsed.diagnostics
        );
        let StartKind::Direction(direction) = parsed.document.kind else {
            return Err("direction");
        };
        assert_eq!(direction.direction.kind, kind);
        assert_eq!(direction.span, Span { start: 0, end: 12 });
    }
    Ok(())
}

#[test]
fn c4_unclosed_brace_at_eof_replaces_missing_newline_error() -> Result<(), &'static str> {
    let parsed = parse("C4Context\nBoundary(b,\"B\") {", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = parsed.diagnostics.first().ok_or("unterminated boundary")?;
    assert_eq!(diagnostic.code, "c4/unterminated");
    assert_eq!(diagnostic.message, "unterminated {");
    assert_eq!(diagnostic.span, Span { start: 26, end: 27 });
    Ok(())
}
