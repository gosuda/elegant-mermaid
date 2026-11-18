use super::{
    ast::*,
    lexer::{MODES, lex},
    parse,
};
use crate::source::Span;

#[test]
fn agentflow_header_retains_authored_direction_and_normalizes() -> Result<(), &'static str> {
    for (authored, canonical) in [
        ("LR", "LR"),
        ("RL", "RL"),
        ("TB", "TB"),
        ("BT", "BT"),
        ("TD", "TB"),
        ("BR", "TB"),
        ("<", "RL"),
        (">", "LR"),
        ("^", "BT"),
        ("v", "TB"),
    ] {
        let source = format!("agentflow-beta {authored}\nA\n");
        let p = parse(&source, &[]);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        assert_eq!(p.document.config.direction.value, canonical);
        assert_eq!(p.document.header.span, Span { start: 0, end: 14 });
        assert_eq!(
            p.document
                .config
                .authored
                .as_ref()
                .ok_or("direction")?
                .text
                .trim(),
            authored
        );
    }
    let p = parse("agentflow-beta\nA\n", &[]);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    assert_eq!(p.document.config.direction.value, "TB");
    Ok(())
}
#[test]
fn agentflow_nodes_preserve_every_bracket_form() -> Result<(), &'static str> {
    let forms = [
        ("[one]", "square"),
        ("(((one)))", "doublecircle"),
        ("((one))", "circle"),
        ("(-one-)", "ellipse"),
        ("([one])", "stadium"),
        ("[[one]]", "subroutine"),
        ("[(one)]", "cylinder"),
        ("(one)", "round"),
        ("{one}", "diamond"),
        ("{{one}}", "hexagon"),
        (">one]", "odd"),
        ("[/one\\]", "trapezoid"),
        ("[\\one/]", "inv_trapezoid"),
        ("[/one/]", "lean_right"),
        ("[\\one\\]", "lean_left"),
    ];
    for (form, shape) in forms {
        let source = format!("agentflow-beta\nA{form}\n");
        let p = parse(&source, &[]);
        assert!(p.diagnostics.is_empty(), "{form}: {:?}", p.diagnostics);
        let s = p
            .document
            .document
            .lines
            .iter()
            .find_map(|l| l.statement.as_ref())
            .ok_or("statement")?;
        let StatementKind::Vertex(v) = &s.kind else {
            return Err("vertex");
        };
        let node = v
            .nodes
            .first()
            .ok_or("node")?
            .vertices
            .first()
            .ok_or("styled vertex")?;
        assert_eq!(node.vertex.shape, Some(shape));
        assert_eq!(
            node.vertex.span,
            Span {
                start: 15,
                end: 16 + form.len()
            }
        );
        let label = node.vertex.label.as_ref().ok_or("label")?;
        assert_eq!(
            label
                .pieces
                .iter()
                .map(|t| t.text.as_ref())
                .collect::<String>(),
            "one"
        );
    }
    Ok(())
}
#[test]
fn agentflow_edges_keep_sets_ids_labels_and_chains() -> Result<(), &'static str> {
    let p = parse(
        "agentflow-beta LR\nA & B e@-->|yes| C & D -- failure --x E -.- F\n",
        &[],
    );
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let s = p
        .document
        .document
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("statement")?;
    let StatementKind::Vertex(v) = &s.kind else {
        return Err("vertex chain");
    };
    assert_eq!(
        v.nodes.iter().map(|n| n.vertices.len()).collect::<Vec<_>>(),
        [2, 2, 1, 1]
    );
    assert_eq!(v.links.len(), 3);
    assert_eq!(
        v.links
            .first()
            .ok_or("edge")?
            .statement
            .id
            .as_ref()
            .ok_or("id")?
            .text,
        "e@"
    );
    assert_eq!(
        v.links
            .first()
            .ok_or("edge")?
            .label()
            .ok_or("label")?
            .pieces
            .first()
            .ok_or("text")?
            .text,
        "yes"
    );
    assert_eq!(
        v.links
            .get(1)
            .ok_or("split edge")?
            .statement
            .operator
            .text
            .trim(),
        "--x"
    );
    Ok(())
}
#[test]
fn agentflow_metadata_strings_and_inline_classes_keep_source_spans() -> Result<(), &'static str> {
    let source = "agentflow-beta\nA[\"é\"]:::hot@{ shape: tool, label: \"a\nb\" }\n";
    let p = parse(source, &[]);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let s = p
        .document
        .document
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("statement")?;
    let StatementKind::Vertex(v) = &s.kind else {
        return Err("vertex");
    };
    let node = v
        .nodes
        .first()
        .ok_or("node")?
        .vertices
        .first()
        .ok_or("styled vertex")?;
    assert_eq!(
        node.class
            .as_ref()
            .ok_or("class")?
            .tokens
            .first()
            .ok_or("class token")?
            .text,
        "hot"
    );
    let text = node.vertex.label.as_ref().ok_or("label")?;
    assert_eq!(text.kind, TextKind::String);
    assert_eq!(
        text.pieces.first().ok_or("piece")?.span,
        Span { start: 17, end: 21 }
    );
    let metadata = node.metadata.first().ok_or("metadata")?;
    assert_eq!(
        source.get(metadata.span.start..metadata.span.end),
        Some("@{ shape: tool, label: \"a\nb\" }")
    );
    assert_eq!(metadata.value, " shape: tool, label: \"a\nb\" ");
    Ok(())
}
#[test]
fn agentflow_flow_global_connector_and_direction_are_tagged() -> Result<(), &'static str> {
    let p = parse(
        "agentflow-beta\nflow f[Title]@{view: expanded}\ndirection LR\nA\nglobal\nB\nend\nend\nconnector out[Done]@{shape: connector}\n",
        &[],
    );
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let mut lines = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref());
    let StatementKind::Flow {
        name, body, close, ..
    } = &lines.next().ok_or("flow")?.kind
    else {
        return Err("flow");
    };
    assert_eq!(
        name.as_ref()
            .ok_or("name")?
            .pieces
            .first()
            .ok_or("piece")?
            .text,
        "f"
    );
    assert_eq!(close.end - close.start, 3);
    assert_eq!(
        body.lines.iter().filter(|l| l.statement.is_some()).count(),
        3
    );
    let connector = lines.next().ok_or("connector")?;
    assert!(
        matches!(connector.kind, StatementKind::Connector { .. }),
        "expected connector after flow, observed {connector:?}"
    );
    Ok(())
}
#[test]
fn agentflow_styles_and_link_styles_keep_order() -> Result<(), &'static str> {
    let p = parse(
        "agentflow-beta\nA --> B\nstyle A fill:#abc,stroke:red\nclassDef hot fill:red\nclass A,B hot\nlinkStyle 0,1 interpolate linear stroke:blue\nlinkStyle default stroke:red\n",
        &[],
    );
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let lines: Vec<_> = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    let StatementKind::Style(s) = &lines.get(1).ok_or("style")?.kind else {
        return Err("style");
    };
    assert_eq!(s.styles.styles.len(), 2);
    assert!(
        matches!(
            lines.get(2).ok_or("classDef")?.kind,
            StatementKind::ClassDef(_)
        ),
        "expected class definition at index 2, observed {:?}",
        lines.get(2)
    );
    assert!(
        matches!(lines.get(3).ok_or("class")?.kind, StatementKind::Class(_)),
        "expected class assignment at index 3, observed {:?}",
        lines.get(3)
    );
    let StatementKind::LinkStyle(s) = &lines.get(4).ok_or("linkStyle")?.kind else {
        return Err("linkStyle");
    };
    assert_eq!(
        s.indices
            .as_ref()
            .ok_or("indices")?
            .indices
            .iter()
            .map(|t| t.text.as_ref())
            .collect::<Vec<_>>(),
        ["0", "1"]
    );
    assert_eq!(
        s.interpolation
            .as_ref()
            .ok_or("interpolation")?
            .tokens
            .first()
            .ok_or("token")?
            .text,
        "linear"
    );
    Ok(())
}
#[test]
fn agentflow_click_variants_retain_arguments_tooltip_target() -> Result<(), &'static str> {
    let p = parse(
        "agentflow-beta\nclick A call callback(1, 'x') \"tip\"\nclick B href \"https://example.org\" \"site\" _blank\nclick C callback\nclick D \"mailto:a@b\"\nclick E call empty()\n",
        &[],
    );
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let mut lines = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref());
    let StatementKind::Click(c) = &lines.next().ok_or("callback")?.kind else {
        return Err("callback");
    };
    assert_eq!(c.id.text, "A");
    assert_eq!(c.arguments.as_ref().ok_or("arguments")?.text, "1, 'x'");
    assert_eq!(c.tooltip.as_ref().ok_or("tooltip")?.text, "tip");
    let StatementKind::Click(c) = &lines.next().ok_or("href")?.kind else {
        return Err("href");
    };
    assert_eq!(c.target.as_ref().ok_or("target")?.text, "_blank");
    assert_eq!(c.url.as_ref().ok_or("url")?.text, "https://example.org");
    assert_eq!(lines.count(), 3);
    Ok(())
}
#[test]
fn agentflow_accessibility_and_line_endings_preserve_unicode() -> Result<(), &'static str> {
    let source =
        "agentflow-beta\raccTitle: é\r\naccDescr: 文\raccDescr {long\r\ntext}\rA[\"`bold`\"]\r";
    let p = parse(source, &[]);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let statements: Vec<_> = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref())
        .collect();
    assert_eq!(statements.len(), 4);
    let StatementKind::Accessibility { title: true, value } =
        &statements.first().ok_or("title")?.kind
    else {
        return Err("title");
    };
    assert_eq!(value.text, "é");
    assert_eq!(value.span, Span { start: 25, end: 27 });
    let StatementKind::Accessibility {
        title: false,
        value,
    } = &statements.get(2).ok_or("description")?.kind
    else {
        return Err("description");
    };
    assert_eq!(value.text, "long\r\ntext");
    assert_eq!(
        source.get(value.span.start..value.span.end),
        Some("accDescr {long\r\ntext}")
    );
    Ok(())
}
#[test]
fn agentflow_unknown_statement_recovers_without_phantom_nodes() -> Result<(), &'static str> {
    let p = parse("agentflow-beta\n= =\nA\n", &[]);
    let d = p.diagnostics.first().ok_or("diagnostic")?;
    assert_eq!(d.code, "agentflow/unexpected-token");
    assert_eq!(
        d.message,
        "unexpected =, expected one of: COMMENT, EOF, NEWLINE, SEMI"
    );
    assert_eq!(d.span, Span { start: 17, end: 18 });
    assert_eq!(
        p.document
            .document
            .lines
            .iter()
            .filter(|l| l.statement.is_some())
            .count(),
        1
    );
    let p = parse("agentflow-beta\n] bad\nA\n", &[]);
    let d = p.diagnostics.first().ok_or("unknown diagnostic")?;
    assert_eq!(d.code, "agentflow/unknown-statement");
    assert_eq!(d.message, "unknown statement ]");
    assert_eq!(d.span, Span { start: 15, end: 20 });
    Ok(())
}
#[test]
fn agentflow_unterminated_delimiters_report_one_opening_span() -> Result<(), &'static str> {
    for suffix in [
        "A[unfinished",
        "A(unfinished",
        "A{unfinished",
        "A -->|unfinished",
        "A(-unfinished",
        "A([unfinished",
        "A[[unfinished",
        "A[(unfinished",
        "A(((unfinished",
        "A[/unfinished",
        "A[\\unfinished",
        "A{{unfinished",
        "A[\"unfinished",
        "A[\"`unfinished",
        "A@{ label: x",
        "A@{label: \"x",
        "flow f\nA\n",
        "global\nA\n",
        "accDescr {unfinished",
        "A -- unfinished",
    ] {
        let source = format!("agentflow-beta\n{suffix}");
        let p = parse(&source, &[]);
        let d = p.diagnostics.first().ok_or("unterminated diagnostic")?;
        assert_eq!(
            d.code, "agentflow/unterminated",
            "{suffix}: {:?}",
            p.diagnostics
        );
        assert_eq!(d.span.end, source.len());
        assert!(
            d.span.start >= 15,
            "unterminated span must follow header, observed {d:?}"
        );
        assert_eq!(p.diagnostics.len(), 1, "{suffix}: {:?}", p.diagnostics);
    }
    Ok(())
}
#[test]
fn agentflow_depth_sixty_five_stops_at_opening_keyword() -> Result<(), &'static str> {
    let source = format!("agentflow-beta\n{}", "flow\n".repeat(65));
    let p = parse(&source, &[]);
    let d = p.diagnostics.first().ok_or("depth diagnostic")?;
    assert_eq!(p.diagnostics.len(), 1);
    assert_eq!(d.code, "limit/nesting-depth");
    assert_eq!(d.message, "nesting depth exceeds 64");
    assert_eq!(
        d.span,
        Span {
            start: 335,
            end: 339
        }
    );
    Ok(())
}
#[test]
fn agentflow_lexer_first_match_and_removed_ranges_are_observable() -> Result<(), &'static str> {
    let source = "ignored\nagentflow-beta\nstyleNode vname 123abc 文 🦀\n";
    let tokens = lex(source, &[Span { start: 0, end: 8 }]);
    assert_eq!(
        tokens.first().ok_or("header")?.span,
        Span { start: 8, end: 22 }
    );
    let tail: Vec<_> = tokens
        .iter()
        .filter(|t| t.span.start >= 23)
        .map(|t| (t.kind, t.text.as_ref()))
        .collect();
    assert_eq!(tail.first(), Some(&("NODE_STRING", "styleNode")));
    assert!(
        tail.contains(&("NUM", "123")),
        "numeric rule must precede identifier rule: {tail:?}"
    );
    assert!(
        tail.contains(&("UNICODE_TEXT", "文")),
        "authority letter range must contain 文: {tail:?}"
    );
    assert!(
        tail.contains(&("INVALID", "🦀")),
        "non-authority emoji must be invalid: {tail:?}"
    );
    assert_eq!(MODES.len(), 19);
    Ok(())
}
#[test]
fn agentflow_property_shape_and_empty_metadata_keep_delimiters() -> Result<(), &'static str> {
    let p = parse("agentflow-beta\nA[|key:value|text]\nB@{}\n", &[]);
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let mut statements = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref());
    let StatementKind::Vertex(v) = &statements.next().ok_or("property")?.kind else {
        return Err("property");
    };
    let vertex = &v
        .nodes
        .first()
        .ok_or("node")?
        .vertices
        .first()
        .ok_or("styled")?
        .vertex;
    let (key, value) = vertex.property.as_ref().ok_or("property pair")?;
    assert_eq!((key.text.as_ref(), value.text.as_ref()), ("key", "value"));
    let StatementKind::Vertex(v) = &statements.next().ok_or("metadata")?.kind else {
        return Err("metadata");
    };
    let data = v
        .nodes
        .first()
        .ok_or("node")?
        .vertices
        .first()
        .ok_or("styled")?
        .metadata
        .first()
        .ok_or("metadata")?;
    assert_eq!(data.value, "");
    assert_eq!(data.span.end - data.span.start, 3);
    Ok(())
}

#[test]
fn agentflow_recovery_inside_flow_preserves_valid_children() -> Result<(), &'static str> {
    let source = "agentflow-beta\nflow f\n] bad\nA --> B\nend\nC\n";
    let p = parse(source, &[]);
    assert_eq!(p.diagnostics.len(), 1);
    let d = p.diagnostics.first().ok_or("diagnostic")?;
    assert_eq!(d.code, "agentflow/unknown-statement");
    assert_eq!(d.message, "unknown statement ]");
    assert_eq!(d.span, Span { start: 22, end: 27 });
    let mut statements = p
        .document
        .document
        .lines
        .iter()
        .filter_map(|l| l.statement.as_ref());
    let StatementKind::Flow { body, .. } = &statements.next().ok_or("flow")?.kind else {
        return Err("flow survives recovery");
    };
    let child = body
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("child")?;
    let StatementKind::Vertex(child) = &child.kind else {
        return Err("child edge");
    };
    assert_eq!(child.links.len(), 1);
    assert_eq!(child.nodes.len(), 2);
    let following = statements.next().ok_or("following statement")?;
    assert!(
        matches!(following.kind, StatementKind::Vertex(_)),
        "recovery must retain the vertex following the flow, observed {following:?}"
    );
    Ok(())
}

#[test]
fn agentflow_metadata_normalization_only_changes_quoted_newlines() -> Result<(), &'static str> {
    let p = parse(
        "agentflow-beta\nA@{label: \"a\r\n  b\", shape: task}@{value: next}\n",
        &[],
    );
    assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    let s = p
        .document
        .document
        .lines
        .iter()
        .find_map(|l| l.statement.as_ref())
        .ok_or("statement")?;
    let StatementKind::Vertex(v) = &s.kind else {
        return Err("vertex");
    };
    let n = v
        .nodes
        .first()
        .ok_or("node")?
        .vertices
        .first()
        .ok_or("vertex")?;
    assert_eq!(n.metadata.len(), 2);
    let first = n.metadata.first().ok_or("metadata")?;
    assert_eq!(first.value, "label: \"a\r\n  b\", shape: task");
    assert_eq!(first.normalized_value(), "label: \"a<br/>b\", shape: task");
    assert_eq!(
        n.metadata.get(1).ok_or("second metadata")?.value,
        "value: next"
    );
    Ok(())
}

#[test]
fn agentflow_literal_keywords_have_jison_word_boundaries() -> Result<(), &'static str> {
    let tokens = lex(
        "agentflow-beta\nclassify flowRef ender styleNode defaulted vname\nv\n",
        &[],
    );
    let names: Vec<_> = tokens
        .iter()
        .filter(|t| t.kind == "NODE_STRING")
        .map(|t| t.text.as_ref())
        .collect();
    assert_eq!(
        names,
        [
            "classify",
            "flowRef",
            "ender",
            "styleNode",
            "defaulted",
            "vname"
        ]
    );
    let down = tokens
        .iter()
        .find(|t| t.kind == "DOWN")
        .ok_or("down token")?;
    assert_eq!(down.text, "v");
    Ok(())
}

#[test]
fn agentflow_unclosed_labels_preserve_opening_and_exact_message() -> Result<(), &'static str> {
    let p = parse("agentflow-beta\nA[unfinished", &[]);
    let d = p.diagnostics.first().ok_or("diagnostic")?;
    assert_eq!(d.code, "agentflow/unterminated");
    assert_eq!(d.message, "unterminated [");
    assert_eq!(d.span, Span { start: 16, end: 27 });
    let p = parse("agentflow-beta\nA[\"é", &[]);
    let d = p.diagnostics.first().ok_or("quoted diagnostic")?;
    assert_eq!(d.span, Span { start: 17, end: 20 });
    assert_eq!(d.message, "unterminated \"é");
    Ok(())
}

#[test]
fn agentflow_removed_operators_never_create_partial_edges() -> Result<(), &'static str> {
    for operator in ["==>", "~~~", "<-->"] {
        let source = format!("agentflow-beta\nA {operator} B\nC\n");
        let p = parse(&source, &[]);
        let diagnostic = p.diagnostics.first().ok_or("rejected operator")?;
        assert!(
            matches!(
                diagnostic.code,
                "agentflow/unexpected-token" | "agentflow/unknown-statement"
            ),
            "removed operator {operator} must produce a syntax rejection, observed {diagnostic:?}"
        );
        let mut statements = p
            .document
            .document
            .lines
            .iter()
            .filter_map(|l| l.statement.as_ref());
        let StatementKind::Vertex(v) = &statements.next().ok_or("recovered C")?.kind else {
            return Err("expected C");
        };
        assert!(
            v.links.is_empty(),
            "recovered standalone C must have no links, observed {v:?}"
        );
        assert_eq!(
            v.nodes
                .first()
                .ok_or("node")?
                .vertices
                .first()
                .ok_or("vertex")?
                .vertex
                .id
                .tokens
                .first()
                .ok_or("id")?
                .text,
            "C"
        );
        let remaining = statements.next();
        assert!(
            remaining.is_none(),
            "rejected operator must leave only C, observed {remaining:?}"
        );
    }
    Ok(())
}
