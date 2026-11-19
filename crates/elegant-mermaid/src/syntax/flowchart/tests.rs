use super::parse;
use crate::diag::Severity;
use crate::model::flowchart::resolve;

#[test]
fn flowchart_demo_model() {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        diagnostics.is_empty(),
        "expected diagnostics.is_empty(); observed diagnostics={:?}",
        diagnostics
    );
    assert_eq!(model.direction, "LR");
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A", "B", "C"]
    );
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.label.as_str())
            .collect::<Vec<_>>(),
        ["Start", "Choice", "Done"]
    );
    assert_eq!(
        model
            .edges
            .iter()
            .map(|edge| (edge.from.as_str(), edge.to.as_str(), edge.label.as_deref()))
            .collect::<Vec<_>>(),
        [
            ("A", "B", None),
            ("B", "C", Some("yes")),
            ("B", "A", Some("no"))
        ]
    );
}

#[test]
fn flowchart_unclosed_bracket() {
    let source = "flowchart LR\n  A[Start --> B\n";
    let parsed = parse(source, &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(
        parsed.diagnostics[0].code,
        "flowchart/unclosed-node-bracket"
    );
    assert_eq!(parsed.diagnostics[0].span.start, 16);
    assert_eq!(parsed.diagnostics[0].span.end, source.len());
    assert_eq!(parsed.diagnostics[0].fixes.len(), 1);
    assert_eq!(
        parsed.diagnostics[0].fixes[0].title,
        "Add the closing bracket"
    );
    assert_eq!(
        parsed.diagnostics[0].fixes[0].edits[0].span.start,
        source.len()
    );
    assert_eq!(parsed.diagnostics[0].fixes[0].edits[0].new_text, "]");
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        diagnostics.is_empty(),
        "expected diagnostics.is_empty(); observed diagnostics={:?}",
        diagnostics
    );
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A"]
    );
    assert_eq!(model.nodes[0].label, "Start --> B");
    assert!(
        model.edges.is_empty(),
        "expected model.edges.is_empty(); observed model.edges={:?}",
        model.edges
    );
}

#[test]
fn flowchart_statement_recovery() {
    let source = "flowchart TD\nA[one]\nend\nB[two]\n";
    let parsed = parse(source, &[]);
    let (model, _) = resolve(source, &parsed.document);
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A", "B"]
    );
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "flowchart/end-without-subgraph"),
        "expected parsed .diagnostics .iter() .any(|diagnostic| diagnostic.code == \"flowchart/end-without-subgraph\"); observed parsed.diagnostics={:?}",
        parsed.diagnostics
    );
}

#[test]
fn flowchart_recovery_makes_progress() {
    let parsed = parse(";@@", &[]);
    assert!(
        !parsed.diagnostics.is_empty(),
        "expected !parsed.diagnostics.is_empty(); observed parsed.diagnostics={:?}",
        parsed.diagnostics
    );
    assert!(
        parsed
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.span.end <= 3),
        "expected parsed .diagnostics .iter() .all(|diagnostic| diagnostic.span.end <= 3); observed parsed.diagnostics={:?}",
        parsed.diagnostics
    );
}

#[test]
fn flowchart_shape_data_and_entities() {
    let source = "flowchart TD\nA@{ shape: diamond, label: 'hello #amp; world' }\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.nodes.len(), 1);
    assert_eq!(model.nodes[0].shape, "diam");
    assert_eq!(model.nodes[0].label, "hello & world");
}

#[test]
fn flowchart_unknown_typed_shape() {
    let source = "flowchart TD\nA@{ shape: NotAShape }\n";
    let parsed = parse(source, &[]);
    let (_, diagnostics) = resolve(source, &parsed.document);
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "flowchart/typed-shape-unsupported");
}

#[test]
fn flowchart_later_label_replaces_only_when_present() {
    let source = "flowchart TD\nA[first]\nA[second]\nA --> B\n";
    let parsed = parse(source, &[]);
    let (model, _) = resolve(source, &parsed.document);
    assert_eq!(model.nodes[0].label, "second");
    assert_eq!(model.edges[0].to, "B");
}

#[test]
fn flowchart_upstream_syntax_regressions() {
    for source in [
        "flowchart\n A@{ shape: rect, label: \"process\" }\n",
        "flowchart TD\nA{{choice}} --> B((circle))\n",
        "flowchart TD\nA:::classA --> B:::classB\nclassDef classA fill:red\n",
        "flowchart LR\nA e1@--> B\ne1@{ animate: true }\n",
        "flowchart LR\nA-->B\nclick A call callback() \"tip\"\n",
        "flowchart LR\nA[/red<br/>text/] --> B\n",
        "flowchart TD\nA[<img src=\"https://example.test/image.svg\"> more text]\n",
        "\n  flowchart LR\naccTitle: A title\naccDescr: A description\noutside --> subgraph1\n",
        "flowchart LR\nA --- B === C\n",
    ] {
        let parsed = parse(source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
    for source in [
        "flowchart TD\nA[/dev/tty unavailable]\n",
        "flowchart TD\nA-->B\nlinkStyle 0:1 stroke:red\n",
        "flowchart TD\nsubgraph\nA-->B\nend\n",
        "flowchart TD\nA --|text \"quoted\"|--> B\n",
        "flowchart TD\nA-->B\nclick A call \"tip\"\n",
    ] {
        let parsed = parse(source, &[]);
        assert!(!parsed.diagnostics.is_empty(), "accepted {source}");
    }
}

#[test]
fn flowchart_edge_markers() {
    for (link, start, end, stroke) in [
        ("<-->", "point", "point", "normal"),
        ("o--o", "circle", "circle", "normal"),
        ("x--x", "cross", "cross", "normal"),
        ("o--x", "none", "none", "normal"),
        ("<==>", "point", "point", "thick"),
        ("o==o", "circle", "circle", "thick"),
        ("x==x", "cross", "cross", "thick"),
        ("o==x", "none", "none", "thick"),
        ("<-.->", "point", "point", "dotted"),
        ("o-.-o", "circle", "circle", "dotted"),
        ("x-.-x", "cross", "cross", "dotted"),
        ("o-.-x", "none", "none", "dotted"),
        ("<-- text -->", "point", "point", "normal"),
        ("-- text -->", "none", "point", "normal"),
    ] {
        let source = format!("flowchart LR\nA {link} B\n");
        let parsed = parse(&source, &[]);
        assert!(
            parsed.diagnostics.is_empty(),
            "{link}: {:?}",
            parsed.diagnostics
        );
        let (model, diagnostics) = resolve(&source, &parsed.document);
        assert!(diagnostics.is_empty(), "{link}: {diagnostics:?}");
        assert_eq!(model.edges.len(), 1, "{link}");
        let edge = &model.edges[0];
        assert_eq!(
            (&*edge.start, &*edge.marker, &*edge.stroke, edge.length),
            (start, end, stroke, 1),
            "{link}"
        );
    }
    let diagnostics = parse("flowchart LR\nA <-- B\n", &[]).diagnostics;
    assert!(
        !diagnostics.is_empty(),
        "expected diagnostics.is_empty() == false; observed diagnostics={:?}",
        diagnostics
    );
}

#[test]
fn flowchart_edge_attribute_reference() {
    let source = "flowchart LR\nA e1@--> B\ne1@{ animate: true, curve: basis }\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.nodes.len(), 2);
    assert_eq!(model.edges.len(), 1);
    assert_eq!(model.edges[0].user_id, "e1");
    assert_eq!(
        model.edges[0].attrs.get("animate").map(String::as_str),
        Some("true")
    );
    assert_eq!(
        model.edges[0].attrs.get("curve").map(String::as_str),
        Some("basis")
    );
}

#[test]
fn flowchart_quote_span_regressions() {
    for source in ["0\"0\"`0\"\"0", "\"\"", "\"00000\"0"] {
        let parsed = parse(source, &[]);
        assert!(!parsed.diagnostics.is_empty(), "{source:?}");
        for diagnostic in parsed.diagnostics {
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len(),
                "{diagnostic:?}"
            );
        }
    }
}

#[test]
fn flowchart_first_subgraph_membership() {
    let source = "flowchart\nsubgraph Frontend\nAPI --> UI\nend\nsubgraph Backend\nAPI --> DB\nend\nsubgraph Frontend[Replacement]\nNEW\nend\n";
    let parsed = parse(source, &[]);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        parsed.diagnostics.is_empty() && diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty() && diagnostics.is_empty(); observed parsed.diagnostics={:?}, diagnostics={:?}",
        parsed.diagnostics,
        diagnostics
    );
    assert_eq!(model.groups.len(), 2);
    assert_eq!(model.groups[0].title, "Frontend");
    assert_eq!(model.groups[0].members, ["API", "UI", "NEW"]);
    assert_eq!(model.groups[1].members, ["DB"]);
}

#[test]
fn flowchart_explicit_label_and_dotted_text() {
    let source = "flowchart\nA --> B[B]\nC[\"\"] -. retry .-> D\n";
    let parsed = parse(source, &[]);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        parsed.diagnostics.is_empty() && diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty() && diagnostics.is_empty(); observed parsed.diagnostics={:?}, diagnostics={:?}",
        parsed.diagnostics,
        diagnostics
    );
    assert!(
        model.nodes[0].label_kind.is_none(),
        "expected model.nodes[0].label_kind.is_none(); observed model.nodes[0].label_kind={:?}",
        model.nodes[0].label_kind
    );
    assert!(
        model.nodes[1].label_kind.is_some(),
        "expected model.nodes[1].label_kind.is_some(); observed model.nodes[1].label_kind={:?}",
        model.nodes[1].label_kind
    );
    assert!(
        model.nodes[2].label_kind.is_some(),
        "expected model.nodes[2].label_kind.is_some(); observed model.nodes[2].label_kind={:?}",
        model.nodes[2].label_kind
    );
    assert_eq!(model.edges[1].label.as_deref(), Some("retry"));
}

#[test]
fn flowchart_nested_subgraph_completes_first() {
    let source = "flowchart\nsubgraph Outer\nA\nsubgraph Inner\nA\nend\nB\nend\n";
    let parsed = parse(source, &[]);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        parsed.diagnostics.is_empty() && diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty() && diagnostics.is_empty(); observed parsed.diagnostics={:?}, diagnostics={:?}",
        parsed.diagnostics,
        diagnostics
    );
    assert_eq!(model.groups[0].members, ["B"]);
    assert_eq!(model.groups[1].members, ["A"]);
}

#[test]
fn flowchart_invalid_direction_span() {
    let parsed = parse("flowchart XY\n A --> B\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(diagnostic.code, "flowchart/dir-invalid");
    assert_eq!(diagnostic.span.start, 10);
    assert_eq!(diagnostic.span.end, 12);
    assert!(
        diagnostic.fixes.is_empty(),
        "expected diagnostic.fixes.is_empty(); observed diagnostic.fixes={:?}",
        diagnostic.fixes
    );
}

#[test]
fn flowchart_title_only_subgraph_ids() {
    let source =
        "flowchart\nsubgraph S\nA\nend\nsubgraph S\nB\nend\nsubgraph \"Quoted group\"\nC\nend\n";
    let parsed = parse(source, &[]);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        parsed.diagnostics.is_empty() && diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty() && diagnostics.is_empty(); observed parsed.diagnostics={:?}, diagnostics={:?}",
        parsed.diagnostics,
        diagnostics
    );
    assert_eq!(model.groups.len(), 2);
    assert_eq!(model.groups[1].id, "subGraph2");
    assert_eq!(model.groups[1].title, "Quoted group");
}

#[test]
fn flowchart_chain_continues_after_comment_line() {
    let source = "flowchart TD\nA --> B\n  --> C\n  %% c\n  --> H\n";
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let parsed = parse(source, &removed);
    assert!(
        parsed.diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty(); observed diagnostics={:?}",
        parsed.diagnostics
    );
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        diagnostics.is_empty(),
        "expected diagnostics.is_empty(); observed diagnostics={:?}",
        diagnostics
    );
    assert_eq!(
        model
            .edges
            .iter()
            .map(|edge| (edge.from.as_str(), edge.to.as_str()))
            .collect::<Vec<_>>(),
        [("A", "B"), ("B", "C"), ("C", "H")]
    );
}

#[test]
fn flowchart_click_continues_after_comment_line() {
    let source = "flowchart TD\nA\nB\nclick\n%% c\n A callback\n";
    let removed = crate::syntax::preprocess::preprocess(source).removed;
    let parsed = parse(source, &removed);
    assert!(
        parsed.diagnostics.is_empty(),
        "expected parsed.diagnostics.is_empty(); observed diagnostics={:?}",
        parsed.diagnostics
    );
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(
        diagnostics
            .iter()
            .all(|d| d.code == "interaction/callback-ignored" && d.severity == Severity::Info),
        "expected only interaction/callback-ignored info; observed diagnostics={:?}",
        diagnostics
    );
    assert_eq!(model.clicks.len(), 1);
    assert_eq!(
        &source[model.clicks[0].target.start..model.clicks[0].target.end],
        "A"
    );
    let at = source.len() - "callback\n".len();
    assert_eq!(
        model.clicks[0].action,
        crate::syntax::flowchart::ast::ClickAction::PlainCall {
            name: "callback".into(),
            name_span: crate::source::Span {
                start: at,
                end: at + "callback".len(),
            },
            tooltip: None,
        }
    );
}
