use super::parse;
use crate::model::flowchart::resolve;

#[test]
fn flowchart_demo_model() {
    let source = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(diagnostics.is_empty());
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
    let (model, diagnostics) = resolve(source, &parsed.document);
    assert!(diagnostics.is_empty());
    assert_eq!(
        model
            .nodes
            .iter()
            .map(|node| node.id.as_str())
            .collect::<Vec<_>>(),
        ["A"]
    );
    assert_eq!(model.nodes[0].label, "");
    assert!(model.edges.is_empty());
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
            .any(|diagnostic| diagnostic.code == "flowchart/end-without-subgraph")
    );
}

#[test]
fn flowchart_recovery_makes_progress() {
    let parsed = parse(";@@", &[]);
    assert!(!parsed.diagnostics.is_empty());
    assert!(
        parsed
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.span.end <= 3)
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
    assert!(!parse("flowchart LR\nA <-- B\n", &[]).diagnostics.is_empty());
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
