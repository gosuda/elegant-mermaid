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
    assert_eq!(model.nodes[0].shape, "diamond");
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
