use super::{Config, Model, Shape, resolve};
use crate::diag::Diagnostic;
use crate::source::Span;

fn resolved(src: &str) -> (Model, Vec<Diagnostic>) {
    let pre = crate::syntax::preprocess::preprocess(src);
    let parsed = crate::syntax::mindmap::parse(src, &pre.removed);
    let (model, mut diagnostics) = resolve(src, &parsed.document);
    diagnostics.splice(0..0, parsed.diagnostics);
    (model, diagnostics)
}

fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
    ds.iter().map(|d| d.code).collect()
}

fn shape(node: &str) -> Option<Shape> {
    let (model, ds) = resolved(&format!("mindmap\n  {node}\n"));
    assert!(ds.is_empty(), "{node}: {ds:?}");
    model.nodes.first().map(|n| n.shape)
}

#[test]
fn shape_follows_opener_and_closer() {
    for (node, want) in [
        ("a", Shape::Default),
        ("a[b]", Shape::Square),
        ("a[b)", Shape::Square),
        ("a(b)", Shape::Rounded),
        ("a(b]", Shape::Cloud),
        ("a(b))", Shape::Cloud),
        ("a((b))", Shape::Circle),
        ("a((b)", Shape::Circle),
        ("a)b(", Shape::Cloud),
        ("a))b))", Shape::Bang),
        ("a{{b}}", Shape::Hexagon),
        ("a(-b-)", Shape::Default),
        ("a-)b(-", Shape::Cloud),
        ("((b))", Shape::Circle),
        ("a[\"b\"]", Shape::Square),
    ] {
        assert_eq!(shape(node), Some(want), "{node}");
    }
}

#[test]
fn ids_and_descriptions() {
    let (m, ds) = resolved("mindmap\n  root  \n    x[ y ]\n    ((z))\n    x[w]\n");
    assert!(ds.is_empty());
    assert_eq!(m.nodes[0].source_id, "root  ");
    assert_eq!(m.nodes[0].label, "root");
    assert_eq!(m.nodes[1].source_id, "x");
    assert_eq!(m.nodes[1].description, " y ");
    assert_eq!(m.nodes[1].label, "y");
    assert_eq!(m.nodes[2].source_id, "z");
    assert_eq!(m.nodes[2].description, "z");
    assert_eq!(m.nodes.len(), 4);
    assert_eq!(m.nodes[0].children, [1, 2, 3]);
    assert_eq!(m.nodes[1].source_id, m.nodes[3].source_id);
}

#[test]
fn parent_is_the_latest_strictly_lower_level() {
    let (m, ds) = resolved("mindmap\n  root\n    a\n      b\n    c\n   d\n     e\n");
    assert!(ds.is_empty());
    let parents: Vec<Option<usize>> = m.nodes.iter().map(|n| n.parent).collect();
    let levels: Vec<i64> = m.nodes.iter().map(|n| n.level).collect();
    assert_eq!(parents, [None, Some(0), Some(1), Some(0), Some(0), Some(4)]);
    assert_eq!(levels, [0, 2, 4, 2, 1, 3]);
}

#[test]
fn indentation_jumps_and_tabs_are_accepted() {
    let (m, ds) = resolved("mindmap\n\troot\n\t\t\t\tdeep\n\t\tmid\n");
    assert!(ds.is_empty());
    let parents: Vec<Option<usize>> = m.nodes.iter().map(|n| n.parent).collect();
    let levels: Vec<i64> = m.nodes.iter().map(|n| n.level).collect();
    assert_eq!(parents, [None, Some(0), Some(0)]);
    assert_eq!(levels, [0, 3, 1]);
}

#[test]
fn second_root_is_rejected_and_dropped() {
    let (m, ds) = resolved("mindmap\n  root\n  other\n    kid\n");
    assert_eq!(codes(&ds), ["mindmap/second-root"]);
    assert_eq!(
        ds[0].message,
        "node other has no parent; only one root is allowed"
    );
    assert_eq!(ds[0].span, Span { start: 17, end: 22 });
    assert_eq!(m.nodes.len(), 2);
    assert_eq!(m.nodes[1].label, "kid");
    assert_eq!(m.nodes[1].parent, Some(0));
}

#[test]
fn shallower_than_the_root_is_a_second_root() {
    let (_, ds) = resolved("mindmap\n    root\n  other\n");
    assert_eq!(codes(&ds), ["mindmap/second-root"]);
}

#[test]
fn decorations_attach_to_the_last_inserted_node() {
    let (m, ds) = resolved(
        "mindmap\n  root\n    a\n  ::icon(first)\n      :::one\n    b\n::icon(second)\n  :::two\n",
    );
    assert!(ds.is_empty());
    assert_eq!(m.nodes[0].icon, "");
    assert_eq!(m.nodes[1].icon, "first");
    assert_eq!(m.nodes[1].class, "one");
    assert_eq!(m.nodes[2].icon, "second");
    assert_eq!(m.nodes[2].class, "two");
    assert_eq!(m.nodes[0].children, [1, 2]);
}

#[test]
fn later_decoration_replaces_earlier_one() {
    let (m, ds) = resolved("mindmap\n  root\n  ::icon(a)\n  ::icon(b)\n  :::x\n  :::y z\n");
    assert!(ds.is_empty());
    assert_eq!(m.nodes[0].icon, "b");
    assert_eq!(m.nodes[0].class, "y z");
}

#[test]
fn decoration_before_any_node_is_reported() {
    let src = "mindmap\n  ::icon(a)\n  :::x\n  root\n";
    let (m, ds) = resolved(src);
    assert_eq!(
        codes(&ds),
        [
            "mindmap/decoration-target-missing",
            "mindmap/decoration-target-missing"
        ]
    );
    assert_eq!(ds[0].message, "decoration has no preceding node");
    assert_eq!(src.get(ds[0].span.start..ds[0].span.end), Some("::icon(a)"));
    assert_eq!(src.get(ds[1].span.start..ds[1].span.end), Some(":::x"));
    assert_eq!(m.nodes[0].label, "root");
}

#[test]
fn empty_mindmap_has_no_nodes() {
    let (m, ds) = resolved("mindmap\n\n");
    assert!(ds.is_empty());
    assert!(m.nodes.is_empty());
}

#[test]
fn labels_decode_entities_and_normalize_newlines() {
    let (m, ds) =
        resolved("mindmap\r\n  root((A#amp;B #9731; #nope;\r\nC))\r\n  ::icon(x\r\ny)\r\n");
    assert!(ds.is_empty());
    assert_eq!(m.nodes[0].label, "A&B \u{2603} #nope;\nC");
    assert_eq!(m.nodes[0].description, "A#amp;B #9731; #nope;\nC");
    assert_eq!(m.nodes[0].icon, "x\ny");
}

#[test]
fn markdown_description_is_flagged() {
    let (m, ds) = resolved("mindmap\n  a[\"`**b**`\"]\n");
    assert!(ds.is_empty());
    assert!(m.nodes[0].markdown);
    assert_eq!(m.nodes[0].label, "**b**");
    let (m, _) = resolved("mindmap\n  a[\"b\"]\n");
    assert!(!m.nodes[0].markdown);
}

#[test]
fn config_reads_padding_and_max_node_width_from_both_blocks() {
    let (m, ds) = resolved(
        "---\nconfig:\n  mindmap:\n    padding: 12\n    maxNodeWidth: 300\n---\n%%{init: {\"mindmap\": {\"padding\": 20}}}%%\nmindmap\n  root\n",
    );
    assert!(ds.is_empty());
    assert_eq!(
        m.config,
        Config {
            padding: Some(20),
            max_node_width: Some(300)
        }
    );
    let (m, _) = resolved(
        "---\nconfig:\n  mindmap:\n    padding: 1.5\n    maxNodeWidth: -3\n    other: 4\n---\nmindmap\n  root\n",
    );
    assert_eq!(m.config, Config::default());
}
