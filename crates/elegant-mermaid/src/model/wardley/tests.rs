use super::{Flow, Model, Strategy, resolve};
use crate::syntax::preprocess::preprocess;
use crate::syntax::wardley::parse;

fn built(text: &str) -> (Model, Vec<String>) {
    let removed = preprocess(text).removed;
    let parsed = parse(text, &removed);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = resolve(text, &parsed.document);
    let messages = diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    (model, messages)
}

fn model(text: &str) -> Model {
    let (model, messages) = built(text);
    assert!(messages.is_empty(), "{messages:?}");
    model
}

#[test]
fn coordinates_are_normalised_thousandths() {
    let cases: [(&str, i64); 11] = [
        ("0.0", 0),
        ("0.5", 50000),
        ("0.95", 95000),
        ("1.0", 100000),
        ("0.123456", 12346),
        ("0.999999", 100000),
        ("1.5", 1500),
        ("12.5", 12500),
        ("99.9996", 100000),
        ("100.0", 100000),
        ("00100.000", 100000),
    ];
    for (value, want) in cases {
        let m = model(&format!("wardley-beta\ncomponent A [{value}, {value}]\n"));
        assert_eq!((m.nodes[0].x, m.nodes[0].y), (want, want), "{value}");
    }
}

#[test]
fn coordinate_out_of_range() {
    let (_, messages) = built("wardley-beta\ncomponent A [100.5, 0.5]\nanchor B [0.5, 250.25]\n");
    assert_eq!(
        messages,
        [
            "wardley/coordinate-out-of-range: Anchor \"B\" evolution must be between 0-1 (decimal) or 0-100 (percentage). Received: 250.25",
            "wardley/coordinate-out-of-range: Component \"A\" visibility must be between 0-1 (decimal) or 0-100 (percentage). Received: 100.5",
        ]
    );
    let (_, messages) = built("wardley-beta\ncomponent A [100.0001, 0.5]\n");
    assert_eq!(messages.len(), 1);
}

#[test]
fn visibility_is_y_and_evolution_is_x() {
    let m = model(
        "wardley-beta\ncomponent A [0.2, 0.7]\nnote \"n\" [0.3, 0.6]\nannotations [0.1, 0.9]\nannotation 4,[0.4, 0.8] \"t\"\naccelerator F [0.5, 0.55]\ndeaccelerator G [0.45, 0.35]\n",
    );
    assert_eq!((m.nodes[0].x, m.nodes[0].y), (70000, 20000));
    assert_eq!(
        (m.notes[0].text.as_str(), m.notes[0].x, m.notes[0].y),
        ("n", 60000, 30000)
    );
    assert_eq!(m.box_point.map(|p| (p.x, p.y)), Some((90000, 10000)));
    let a = &m.annotations[0];
    assert_eq!(
        (a.number, a.x, a.y, a.text.as_str()),
        (4, 80000, 40000, "t")
    );
    assert_eq!(
        (
            m.accelerators[0].name.as_str(),
            m.accelerators[0].x,
            m.accelerators[0].y
        ),
        ("F", 55000, 50000)
    );
    assert_eq!(
        (
            m.deaccelerators[0].name.as_str(),
            m.deaccelerators[0].x,
            m.deaccelerators[0].y
        ),
        ("G", 35000, 45000)
    );
}

#[test]
fn first_annotations_box_wins() {
    let m = model("wardley-beta\nannotations [0.1, 0.9]\nannotations [0.3, 0.4]\n");
    assert_eq!(m.box_point.map(|p| (p.x, p.y)), Some((90000, 10000)));
}

#[test]
fn later_declaration_replaces_but_keeps_position_and_label_offset() {
    let m = model(
        "wardley-beta\ncomponent A [0.1, 0.2] label [-5, 6] (build) (inertia)\ncomponent B [0.3, 0.3]\ncomponent A [0.5, 0.6]\n",
    );
    assert_eq!(m.nodes.len(), 2);
    let a = &m.nodes[0];
    assert_eq!(a.id, "A");
    assert_eq!((a.x, a.y), (60000, 50000));
    assert!(a.has_offset);
    assert_eq!((a.offset_x, a.offset_y), (-5, 6));
    assert_eq!(a.strategy, Strategy::None);
    assert!(!a.inertia);
    let m = model("wardley-beta\nanchor A [0.1, 0.2]\ncomponent A [0.5, 0.6]\n");
    assert!(!m.nodes[0].anchor);
}

#[test]
fn pipeline_inherits_visibility_and_keeps_members() {
    let m = model(
        "wardley-beta\ncomponent K [0.45, 0.57]\npipeline K {\n  component Fire [0.35] label [-60, 35]\n  component Gas [0.53]\n}\nK -> Fire\nFire -> K\n",
    );
    assert_eq!(m.nodes.len(), 3);
    assert!(m.nodes[0].pipeline_parent);
    let fire = &m.nodes[1];
    assert_eq!((fire.id.as_str(), fire.name.as_str()), ("K_Fire", "Fire"));
    assert_eq!((fire.x, fire.y), (35000, 45000));
    assert_eq!((fire.offset_x, fire.offset_y), (-60, 35));
    assert_eq!(m.pipelines.len(), 1);
    assert_eq!(m.pipelines[0].node, "K");
    assert_eq!(m.pipelines[0].components, ["K_Fire", "K_Gas"]);
    assert_eq!(m.links[0].target, "K_Fire");
    assert_eq!(m.links[1].source, "K_Fire");
}

#[test]
fn repeated_pipeline_replaces_membership() {
    let m = model(
        "wardley-beta\ncomponent K [0.45, 0.57]\npipeline K {\n component A [0.1]\n}\npipeline K {\n component B [0.2]\n}\n",
    );
    assert_eq!(m.pipelines.len(), 1);
    assert_eq!(m.pipelines[0].components, ["K_B"]);
    assert_eq!(m.nodes.len(), 3);
}

#[test]
fn pipeline_parent_must_exist() {
    let (_, messages) = built("wardley-beta\npipeline Nope {\n component A [0.1]\n}\n");
    assert_eq!(
        messages,
        [
            "wardley/pipeline-parent-unknown: Pipeline \"Nope\" must reference an existing component with coordinates."
        ]
    );
}

#[test]
fn link_flows_labels_and_dashes() {
    let m = model(
        "wardley-beta\ncomponent A [0.1, 0.1]\ncomponent B [0.2, 0.2]\nA +> B; first\nA +<> B\nA +'q'< B; ignored\nA +''> B; dropped\nA -.-> B +<\nA --> B\nA > B\nA -> Ghost\n",
    );
    let got: Vec<(&str, &str, bool, &str, Flow)> = m
        .links
        .iter()
        .map(|l| {
            (
                l.source.as_str(),
                l.target.as_str(),
                l.dashed,
                l.label.as_str(),
                l.flow,
            )
        })
        .collect();
    assert_eq!(
        got,
        [
            ("A", "B", false, "first", Flow::Forward),
            ("A", "B", false, "", Flow::Bidirectional),
            ("A", "B", false, "q", Flow::Backward),
            ("A", "B", false, "", Flow::Forward),
            ("A", "B", true, "", Flow::Backward),
            ("A", "B", false, "", Flow::None),
            ("A", "B", false, "", Flow::None),
            ("A", "Ghost", false, "", Flow::None),
        ]
    );
}

#[test]
fn evolve_needs_known_node_and_replaces_trend() {
    let m = model(
        "wardley-beta\ncomponent A [0.4, 0.2]\ncomponent B [0.1, 0.1]\nevolve A 0.5\nevolve B 0.6\nevolve A 0.7\nevolve Ghost 999.5\n",
    );
    let got: Vec<(&str, i64, i64)> = m
        .trends
        .iter()
        .map(|t| (t.node.as_str(), t.target_x, t.target_y))
        .collect();
    assert_eq!(got, [("A", 70000, 40000), ("B", 60000, 10000)]);
    let (_, messages) = built("wardley-beta\ncomponent A [0.4, 0.2]\nevolve A 150.5\n");
    assert_eq!(
        messages,
        [
            "wardley/coordinate-out-of-range: Evolve target for \"A\" must be between 0-1 (decimal) or 0-100 (percentage). Received: 150.5"
        ]
    );
}

#[test]
fn evolution_stages_and_boundaries() {
    let m = model("wardley-beta\nevolution Genesis@0.25 -> Custom / Concept -> Product@0.8125\n");
    assert_eq!(m.stages, ["Genesis", "Custom / Concept", "Product"]);
    assert_eq!(m.boundaries, [250, 813]);
    let m = model("wardley-beta\nevolution A -> B\nevolution C -> D -> E\n");
    assert_eq!(m.stages, ["C", "D", "E"]);
    assert!(m.boundaries.is_empty());
}

fn config(m: &Model) -> Vec<(&str, i64)> {
    m.config.iter().map(|e| (e.key.as_str(), e.value)).collect()
}

#[test]
fn size_and_config() {
    let m = model("wardley-beta\nsize [1100, 800]\n");
    assert_eq!(config(&m), [("height", 800), ("width", 1100)]);
    let m = model(
        "---\nconfig:\n  wardley-beta:\n    width: 700\n    padding: 20\n    nodeRadius: 9\n---\nwardley-beta\nsize [1100, 0]\n",
    );
    assert_eq!(config(&m), [("padding", 20), ("width", 1100)]);
    let m = model(
        "%%{init: {\"wardley-beta\": {\"width\": 90000, \"height\": 400}}}%%\nwardley-beta\n",
    );
    assert_eq!(config(&m), [("height", 400)]);
}

#[test]
fn title_and_accessibility() {
    let m = model("---\ntitle: Front\n---\nwardley-beta\naccTitle: T\naccDescr: D\n");
    assert_eq!(
        (m.title.as_str(), m.acc_title.as_str(), m.acc_descr.as_str()),
        ("Front", "T", "D")
    );
    let m = model("---\ntitle: Front\n---\nwardley-beta\ntitle One\ntitle Two &amp; #35;x\n");
    assert_eq!(m.title, "Two &amp; #x");
    let m = model("---\ntitle: Front\n---\nwardley-beta\ntitle One\ntitle\n");
    assert_eq!(m.title, "Front");
}

#[test]
fn entities_are_decoded_in_display_text_only() {
    let m =
        model("wardley-beta\ncomponent \"a #35; b\" [0.1, 0.1]\n\"a #35; b\" -> \"a #35; b\"\n");
    assert_eq!(m.nodes[0].id, "a #35; b");
    assert_eq!(m.nodes[0].label, "a # b");
    assert_eq!(m.links.len(), 1);
}
