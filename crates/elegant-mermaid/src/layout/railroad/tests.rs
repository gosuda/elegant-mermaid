use super::place::layout;
use super::tree::{Constants, Kind, Node, Params, Rule, joins};
use super::{display_text, rules_of};
use crate::DiagramKind;
use crate::diag::Severity;
use crate::error::RenderError;
use crate::geom::{GeomError, Point, Rect, Size};
use crate::layout::{families, input::Input, modeldump};
use crate::measure::{Metric, Role};
use crate::model::Resolved;
use crate::scene::{DumpOptions, GroupRole, Item, PathCommand, Profile, Scene, ShapeStyle};

const CELL: Constants = Constants {
    pad_x: 1,
    pad_y: 1,
    line_height: 1,
    hsep: 2,
    vsep: 1,
    arc_radius: 1,
    terminal_radius: 0,
    marker_radius: 1,
    margin: 1,
    rule_name_gap: 2,
    rule_end_gap: 2,
    rule_min_baseline: 2,
    rule_min_height: 3,
    empty_width: 20,
    empty_height: 5,
};

const VECTOR: Constants = Constants {
    pad_x: 640,
    pad_y: 640,
    line_height: 1280,
    hsep: 640,
    vsep: 512,
    arc_radius: 640,
    terminal_radius: 640,
    marker_radius: 320,
    margin: 640,
    rule_name_gap: 1280,
    rule_end_gap: 640,
    rule_min_baseline: 1280,
    rule_min_height: 2560,
    empty_width: 12800,
    empty_height: 6400,
};

fn cell_params() -> Params {
    Params {
        profile: Profile::Cell,
        options: DumpOptions::default(),
        constants: CELL,
        metric: Metric::cell(),
    }
}

fn leaf(id: &str, text: &str) -> Node {
    Node {
        id: id.into(),
        kind: Kind::Terminal,
        text: text.into(),
        children: Vec::new(),
    }
}

fn composite(id: &str, kind: Kind, children: Vec<Node>) -> Node {
    Node {
        id: id.into(),
        kind,
        text: String::new(),
        children,
    }
}

fn rule(root: Node) -> Rule {
    Rule {
        id: "r0".into(),
        title: "r =".into(),
        root,
    }
}

fn layout_one(root: Node) -> Result<Scene, GeomError> {
    layout(&[rule(root)], cell_params())
}

fn box_rect(scene: &Scene, id: &str) -> Result<Rect, &'static str> {
    scene
        .boxes()
        .iter()
        .find(|entry| entry.id == id)
        .map(|entry| entry.rect)
        .ok_or("no such box")
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

#[test]
fn single_terminal_rule() -> Result<(), Box<dyn std::error::Error>> {
    let scene = layout_one(leaf("r0.0", "ab"))?;
    assert_eq!(box_rect(&scene, "r0")?, rect(0, 1, 16, 6));
    assert_eq!(box_rect(&scene, "r0.0")?, rect(8, 2, 4, 3));
    assert_eq!(scene.canvas(), Size { w: 16, h: 9 });
    let labels = scene.labels();
    assert_eq!(labels.len(), 1);
    assert_eq!(labels[0].id, "r0.label");
    assert_eq!(labels[0].rect, rect(1, 3, 3, 1));
    Ok(())
}

#[test]
fn sequence_joins_align_centre_lines() -> Result<(), Box<dyn std::error::Error>> {
    let tall = composite(
        "r0.2",
        Kind::Choice,
        vec![leaf("r0.3", "x"), leaf("r0.4", "y")],
    );
    let scene = layout_one(composite(
        "r0.0",
        Kind::Sequence,
        vec![leaf("r0.1", "a"), tall],
    ))?;
    assert_eq!(box_rect(&scene, "r0.0")?, rect(8, 1, 3 + 2 + 7, 7));
    assert_eq!(box_rect(&scene, "r0.1")?, rect(8, 3, 3, 3));
    assert_eq!(box_rect(&scene, "r0.2")?, rect(13, 1, 7, 7));
    let routes = scene.routes();
    assert_eq!(routes.len(), 1);
    assert_eq!(
        (
            routes[0].id.as_str(),
            routes[0].from.as_str(),
            routes[0].to.as_str()
        ),
        ("e0", "r0.1", "r0.2")
    );
    assert_eq!(
        routes[0].points,
        vec![Point { x: 11, y: 4 }, Point { x: 13, y: 4 }]
    );
    Ok(())
}

#[test]
fn choice_centres_narrow_alternatives() -> Result<(), Box<dyn std::error::Error>> {
    let scene = layout_one(composite(
        "r0.0",
        Kind::Choice,
        vec![leaf("r0.1", "abcd"), leaf("r0.2", "a")],
    ))?;
    assert_eq!(box_rect(&scene, "r0.0")?, rect(8, 1, 6 + 4, 7));
    assert_eq!(box_rect(&scene, "r0.1")?, rect(10, 1, 6, 3));
    assert_eq!(box_rect(&scene, "r0.2")?, rect(11, 5, 3, 3));
    Ok(())
}

#[test]
fn optional_and_repetition_bands() -> Result<(), Box<dyn std::error::Error>> {
    let cases = [
        (Kind::Optional, 3 + 4, 3 + 2, 2, 2),
        (Kind::ZeroOrMore, 3 + 4, 3 + 4, 2, 2),
        (Kind::OneOrMore, 3 + 4, 3 + 2, 0, 2),
    ];
    for (kind, w, h, y, x) in cases {
        let scene = layout_one(composite("r0.0", kind, vec![leaf("r0.1", "a")]))?;
        let outer = box_rect(&scene, "r0.0")?;
        assert_eq!((outer.w, outer.h), (w, h), "{kind:?}");
        assert_eq!(
            box_rect(&scene, "r0.1")?,
            rect(outer.x + x, outer.y + y, 3, 3),
            "{kind:?}"
        );
    }
    Ok(())
}

#[test]
fn rule_boxes_stack_with_vertical_separation() -> Result<(), Box<dyn std::error::Error>> {
    let rules = [
        Rule {
            id: "r0".into(),
            title: "a =".into(),
            root: leaf("r0.0", "x"),
        },
        Rule {
            id: "r1".into(),
            title: "b =".into(),
            root: leaf("r1.0", "y"),
        },
    ];
    let scene = layout(&rules, cell_params())?;
    let first = box_rect(&scene, "r0")?;
    let second = box_rect(&scene, "r1")?;
    assert_eq!(second.y, first.y + first.h + 1);
    assert_eq!(scene.canvas().h, second.y + second.h + 1 + 1);
    Ok(())
}

#[test]
fn empty_document_canvas() -> Result<(), Box<dyn std::error::Error>> {
    let scene = layout(&[], cell_params())?;
    assert_eq!(scene.canvas(), Size { w: 20, h: 5 });
    assert!(scene.boxes().is_empty());
    Ok(())
}

#[test]
fn arity_violations() {
    let roots = [
        composite("r0.0", Kind::Choice, vec![leaf("r0.1", "a")]),
        composite("r0.0", Kind::Sequence, Vec::new()),
        composite(
            "r0.0",
            Kind::Optional,
            vec![leaf("r0.1", "a"), leaf("r0.2", "b")],
        ),
        Node {
            id: "r0.0".into(),
            kind: Kind::Terminal,
            text: String::new(),
            children: vec![leaf("r0.1", "a")],
        },
    ];
    for root in roots {
        assert!(matches!(layout_one(root), Err(GeomError::Domain)));
    }
}

#[test]
fn overflow_is_reported() {
    let mut params = cell_params();
    params.constants.pad_x = i64::from(i32::MAX);
    let outcome = layout(&[rule(leaf("r0.0", "a"))], params);
    assert!(matches!(outcome, Err(GeomError::Overflow)));
}

#[test]
fn joins_follow_preorder() -> Result<(), Box<dyn std::error::Error>> {
    let inner = composite(
        "r0.2",
        Kind::Sequence,
        vec![leaf("r0.3", "b"), leaf("r0.4", "c")],
    );
    let outer = composite(
        "r0.0",
        Kind::Sequence,
        vec![leaf("r0.1", "a"), inner, leaf("r0.5", "d")],
    );
    let got = joins(&[rule(outer.clone())]);
    let want = [
        ("e0", "r0.1", "r0.2"),
        ("e1", "r0.2", "r0.5"),
        ("e2", "r0.3", "r0.4"),
    ];
    assert_eq!(got.len(), want.len());
    for (join, (id, from, to)) in got.iter().zip(want) {
        assert_eq!(
            (join.id.as_str(), join.from.as_str(), join.to.as_str()),
            (id, from, to)
        );
    }
    let scene = layout_one(outer)?;
    assert_eq!(scene.routes().len(), want.len());
    for (route, (id, from, to)) in scene.routes().iter().zip(want) {
        assert_eq!(
            (route.id.as_str(), route.from.as_str(), route.to.as_str()),
            (id, from, to)
        );
    }
    Ok(())
}

#[test]
fn vector_loop_uses_quarter_arcs() -> Result<(), Box<dyn std::error::Error>> {
    let params = Params {
        profile: Profile::Vector,
        options: DumpOptions::default(),
        constants: VECTOR,
        metric: Metric::for_role(Role::Label),
    };
    let root = composite("r0.0", Kind::OneOrMore, vec![leaf("r0.1", "a")]);
    let scene = layout(&[rule(root)], params)?;
    let mut arcs = Vec::new();
    for group in scene.items().iter().filter(|group| group.owner == "r0.0") {
        assert_eq!(group.role, GroupRole::Group);
        for item in &group.items {
            let Item::Path(path) = item else {
                return Err("rail is not a path".into());
            };
            assert_eq!(path.shape.style, ShapeStyle::Edge);
            arcs.extend(path.commands.iter().filter_map(|command| match command {
                PathCommand::Arc { r, sweep, .. } => Some((*r, *sweep)),
                _ => None,
            }));
        }
    }
    assert_eq!(arcs.len(), 4);
    for (r, sweep) in arcs {
        assert!(
            r == 640 && (sweep == 16384 || sweep == -16384),
            "{r} {sweep}"
        );
    }
    Ok(())
}

const SAMPLE: &str = "railroad-beta\nr = sequence(terminal(\"a\"), optional(special(\"b c\"))) ;\nq = oneOrMore(nonterminal(\"r\")) ;\n";

const SAMPLE_MODEL_DUMP: &str = r#"{"version":1,"stage":"model","kind":"railroad","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
"boxes":[{"id":"r0","role":"group","parent":"","exclusive":false,"direction":"","shape":"rule"},
{"id":"r0.0","role":"group","parent":"r0","exclusive":false,"direction":"","shape":"sequence"},
{"id":"r0.1","role":"node","parent":"r0.0","exclusive":true,"shape":"terminal"},
{"id":"r0.2","role":"group","parent":"r0.0","exclusive":false,"direction":"","shape":"optional"},
{"id":"r0.3","role":"node","parent":"r0.2","exclusive":true,"shape":"special"},
{"id":"r1","role":"group","parent":"","exclusive":false,"direction":"","shape":"rule"},
{"id":"r1.0","role":"group","parent":"r1","exclusive":false,"direction":"","shape":"oneOrMore"},
{"id":"r1.1","role":"node","parent":"r1.0","exclusive":true,"shape":"nonterminal"}],
"routes":[{"id":"e0","from":"r0.1","to":"r0.2","orthogonal":true,"marker_end":"none"}],
"labels":[{"id":"r0.label","owner":"r0","text":"r =","lines":[]},
{"id":"r0.1.label","owner":"r0.1","text":"a","lines":[]},
{"id":"r0.3.label","owner":"r0.3","text":"? b c ?","lines":[]},
{"id":"r1.label","owner":"r1","text":"q =","lines":[]},
{"id":"r1.1.label","owner":"r1.1","text":"r","lines":[]}]}
"#;

fn input_of(source: &str, profile: Profile) -> Result<Input, &'static str> {
    let (resolved, diagnostics) = Resolved::parse(DiagramKind::Railroad, source, &[]);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err("source has error diagnostics");
    }
    resolved
        .ok_or("no model")?
        .input(profile, DumpOptions::default())
        .map_err(|_| "input failed")
}

#[test]
fn model_dump_golden() -> Result<(), &'static str> {
    let input = input_of(SAMPLE, Profile::Vector)?;
    assert_eq!(modeldump::model_dump(&input), SAMPLE_MODEL_DUMP);
    Ok(())
}

#[test]
fn input_round_trips_through_the_family_tree() -> Result<(), Box<dyn std::error::Error>> {
    let input = input_of(SAMPLE, Profile::Cell)?;
    let rules = rules_of(&input)?;
    let tree_joins = joins(&rules);
    assert_eq!(tree_joins.len(), input.routes.len());
    for (join, route) in tree_joins.iter().zip(&input.routes) {
        assert_eq!(
            (&route.id, &route.from, &route.to),
            (&join.id, &join.from, &join.to)
        );
    }
    assert_eq!(rules.len(), 2);
    assert_eq!(rules[0].title, "r =");
    assert_eq!(rules[1].root.kind, Kind::OneOrMore);
    Ok(())
}

#[test]
fn layouts_satisfy_the_hard_constraints() -> Result<(), Box<dyn std::error::Error>> {
    let sources = [
        SAMPLE,
        "railroad-ebnf-beta\nr = a , ( b | c d )* - e , [ f ] , { g } , ? h ? , i+ ;\n",
        "railroad-abnf-beta\nr = 1*3a / 2[b c] / *(d / e) ;\n",
        "railroad-peg-beta\nr <- &a !(b / c)+ d? e* . ;\n",
        "railroad-beta\ntitle Empty\n",
    ];
    for source in sources {
        for profile in [Profile::Vector, Profile::Cell] {
            let input = input_of(source, profile)?;
            let (scene, _) = families::layout(&input)?;
            assert_eq!(scene.validate()?, None, "{source:?} {profile:?}");
        }
    }
    Ok(())
}

#[test]
fn labels_are_only_rule_titles() -> Result<(), Box<dyn std::error::Error>> {
    let input = input_of(SAMPLE, Profile::Cell)?;
    let (scene, _) = families::layout(&input)?;
    let owners: Vec<&str> = scene.labels().iter().map(|l| l.owner.as_str()).collect();
    assert_eq!(owners, ["r0", "r1"]);
    Ok(())
}

#[test]
fn rejects_models_over_the_limits() -> Result<(), &'static str> {
    let mut input = input_of(SAMPLE, Profile::Cell)?;
    input.options.limits.max_nodes = 3;
    assert!(matches!(
        families::layout(&input),
        Err(RenderError::TooLarge {
            limit: 3,
            actual: 8
        })
    ));
    let mut input = input_of(SAMPLE, Profile::Cell)?;
    input.options.limits.max_text_bytes = 4;
    assert!(matches!(
        families::layout(&input),
        Err(RenderError::TooLarge { limit: 4, .. })
    ));
    Ok(())
}

#[test]
fn rejects_ambiguous_owners() -> Result<(), &'static str> {
    let mut input = input_of(SAMPLE, Profile::Cell)?;
    input.routes[0].id = "r0.1".into();
    assert!(families::layout(&input).is_err());
    Ok(())
}

#[test]
fn rejects_cyclic_or_branching_input() {
    use crate::layout::input::{Box as InputBox, Spacing};
    use crate::scene::{BoxRole, Direction};
    let entry = |id: &str, parent: &str, shape: &str| InputBox {
        icon: false,
        id: id.into(),
        role: BoxRole::Node,
        shape: shape.into(),
        parent: parent.into(),
        exclusive: false,
        text: String::new(),
        direction: String::new(),
    };
    let blank = |boxes: Vec<InputBox>| Input {
        kind: "railroad",
        profile: Profile::Cell,
        direction: Direction::Tb,
        options: DumpOptions::default(),
        boxes,
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    };
    let looped = blank(vec![
        entry("a", "", "optional"),
        entry("a", "a", "optional"),
    ]);
    assert!(matches!(super::layout(&looped), Err(GeomError::Domain)));
    let wide = blank(vec![
        entry("r", "", "rule"),
        entry("x", "r", ""),
        entry("y", "r", ""),
    ]);
    assert!(matches!(super::layout(&wide), Err(GeomError::Domain)));
}

#[test]
fn control_characters_display_as_spaces_or_replacement() -> Result<(), &'static str> {
    let input = input_of(
        "railroad-beta\nr = terminal(\"a\\tb\\nc\") ;\n",
        Profile::Cell,
    )?;
    assert_eq!(input.boxes[1].text, "a b c");
    assert_eq!(display_text("a\u{1}\u{85}b"), "a\u{fffd}\u{fffd}b");
    Ok(())
}
