use super::*;
use crate::geom::{Point, Rect};

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn node(id: &str) -> SceneBox {
    SceneBox {
        id: id.to_owned(),
        role: BoxRole::Node,
        rect: rect(0, 0, 10, 10),
        parent: String::new(),
        exclusive: true,
    }
}

fn text_item() -> Item {
    Item::Text(TextItem {
        rect: rect(0, 0, 10, 10),
        role: TextRole::Label,
        size: 14,
        align: Align::Middle,
        style: TextStyle::Text,
        series: 0,
        lines: vec![vec![Run::plain("A")]],
    })
}

fn shape_item() -> Item {
    Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect: rect(0, 0, 10, 10),
    })
}

fn marker_item() -> Option<Item> {
    Some(Item::MarkerRef(MarkerRefItem {
        marker: MarkerName::new("arrowhead")?,
        at: Point { x: 0, y: 0 },
        axis: MarkerAxis::PlusX,
    }))
}

fn symbol_item() -> Option<Item> {
    Some(Item::SymbolRef(SymbolRefItem {
        symbol: SymbolName::new("disc")?,
        at: Point { x: 0, y: 0 },
        style: ShapeStyle::Ink,
    }))
}

fn two_node_dump() -> Dump {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    dump.boxes.push(node("A"));
    let mut b = node("B");
    b.rect.y = 20;
    dump.boxes.push(b);
    dump.routes.push(SceneRoute {
        id: String::from("e0"),
        from: String::from("A"),
        to: String::from("B"),
        orthogonal: true,
        points: vec![Point { x: 0, y: 10 }, Point { x: 0, y: 20 }],
        marker_start: String::new(),
        marker_end: String::new(),
        stroke: String::new(),
    });
    dump
}

fn group(role: GroupRole, owner: &str, items: Vec<Item>) -> Group {
    Group::new(role, owner).with_items(items)
}

#[test]
fn every_shape_style_is_a_shape_row_of_the_table() {
    let table: Vec<&str> = r#gen::styles::STYLES
        .iter()
        .filter(|row| row.class == StyleClass::Shape.code())
        .map(|row| row.name)
        .collect();
    let names: Vec<&str> = [
        ShapeStyle::Node,
        ShapeStyle::Group,
        ShapeStyle::Band,
        ShapeStyle::Note,
        ShapeStyle::Edge,
        ShapeStyle::Rule,
        ShapeStyle::Mark,
        ShapeStyle::MarkHollow,
        ShapeStyle::Ink,
        ShapeStyle::InkLine,
        ShapeStyle::Series,
        ShapeStyle::SeriesLine,
        ShapeStyle::SeriesTint,
        ShapeStyle::SeriesFlow,
        ShapeStyle::Error,
        ShapeStyle::Warning,
        ShapeStyle::Success,
        ShapeStyle::Plate,
    ]
    .iter()
    .map(|style| style.name())
    .collect();
    assert_eq!(names.len(), table.len());
    for name in names {
        assert!(table.contains(&name), "{name} is not a shape row");
    }
}

#[test]
fn every_text_style_is_a_text_row_of_the_table() {
    let table: Vec<&str> = r#gen::styles::STYLES
        .iter()
        .filter(|row| row.class == StyleClass::Text.code())
        .map(|row| row.name)
        .collect();
    let names: Vec<&str> = [
        TextStyle::Text,
        TextStyle::TextMuted,
        TextStyle::TextInverse,
        TextStyle::TextOnSeries,
    ]
    .iter()
    .map(|style| style.name())
    .collect();
    assert_eq!(names.len(), table.len());
    for name in names {
        assert!(table.contains(&name), "{name} is not a text row");
    }
}

#[test]
fn profile_and_direction_names_are_fixed() {
    assert_eq!(Profile::Vector.as_str(), "vector");
    assert_eq!(Profile::Cell.as_str(), "cell");
    assert_eq!(Direction::Tb.as_str(), "TB");
    assert_eq!(Direction::Bt.as_str(), "BT");
    assert_eq!(Direction::Lr.as_str(), "LR");
    assert_eq!(Direction::Rl.as_str(), "RL");
    assert_eq!(Profile::default(), Profile::Vector);
    assert_eq!(Direction::default(), Direction::Tb);
}

#[test]
fn td_resolves_to_tb() {
    assert_eq!(Direction::from_token("TD"), Some(Direction::Tb));
    assert_eq!(Direction::from_token("tb"), Some(Direction::Tb));
    assert_eq!(Direction::from_token(" RL "), Some(Direction::Rl));
    assert_eq!(Direction::from_token("TB"), Some(Direction::Tb));
    assert_eq!(Direction::from_token("XX"), None);
    assert_eq!(Direction::from_token(""), None);
}

#[test]
fn limits_defaults_match_the_dump_spec() {
    let limits = Limits::default();
    assert_eq!(limits.max_nodes, 2000);
    assert_eq!(limits.max_edges, 5000);
    assert_eq!(limits.max_text_bytes, 1_048_576);
    let options = DumpOptions::default();
    assert_eq!(options.thoroughness, 3);
    assert_eq!(options.max_width, 0);
    assert!(
        options.config.is_empty(),
        "default dump options must have no config entries: {options:?}"
    );
}

#[test]
fn series_lines_never_rest_on_colour_alone() {
    let kinds: Vec<Line> = (0..12u8).map(Line::for_series).collect();
    assert_eq!(kinds[0], Line::Solid);
    assert_eq!(kinds[1], Line::Dashed);
    assert_eq!(kinds[2], Line::Dotted);
    assert_eq!(kinds[3], Line::Solid);
    assert_eq!(kinds[11], Line::Dotted);
    assert_eq!(Line::Dotted.as_str(), "dotted");
    assert_eq!(Line::Double.as_str(), "double");
    assert_eq!(Line::default(), Line::Solid);
    assert_eq!(Width::default(), Width::Normal);
}

#[test]
fn marker_names_are_checked_against_the_table() {
    let arrowhead = MarkerName::new("arrowhead").map(MarkerName::as_str);
    assert_eq!(arrowhead, Some("arrowhead"));
    assert_eq!(MarkerName::new("no-such-marker"), None);
    let paint = MarkerName::new("point").and_then(MarkerName::paint);
    assert_eq!(paint, Some("filled"));
    let hollow = MarkerName::new("extension").and_then(MarkerName::paint);
    assert_eq!(hollow, Some("hollow"));
    let open = MarkerName::new("openArrow").and_then(MarkerName::paint);
    assert_eq!(open, Some("open"));
}

#[test]
fn symbol_names_are_checked_against_the_table() {
    let disc = SymbolName::new("disc").map(SymbolName::as_str);
    assert_eq!(disc, Some("disc"));
    assert_eq!(SymbolName::new("no-such-symbol"), None);
    assert_eq!(
        SymbolName::new("disc").and_then(SymbolName::unicode),
        Some('●')
    );
    assert_eq!(
        SymbolName::new("disc").and_then(SymbolName::ascii),
        Some('*')
    );
    assert_eq!(
        SymbolName::new("bullseye").and_then(SymbolName::ascii),
        Some('@')
    );
}

#[test]
fn item_classes_follow_the_closed_order() {
    assert_eq!(shape_item().class(), ItemClass::Shape);
    assert_eq!(
        marker_item().map(|item| item.class()),
        Some(ItemClass::Marker)
    );
    assert_eq!(
        symbol_item().map(|item| item.class()),
        Some(ItemClass::Symbol)
    );
    assert_eq!(text_item().class(), ItemClass::Text);
    assert!(
        ItemClass::Shape < ItemClass::Marker,
        "shapes must precede markers: {:?}, {:?}",
        ItemClass::Shape,
        ItemClass::Marker
    );
    assert!(
        ItemClass::Marker < ItemClass::Symbol,
        "markers must precede symbols: {:?}, {:?}",
        ItemClass::Marker,
        ItemClass::Symbol
    );
    assert!(
        ItemClass::Symbol < ItemClass::Text,
        "symbols must precede text: {:?}, {:?}",
        ItemClass::Symbol,
        ItemClass::Text
    );
}

#[test]
fn shape_builders_change_one_field_at_a_time() {
    let shape = Shape::plain(ShapeStyle::SeriesLine)
        .with_series(4)
        .with_line(Line::for_series(4))
        .with_width(Width::Emphasis);
    assert_eq!(shape.style, ShapeStyle::SeriesLine);
    assert_eq!(shape.series, 4);
    assert_eq!(shape.line, Line::Dashed);
    assert_eq!(shape.width, Width::Emphasis);
    let plain = Shape::plain(ShapeStyle::Node);
    assert_eq!(plain.series, 0);
    assert_eq!(plain.width, Width::Normal);
    assert_eq!(plain.line, Line::Solid);
}

#[test]
fn roles_and_alignments_have_fixed_names() {
    assert_eq!(TextRole::Title.as_str(), "title");
    assert_eq!(TextRole::Label.as_str(), "label");
    assert_eq!(TextRole::Body.as_str(), "body");
    assert_eq!(Align::Start.as_str(), "start");
    assert_eq!(Align::Middle.as_str(), "middle");
    assert_eq!(Align::End.as_str(), "end");
}

#[test]
fn group_and_box_roles_have_fixed_names() {
    assert_eq!(GroupRole::Decor.as_str(), "decor");
    assert_eq!(GroupRole::Group.as_str(), "group");
    assert_eq!(GroupRole::Edge.as_str(), "edge");
    assert_eq!(GroupRole::Node.as_str(), "node");
    assert_eq!(BoxRole::Node.as_str(), "node");
    assert_eq!(BoxRole::Group.as_str(), "group");
    assert_eq!(BoxRole::from_name("group"), Some(BoxRole::Group));
    assert_eq!(BoxRole::from_name("frame"), None);
    assert_eq!(MarkerAxis::MinusY.as_str(), "-y");
    assert_eq!(ItemClass::Text.as_str(), "text");
    assert_eq!(StyleClass::Text.code(), 1);
}

#[test]
fn scene_reports_its_parts() {
    let dump = two_node_dump();
    let scene = Scene::new(
        Size { w: 30, h: 40 },
        dump,
        vec![group(GroupRole::Node, "A", vec![shape_item()])],
    );
    assert_eq!(scene.canvas(), Size { w: 30, h: 40 });
    assert_eq!(scene.profile(), Profile::Vector);
    assert_eq!(scene.boxes().len(), 2);
    assert_eq!(scene.routes().len(), 1);
    assert!(
        scene.labels().is_empty(),
        "two-node scene must have no route labels: {:?}",
        scene.labels()
    );
    assert_eq!(scene.items().len(), 1);
    assert_eq!(scene.dump_part().kind, "flowchart");
    assert!(
        scene.check().unwrap_or(false),
        "two-node scene must satisfy hard constraints: {scene:?}"
    );
}

#[test]
fn a_well_ordered_scene_passes_the_group_rules() {
    let dump = two_node_dump();
    let groups = vec![
        group(GroupRole::Decor, "", vec![shape_item()]),
        group(GroupRole::Edge, "e0", vec![shape_item()]),
        group(GroupRole::Node, "A", vec![shape_item(), text_item()]),
        group(GroupRole::Node, "B", vec![text_item()]),
        group(GroupRole::Decor, "", vec![text_item()]),
    ];
    assert_eq!(check_groups(&groups, &dump), Ok(()));
}

#[test]
fn a_decor_group_in_the_middle_is_rejected() {
    let dump = two_node_dump();
    let groups = vec![
        group(GroupRole::Node, "A", Vec::new()),
        group(GroupRole::Decor, "", Vec::new()),
        group(GroupRole::Node, "B", Vec::new()),
    ];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::UnexpectedDecor { group: 1 })
    );
}

#[test]
fn a_decor_group_with_an_owner_is_rejected() {
    let dump = two_node_dump();
    let groups = vec![group(GroupRole::Decor, "A", Vec::new())];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::DecorOwner {
            group: 0,
            owner: String::from("A"),
        })
    );
}

#[test]
fn groups_must_follow_dump_order() {
    let mut dump = two_node_dump();
    dump.routes.clear();
    let groups = vec![
        group(GroupRole::Node, "B", Vec::new()),
        group(GroupRole::Node, "A", Vec::new()),
    ];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::OwnerMismatch {
            group: 0,
            expected: "node",
            owner_expected: String::from("A"),
            owner: String::from("B"),
        })
    );
}

#[test]
fn groups_must_follow_the_role_order() {
    let dump = two_node_dump();
    let groups = vec![
        group(GroupRole::Node, "A", Vec::new()),
        group(GroupRole::Edge, "e0", Vec::new()),
        group(GroupRole::Node, "B", Vec::new()),
    ];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::OwnerMismatch {
            group: 0,
            expected: "edge",
            owner_expected: String::from("e0"),
            owner: String::from("A"),
        })
    );
}

#[test]
fn a_missing_group_is_rejected() {
    let dump = two_node_dump();
    let groups = vec![
        group(GroupRole::Edge, "e0", Vec::new()),
        group(GroupRole::Node, "A", Vec::new()),
    ];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::MissingGroup {
            role: "node",
            id: String::from("B"),
        })
    );
}

#[test]
fn an_extra_group_is_rejected() {
    let dump = two_node_dump();
    let groups = vec![
        group(GroupRole::Edge, "e0", Vec::new()),
        group(GroupRole::Node, "A", Vec::new()),
        group(GroupRole::Node, "B", Vec::new()),
        group(GroupRole::Edge, "e1", Vec::new()),
    ];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::UnexpectedGroup {
            group: 3,
            role: "edge",
        })
    );
}

#[test]
fn item_classes_must_not_decrease() {
    let dump = two_node_dump();
    let groups = vec![group(GroupRole::Node, "A", vec![text_item(), shape_item()])];
    assert_eq!(
        check_groups(&groups, &dump),
        Err(GroupOrder::ItemOrder {
            group: 0,
            earlier: "text",
            later: "shape",
        })
    );
}

#[test]
fn scene_is_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Scene>();
    assert_send_sync::<Dump>();
    assert_send_sync::<Group>();
}
