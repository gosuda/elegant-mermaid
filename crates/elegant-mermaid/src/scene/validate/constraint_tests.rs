use super::*;
use crate::geom::Size;
use crate::scene::{BoxRole, Dump, DumpOptions, SceneBox, SceneLabel, SceneRoute};

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn point(x: i32, y: i32) -> Point {
    Point { x, y }
}

fn bbox(id: &str, r: Rect) -> SceneBox {
    SceneBox {
        id: id.to_owned(),
        role: BoxRole::Node,
        rect: r,
        parent: String::new(),
        exclusive: true,
    }
}

fn route(id: &str, from: &str, to: &str, points: Vec<Point>) -> SceneRoute {
    SceneRoute {
        id: id.to_owned(),
        from: from.to_owned(),
        to: to.to_owned(),
        orthogonal: true,
        points,
        marker_start: String::new(),
        marker_end: String::new(),
        stroke: String::new(),
    }
}

fn label(id: &str, owner: &str, r: Rect) -> SceneLabel {
    SceneLabel {
        id: id.to_owned(),
        owner: owner.to_owned(),
        text: String::from("x"),
        rect: r,
        lines: vec![String::from("x")],
    }
}

fn canvas() -> Size {
    Size { w: 100, h: 100 }
}

/// Two disjoint nodes, one route between them, and one label in the gap.
fn valid_dump() -> Dump {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    dump.boxes.push(bbox("A", rect(0, 0, 20, 20)));
    dump.boxes.push(bbox("B", rect(0, 60, 20, 20)));
    dump.routes
        .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
    dump.labels
        .push(label("e0.label", "e0", rect(0, 30, 8, 10)));
    dump
}

fn failure(dump: &Dump) -> Option<Clause> {
    validate(canvas(), dump).unwrap_or(None)
}

fn malformed(dump: &Dump) -> Option<Malformed> {
    well_formed(canvas(), dump).err()
}

#[test]
fn a_valid_dump_passes_every_clause() {
    let dump = valid_dump();
    assert_eq!(failure(&dump), None);
    assert!(
        check(canvas(), &dump).unwrap_or(false),
        "valid fixture must pass all clauses; canvas: {:?}, dump: {dump:?}",
        canvas()
    );
    assert_eq!(well_formed(canvas(), &dump), Ok(()));
}

#[test]
fn clause_ids_and_messages_are_fixed_and_in_order() {
    let ids: Vec<&str> = CLAUSES.iter().map(|c| c.id()).collect();
    assert_eq!(
        ids,
        [
            "canvas",
            "exclusive-siblings",
            "parent",
            "orthogonal",
            "ports",
            "route-clearance",
            "label-clearance",
            "frame-clearance"
        ]
    );
    let messages: Vec<&str> = CLAUSES.iter().map(|c| c.message()).collect();
    assert_eq!(
        messages,
        [
            "box outside canvas",
            "exclusive sibling boxes overlap",
            "box outside its parent",
            "orthogonal route has a diagonal segment",
            "route end is off its box boundary",
            "route crosses an exclusive box",
            "label overlaps an exclusive box",
            "group frame overlaps a foreign box or label"
        ]
    );
    assert_eq!(
        Clause::Canvas.report(),
        "invalid canvas: box outside canvas"
    );
    assert_eq!(
        Clause::Ports.report(),
        "invalid ports: route end is off its box boundary"
    );
    assert_eq!(format!("{}", Clause::LabelClearance), "label-clearance");
    assert_eq!(
        Clause::FrameClearance.report(),
        "invalid frame-clearance: group frame overlaps a foreign box or label"
    );
}

#[test]
fn clause_canvas_rejects_a_box_outside_the_canvas() {
    let mut dump = valid_dump();
    if let Some(b) = dump.boxes.get_mut(1) {
        b.rect = rect(0, 90, 20, 20);
    }
    if let Some(r) = dump.routes.first_mut() {
        r.points = vec![point(10, 20), point(10, 90)];
    }
    assert_eq!(failure(&dump), Some(Clause::Canvas));
}

#[test]
fn clause_exclusive_siblings_rejects_overlapping_siblings() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("C", rect(10, 10, 20, 20)));
    assert_eq!(failure(&dump), Some(Clause::ExclusiveSiblings));
}

#[test]
fn clause_exclusive_siblings_ignores_touching_boxes() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("C", rect(20, 0, 20, 20)));
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_exclusive_siblings_ignores_a_non_exclusive_box() {
    let mut dump = valid_dump();
    let mut shared = bbox("C", rect(10, 10, 20, 20));
    shared.exclusive = false;
    dump.boxes.push(shared);
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_exclusive_siblings_keeps_boxes_of_other_parents() {
    let mut dump = valid_dump();
    let mut frame = bbox("G", rect(0, 0, 40, 40));
    frame.exclusive = false;
    dump.boxes.push(frame);
    let mut other = bbox("C", rect(10, 10, 20, 20));
    other.parent = String::from("G");
    dump.boxes.push(other);
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_parent_rejects_a_box_outside_its_parent() {
    let mut dump = valid_dump();
    let mut frame = bbox("G", rect(40, 0, 40, 40));
    frame.role = BoxRole::Group;
    frame.exclusive = false;
    dump.boxes.push(frame);
    let mut child = bbox("C", rect(40, 0, 20, 20));
    child.parent = String::from("G");
    dump.boxes.push(child);
    assert_eq!(failure(&dump), None);
    if let Some(b) = dump.boxes.get_mut(2) {
        b.rect = rect(70, 30, 20, 20);
    }
    assert_eq!(failure(&dump), Some(Clause::Parent));
}

#[test]
fn clause_orthogonal_rejects_a_diagonal_segment() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points = vec![point(10, 20), point(12, 60)];
    }
    assert_eq!(failure(&dump), Some(Clause::Orthogonal));
}

#[test]
fn clause_orthogonal_passes_a_diagonal_route_that_is_not_marked() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.orthogonal = false;
        r.points = vec![point(10, 20), point(12, 60)];
    }
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_ports_rejects_a_route_end_off_the_boundary() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points = vec![point(10, 20), point(10, 55)];
    }
    assert_eq!(failure(&dump), Some(Clause::Ports));
}

#[test]
fn clause_ports_rejects_an_endpoint_inside_the_box() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points = vec![point(10, 20), point(10, 50)];
    }
    assert_eq!(failure(&dump), Some(Clause::Ports));
}

#[test]
fn clause_ports_rejects_a_route_without_points() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points = Vec::new();
    }
    assert_eq!(failure(&dump), Some(Clause::Ports));
}

#[test]
fn clause_ports_accepts_a_corner_end() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.orthogonal = false;
        r.points = vec![point(0, 20), point(0, 60)];
    }
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_route_clearance_rejects_a_route_through_a_box() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("C", rect(0, 30, 20, 20)));
    assert_eq!(failure(&dump), Some(Clause::RouteClearance));
}

#[test]
fn clause_route_clearance_ignores_a_box_in_the_scope() {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    let mut frame = bbox("G", rect(0, 0, 40, 100));
    frame.role = BoxRole::Group;
    dump.boxes.push(frame);
    let mut a = bbox("A", rect(0, 0, 20, 20));
    a.parent = String::from("G");
    dump.boxes.push(a);
    let mut b = bbox("B", rect(0, 60, 20, 20));
    b.parent = String::from("G");
    dump.boxes.push(b);
    dump.routes
        .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_route_clearance_ignores_a_zero_area_box() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("C", rect(0, 35, 0, 0)));
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_label_clearance_rejects_a_label_over_a_box() {
    let mut dump = valid_dump();
    if let Some(l) = dump.labels.first_mut() {
        l.rect = rect(10, 10, 8, 5);
    }
    assert_eq!(failure(&dump), Some(Clause::LabelClearance));
}

#[test]
fn clause_label_clearance_ignores_a_group_in_the_owner_ancestors() {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    let mut frame = bbox("G", rect(0, 0, 40, 40));
    frame.role = BoxRole::Group;
    dump.boxes.push(frame);
    let mut a = bbox("A", rect(0, 0, 20, 20));
    a.parent = String::from("G");
    dump.boxes.push(a);
    dump.labels
        .push(label("G.title", "A", rect(25, 25, 10, 10)));
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_label_clearance_ignores_a_box_owner_ancestor() {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    let mut frame = bbox("G", rect(0, 0, 40, 40));
    frame.role = BoxRole::Group;
    dump.boxes.push(frame);
    let mut a = bbox("A", rect(0, 0, 20, 20));
    a.parent = String::from("G");
    dump.boxes.push(a);
    dump.labels
        .push(label("A.title", "A", rect(25, 25, 10, 10)));
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_label_clearance_accepts_a_label_inside_its_own_exclusive_box() {
    let mut dump = valid_dump();
    if let Some(l) = dump.labels.first_mut() {
        l.owner = String::from("A");
        l.rect = rect(2, 2, 8, 5);
    }
    assert_eq!(failure(&dump), None);
}

#[test]
fn clause_label_clearance_prefers_a_route_when_box_and_route_ids_collide() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("e0", rect(50, 0, 20, 20)));
    dump.labels.clear();
    dump.labels.push(label("l", "e0", rect(52, 2, 8, 5)));
    assert_eq!(failure(&dump), Some(Clause::LabelClearance));
}

fn group(id: &str, r: Rect, parent: &str) -> SceneBox {
    SceneBox {
        role: BoxRole::Group,
        parent: parent.to_owned(),
        exclusive: false,
        ..bbox(id, r)
    }
}

/// A frame with one member, and one foreign node away from the frame.
fn frame_dump() -> Dump {
    let mut dump = Dump::new("flowchart", DumpOptions::default());
    dump.boxes.push(group("G", rect(0, 0, 40, 40), ""));
    let mut member = bbox("N", rect(5, 5, 10, 10));
    member.parent = String::from("G");
    dump.boxes.push(member);
    dump.boxes.push(bbox("F", rect(60, 0, 10, 10)));
    dump
}

fn frame_failure(change: impl FnOnce(&mut Dump)) -> Option<Clause> {
    let mut dump = frame_dump();
    change(&mut dump);
    failure(&dump)
}

fn frame_label(r: Rect) -> impl FnOnce(&mut Dump) {
    move |dump| dump.labels.push(label("l", "N", r))
}

#[test]
fn clause_frame_clearance_accepts_members_and_distant_boxes() {
    assert_eq!(frame_failure(|_| {}), None);
}

#[test]
fn clause_frame_clearance_rejects_a_foreign_node_in_the_frame() {
    let overlapping = frame_failure(|d| d.boxes[2].rect = rect(30, 30, 20, 20));
    let inside = frame_failure(|d| d.boxes[2].rect = rect(20, 20, 10, 10));
    assert_eq!(overlapping, Some(Clause::FrameClearance));
    assert_eq!(inside, Some(Clause::FrameClearance));
}

#[test]
fn clause_frame_clearance_accepts_a_foreign_node_that_touches_the_frame() {
    assert_eq!(
        frame_failure(|d| d.boxes[2].rect = rect(40, 0, 10, 10)),
        None
    );
}

#[test]
fn clause_frame_clearance_compares_sibling_frames() {
    let overlapping = frame_failure(|d| d.boxes.push(group("H", rect(30, 0, 40, 40), "")));
    let disjoint = frame_failure(|d| d.boxes.push(group("H", rect(40, 0, 20, 40), "")));
    assert_eq!(overlapping, Some(Clause::FrameClearance));
    assert_eq!(disjoint, None);
}

#[test]
fn clause_frame_clearance_skips_nested_frames() {
    let nested = frame_failure(|d| {
        d.boxes.push(group("H", rect(2, 2, 30, 30), "G"));
        d.boxes[1].parent = String::from("H");
    });
    assert_eq!(nested, None);
}

#[test]
fn clause_frame_clearance_compares_a_frame_with_the_nested_frame_of_another() {
    let failed = frame_failure(|d| {
        d.boxes.push(group("P", rect(30, 30, 60, 60), ""));
        d.boxes.push(group("Q", rect(35, 35, 20, 20), "P"));
    });
    assert_eq!(failed, Some(Clause::FrameClearance));
}

#[test]
fn clause_frame_clearance_accepts_a_label_strictly_inside_or_disjoint() {
    assert_eq!(frame_failure(frame_label(rect(10, 20, 10, 5))), None);
    assert_eq!(frame_failure(frame_label(rect(60, 50, 5, 5))), None);
    assert_eq!(frame_failure(frame_label(rect(40, 20, 10, 5))), None);
}

#[test]
fn clause_frame_clearance_rejects_a_label_on_a_frame_border() {
    for r in [
        rect(35, 20, 10, 5),
        rect(0, 20, 10, 5),
        rect(10, 35, 10, 5),
        rect(10, 0, 10, 5),
    ] {
        assert_eq!(
            frame_failure(frame_label(r)),
            Some(Clause::FrameClearance),
            "{r:?}"
        );
    }
}

#[test]
fn clause_frame_clearance_follows_label_clearance() {
    let failed = frame_failure(|d| {
        d.boxes[2].rect = rect(36, 36, 10, 10);
        d.labels.push(label("l", "N", rect(36, 36, 10, 10)));
    });
    assert_eq!(failed, Some(Clause::LabelClearance));
}

#[test]
fn clause_order_reports_the_earlier_clause_when_two_fail() {
    let mut dump = valid_dump();
    dump.boxes.push(bbox("C", rect(10, 10, 20, 20)));
    if let Some(l) = dump.labels.first_mut() {
        l.rect = rect(10, 10, 8, 5);
    }
    assert_eq!(failure(&dump), Some(Clause::ExclusiveSiblings));
    if let Some(b) = dump.boxes.get_mut(1) {
        b.rect = rect(0, 90, 20, 20);
    }
    assert_eq!(failure(&dump), Some(Clause::Canvas));
}

#[test]
fn clause_order_reports_ports_before_route_clearance() {
    let mut dump = valid_dump();
    if let Some(r) = dump.routes.first_mut() {
        r.points = vec![point(10, 25), point(10, 55)];
    }
    assert_eq!(failure(&dump), Some(Clause::Ports));
}

#[path = "malformed_tests.rs"]
mod malformed_tests;
