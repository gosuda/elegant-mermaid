use super::{
    ArchAlign, ArchEdge, ArchGroup, ArchInput, ArchLayout, ArchNode, ArchParams, architecture,
};
use crate::geom::{COORD_LIMIT, GeomError, Rect, Size};
use crate::layout::input::RouteSide;

fn params() -> ArchParams {
    ArchParams {
        pitch_x: 7680,
        pitch_y: 7680,
        label_wrap: 7168,
        icon_w: 5120,
        icon_h: 5120,
        padding: 2560,
        line_height: 1280,
        badge: 1536,
        inset: 768,
        label_gap: 256,
        thickness: 0,
        margin: 1024,
        gutter: 0,
        fuel: 2000,
        ring_cap: 4,
    }
}

fn node(parent: Option<usize>) -> ArchNode {
    ArchNode {
        parent,
        junction: false,
        icon: Size { w: 5120, h: 5120 },
        label: Size { w: 0, h: 0 },
    }
}

fn edge(from: usize, to: usize, from_side: RouteSide, to_side: RouteSide) -> ArchEdge {
    ArchEdge {
        from,
        to,
        from_side,
        to_side,
        label: Size { w: 0, h: 0 },
    }
}

fn run(input: &ArchInput) -> ArchLayout {
    let result = architecture(input, params());
    assert!(result.is_ok(), "layout: {result:?}");
    result.unwrap_or_else(|_| unreachable!("layout success asserted above"))
}

fn overlap(a: Rect, b: Rect) -> bool {
    a.x < b.x + b.w && b.x < a.x + a.w && a.y < b.y + b.h && b.y < a.y + a.h
}

fn strictly_contains(outer: Rect, inner: Rect) -> bool {
    outer.x < inner.x
        && inner.x + inner.w < outer.x + outer.w
        && outer.y < inner.y
        && inner.y + inner.h < outer.y + outer.h
}

#[test]
fn chain_follows_edge_sides() {
    let input = ArchInput {
        nodes: vec![node(None), node(None), node(None)],
        edges: vec![
            edge(0, 1, RouteSide::Right, RouteSide::Left),
            edge(1, 2, RouteSide::Down, RouteSide::Up),
        ],
        ..ArchInput::default()
    };
    let out = run(&input);
    let (a, b, c) = (out.boxes[0], out.boxes[1], out.boxes[2]);
    assert_eq!(a.y, b.y);
    assert_eq!(b.x - a.x, 7680);
    assert_eq!(b.x, c.x);
    assert_eq!(c.y - b.y, 7680);
}

#[test]
fn routes_use_gutter_lines() {
    let input = ArchInput {
        nodes: vec![node(None), node(None)],
        edges: vec![edge(0, 1, RouteSide::Right, RouteSide::Left)],
        ..ArchInput::default()
    };
    let out = run(&input);
    let route = &out.routes[0];
    assert_eq!(route.len(), 3);
    let (a, b) = (out.boxes[0], out.boxes[1]);
    assert_eq!((route[0].x, route[0].y), (a.x + a.w, a.y + a.h / 2));
    assert_eq!((route[2].x, route[2].y), (b.x, b.y + b.h / 2));
    assert_eq!(route[1].y, route[0].y);
    assert_eq!(route[1].y, route[2].y);
}

#[test]
fn perpendicular_route_has_one_elbow() {
    let input = ArchInput {
        nodes: vec![node(None), node(None)],
        edges: vec![edge(0, 1, RouteSide::Right, RouteSide::Up)],
        ..ArchInput::default()
    };
    let out = run(&input);
    assert_eq!(out.routes[0].len(), 5);
    for pair in out.routes[0].windows(2) {
        assert!(pair[0].x == pair[1].x || pair[0].y == pair[1].y);
    }
}

#[test]
fn ports_spread_along_one_side() {
    let input = ArchInput {
        nodes: vec![node(None), node(None), node(None)],
        edges: vec![
            edge(0, 1, RouteSide::Right, RouteSide::Left),
            edge(0, 2, RouteSide::Right, RouteSide::Left),
        ],
        ..ArchInput::default()
    };
    let out = run(&input);
    let (first, second) = (out.routes[0][0], out.routes[1][0]);
    let icon = out.icons[0];
    assert_eq!(first.x, second.x);
    assert_eq!(first.y, icon.y + icon.h / 3);
    assert_eq!(second.y, icon.y + 2 * icon.h / 3);
}

#[test]
fn group_frames_are_disjoint_and_contain_members() {
    let input = ArchInput {
        groups: vec![
            ArchGroup {
                parent: None,
                title: Size { w: 2560, h: 1280 },
                icon: true,
            },
            ArchGroup {
                parent: None,
                title: Size { w: 0, h: 0 },
                icon: false,
            },
            ArchGroup {
                parent: Some(0),
                title: Size { w: 0, h: 0 },
                icon: false,
            },
        ],
        nodes: vec![node(Some(0)), node(Some(1)), node(Some(2)), node(None)],
        edges: vec![
            edge(0, 1, RouteSide::Right, RouteSide::Left),
            edge(1, 2, RouteSide::Right, RouteSide::Left),
            edge(2, 3, RouteSide::Down, RouteSide::Up),
        ],
        ..ArchInput::default()
    };
    let out = run(&input);
    let frames = &out.frames;
    assert!(!overlap(frames[0], frames[1]));
    assert!(strictly_contains(frames[0], frames[2]));
    assert!(strictly_contains(frames[0], out.boxes[0]));
    assert!(strictly_contains(frames[1], out.boxes[1]));
    assert!(strictly_contains(frames[2], out.boxes[2]));
    assert!(!overlap(frames[0], out.boxes[3]));
    assert!(!overlap(frames[1], out.boxes[3]));
    assert!(strictly_contains(frames[0], out.titles[0]));
    assert_eq!(out.group_icons[0].w, 1536);
}

#[test]
fn empty_group_keeps_a_frame() {
    let input = ArchInput {
        groups: vec![ArchGroup {
            parent: None,
            title: Size { w: 0, h: 0 },
            icon: false,
        }],
        nodes: vec![node(None)],
        ..ArchInput::default()
    };
    let out = run(&input);
    assert!(out.frames[0].w > 0);
    assert!(!overlap(out.frames[0], out.boxes[0]));
}

#[test]
fn align_forces_one_row() {
    let input = ArchInput {
        nodes: vec![node(None), node(None), node(None)],
        edges: vec![
            edge(0, 1, RouteSide::Right, RouteSide::Left),
            edge(1, 2, RouteSide::Down, RouteSide::Up),
        ],
        aligns: vec![ArchAlign {
            column: false,
            members: vec![0, 2],
        }],
        ..ArchInput::default()
    };
    let out = run(&input);
    assert_eq!(out.boxes[0].y, out.boxes[2].y);
    let loose = run(&ArchInput {
        aligns: Vec::new(),
        ..input
    });
    assert_ne!(loose.boxes[0].y, loose.boxes[2].y);
}

#[test]
fn disconnected_components_sit_right_of_the_first() {
    let input = ArchInput {
        nodes: vec![node(None), node(None)],
        ..ArchInput::default()
    };
    let out = run(&input);
    assert_eq!(out.boxes[0].y, out.boxes[1].y);
    assert_eq!(out.boxes[1].x - out.boxes[0].x, 2 * 7680);
}

#[test]
fn labels_widen_the_pitch() {
    let mut input = ArchInput {
        nodes: vec![node(None), node(None), node(None)],
        ..ArchInput::default()
    };
    input.nodes[0].label = Size { w: 9000, h: 2560 };
    let out = run(&input);
    assert!(out.boxes[1].x - out.boxes[0].x >= 9000 + 7680 - 7168);
    let label = out.labels[0];
    assert_eq!(label.y, out.icons[0].y + out.icons[0].h);
    assert_eq!(out.boxes[0].h, out.icons[0].h + label.h);
}

#[test]
fn edge_labels_stay_off_nodes() {
    let mut e = edge(0, 1, RouteSide::Right, RouteSide::Left);
    e.label = Size { w: 2560, h: 1280 };
    let input = ArchInput {
        nodes: vec![node(None), node(None)],
        edges: vec![e],
        ..ArchInput::default()
    };
    let out = run(&input);
    let label = out.edge_labels[0];
    assert_eq!(label.w, 2560);
    for b in &out.boxes {
        assert!(!overlap(label, *b));
    }
}

#[test]
fn fuel_stops_the_queue_and_seeds_the_rest() -> Result<(), GeomError> {
    let input = ArchInput {
        nodes: vec![node(None), node(None), node(None)],
        edges: vec![
            edge(0, 1, RouteSide::Right, RouteSide::Left),
            edge(1, 2, RouteSide::Right, RouteSide::Left),
        ],
        ..ArchInput::default()
    };
    let mut p = params();
    p.fuel = 1;
    let out = architecture(&input, p)?;
    assert!(out.budget);
    assert_eq!(out.boxes.len(), 3);
    for i in 0..out.boxes.len() {
        for j in i + 1..out.boxes.len() {
            assert!(!overlap(out.boxes[i], out.boxes[j]));
        }
    }
    Ok(())
}

#[test]
fn invalid_input_is_a_domain_error() {
    let good = ArchInput {
        nodes: vec![node(None), node(None)],
        edges: vec![edge(0, 1, RouteSide::Right, RouteSide::Left)],
        ..ArchInput::default()
    };
    type Mutation = fn(&mut ArchInput, &mut ArchParams);
    let cases: [(&str, Mutation); 6] = [
        ("node parent", |i, _| i.nodes[0].parent = Some(3)),
        ("group parent", |i, _| {
            i.groups = vec![ArchGroup {
                parent: Some(0),
                title: Size { w: 0, h: 0 },
                icon: false,
            }];
        }),
        ("edge end", |i, _| i.edges[0].to = 9),
        ("align member", |i, _| {
            i.aligns = vec![ArchAlign {
                column: false,
                members: vec![0, 7],
            }];
        }),
        ("pitch", |_, p| p.pitch_x = 0),
        ("gutter", |_, p| p.gutter = 2),
    ];
    for (name, mutate) in cases {
        let mut input = good.clone();
        let mut p = params();
        mutate(&mut input, &mut p);
        assert_eq!(architecture(&input, p), Err(GeomError::Domain), "{name}");
    }
}

#[test]
fn overflow_is_reported() {
    let mut input = ArchInput {
        nodes: vec![node(None)],
        ..ArchInput::default()
    };
    input.nodes[0].label = Size {
        w: i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX),
        h: 1280,
    };
    assert_eq!(architecture(&input, params()), Err(GeomError::Overflow));
}
