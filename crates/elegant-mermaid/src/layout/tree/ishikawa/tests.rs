use super::{IshikawaParams, MAX_DEPTH, ishikawa};
use crate::geom::{
    GeomError, Point, Rect, floor_div, intersects, is_orthogonal, polyline_hits_rect,
};
use crate::layout::tree::{Layout, Node, normalize};

const CELL_FISH: IshikawaParams = IshikawaParams {
    spine_base: 40,
    rib_min: 12,
    rib_pool: 80,
    min_spacing: 4,
    bone_stub: 3,
    bone_base: 6,
    bone_per_child: 1,
    inset: 2,
    cos: 4561,
    sin: 32455,
};

const VECTOR_FISH: IshikawaParams = IshikawaParams {
    spine_base: 16000,
    rib_min: 4800,
    rib_pool: 32000,
    min_spacing: 1792,
    bone_stub: 1920,
    bone_base: 3840,
    bone_per_child: 320,
    inset: 1280,
    cos: 4561,
    sin: 32455,
};

fn node(parent: Option<usize>, width: i32, height: i32) -> Node {
    Node {
        parent,
        width,
        height,
    }
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn pts(xy: &[i32]) -> Vec<Point> {
    xy.chunks(2).map(|c| Point { x: c[0], y: c[1] }).collect()
}

fn depth_of(nodes: &[Node], mut i: usize) -> usize {
    let mut d = 0;
    while let Some(parent) = nodes[i].parent {
        i = parent;
        d += 1;
    }
    d
}

#[test]
fn effect_only() -> Result<(), GeomError> {
    let got = ishikawa(&[node(None, 6, 3)], CELL_FISH)?;
    assert_eq!(got.boxes, [rect(0, 39, 6, 3)]);
    assert_eq!(got.routes, [Vec::<Point>::new()]);
    Ok(())
}

#[test]
fn empty_input() -> Result<(), GeomError> {
    let got = ishikawa(&[], CELL_FISH)?;
    assert!(got.boxes.is_empty());
    assert!(got.routes.is_empty());
    Ok(())
}

#[test]
fn leaf_cause_shifts_left_by_its_reach() -> Result<(), GeomError> {
    let nodes = [node(None, 6, 3), node(Some(0), 5, 3)];
    let got = ishikawa(&nodes, CELL_FISH)?;
    assert_eq!(got.boxes, [rect(0, 39, 6, 3), rect(-5, 29, 5, 3)]);
    assert_eq!(got.routes[0], pts(&[-5, 40, 0, 40]));
    assert_eq!(got.routes[1], pts(&[-2, 40, -3, 32]));
    Ok(())
}

#[test]
fn both_sides_mirror_around_the_spine() -> Result<(), GeomError> {
    let nodes = [node(None, 6, 3), node(Some(0), 5, 3), node(Some(0), 5, 3)];
    let got = ishikawa(&nodes, CELL_FISH)?;
    assert_eq!(got.boxes[1], rect(-5, 29, 5, 3));
    assert_eq!(got.boxes[2], rect(-5, 48, 5, 3));
    assert_eq!(got.routes[2], pts(&[-2, 40, -3, 48]));
    Ok(())
}

#[test]
fn sub_causes_follow_the_upstream_slots() -> Result<(), GeomError> {
    let nodes = [
        node(None, 6, 3),
        node(Some(0), 5, 3),
        node(Some(1), 3, 1),
        node(Some(1), 3, 1),
    ];
    let got = ishikawa(&nodes, CELL_FISH)?;
    assert_eq!(got.boxes[0], rect(0, 79, 6, 3));
    assert_eq!(got.boxes[1], rect(-15, -3, 5, 3));
    assert_eq!(got.boxes[3], rect(-12, 54, 3, 1));
    assert_eq!(got.boxes[2], rect(-16, 27, 3, 1));
    assert_eq!(got.routes[1], pts(&[-2, 80, -13, 0]));
    assert_eq!(got.routes[3], pts(&[-6, 54, -9, 54]));
    assert_eq!(got.routes[2], pts(&[-10, 27, -13, 27]));
    assert_eq!(got.routes[0], pts(&[-16, 80, 0, 80]));
    Ok(())
}

#[test]
fn lower_side_keeps_declaration_order() -> Result<(), GeomError> {
    let nodes = [
        node(None, 6, 3),
        node(Some(0), 5, 3),
        node(Some(0), 5, 3),
        node(Some(2), 3, 1),
        node(Some(2), 3, 1),
    ];
    let got = ishikawa(&nodes, CELL_FISH)?;
    let (first, second) = (got.routes[3][1].y, got.routes[4][1].y);
    assert!(first < second);
    assert!(first > got.routes[0][0].y);
    Ok(())
}

#[test]
fn diagonal_bones_share_the_rib_slope() -> Result<(), GeomError> {
    let nodes = [
        node(None, 6, 3),
        node(Some(0), 5, 3),
        node(Some(1), 3, 1),
        node(Some(2), 3, 1),
        node(Some(3), 3, 1),
        node(Some(2), 3, 1),
    ];
    for params in [CELL_FISH, VECTOR_FISH] {
        let got = ishikawa(&nodes, params)?;
        for (i, route) in got.routes.iter().enumerate().take(nodes.len()).skip(1) {
            let dx = i64::from(route[1].x) - i64::from(route[0].x);
            let dy = i64::from(route[1].y) - i64::from(route[0].y);
            if dy == 0 {
                assert_eq!(depth_of(&nodes, i) % 2, 0, "horizontal bone of node {i}");
                continue;
            }
            assert_eq!(depth_of(&nodes, i) % 2, 1, "node {i}");
            let run = floor_div(dy.abs() * i64::from(params.cos), i64::from(params.sin));
            assert_eq!(dx, -run, "node {i}");
        }
    }
    Ok(())
}

#[test]
fn rejects_bad_input() {
    let root = node(None, 1, 1);
    let cases: [(&str, Vec<Node>); 4] = [
        ("rooted", vec![node(Some(0), 1, 1)]),
        ("empty box", vec![root, node(Some(0), 0, 1)]),
        ("orphan", vec![root, node(Some(5), 1, 1)]),
        (
            "off branch",
            vec![
                root,
                node(Some(0), 1, 1),
                node(Some(1), 1, 1),
                node(Some(1), 1, 1),
                node(Some(2), 1, 1),
            ],
        ),
    ];
    for (name, nodes) in cases {
        assert_eq!(
            ishikawa(&nodes, CELL_FISH).err(),
            Some(GeomError::Domain),
            "{name}"
        );
    }
    let bad = IshikawaParams {
        sin: 0,
        ..CELL_FISH
    };
    assert_eq!(ishikawa(&[root], bad).err(), Some(GeomError::Domain));
}

#[test]
fn rejects_too_deep_trees() -> Result<(), GeomError> {
    let mut nodes = vec![node(None, 1, 1)];
    for i in 1..=MAX_DEPTH + 1 {
        nodes.push(node(Some(i - 1), 1, 1));
    }
    ishikawa(&nodes[..=MAX_DEPTH], CELL_FISH)?;
    assert_eq!(ishikawa(&nodes, CELL_FISH).err(), Some(GeomError::Domain));
    Ok(())
}

struct Draw {
    state: u32,
}

impl Draw {
    fn next(&mut self, n: u32) -> u32 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        self.state % n
    }

    fn size(&mut self, max: u32) -> i32 {
        i32::try_from(1 + self.next(max)).unwrap_or(1)
    }
}

fn random_fish(seed: u32, max_nodes: u32, max_w: u32, max_h: u32) -> Vec<Node> {
    let mut d = Draw { state: seed };
    let count = 1 + d.next(max_nodes);
    let mut nodes = vec![node(None, d.size(max_w), d.size(max_h))];
    let mut path = vec![0usize];
    for i in 1..count as usize {
        let keep = 1 + d.next(u32::try_from(path.len()).unwrap_or(1)) as usize;
        path.truncate(keep);
        nodes.push(node(Some(path[keep - 1]), d.size(max_w), d.size(max_h)));
        path.push(i);
    }
    nodes
}

fn on_boundary(p: Point, r: Rect) -> bool {
    let inside = p.x >= r.x && p.x <= r.x + r.w && p.y >= r.y && p.y <= r.y + r.h;
    inside && (p.x == r.x || p.x == r.x + r.w || p.y == r.y || p.y == r.y + r.h)
}

fn check_fish(nodes: &[Node], params: IshikawaParams, margin: i32) -> Result<(), GeomError> {
    let mut got: Layout = ishikawa(nodes, params)?;
    let canvas = normalize(&mut got, margin)?;
    for (i, a) in got.boxes.iter().enumerate() {
        assert!(a.x >= 0 && a.y >= 0 && a.x + a.w <= canvas.w && a.y + a.h <= canvas.h);
        for (j, b) in got.boxes.iter().enumerate().skip(i + 1) {
            assert!(
                !intersects(*a, *b)?,
                "boxes {i} and {j} overlap: {a:?} {b:?}"
            );
        }
    }
    for (k, route) in got.routes.iter().enumerate() {
        let Some(last) = route.last() else {
            continue;
        };
        assert!(
            on_boundary(*last, got.boxes[k]),
            "route {k} ends off its box"
        );
        for (j, b) in got.boxes.iter().enumerate().filter(|(j, _)| *j != k) {
            assert!(
                !polyline_hits_rect(route, *b)?,
                "route {k} crosses box {j}: {route:?} {b:?}"
            );
        }
        if k == 0 || depth_of(nodes, k).is_multiple_of(2) {
            assert!(is_orthogonal(route), "route {k} is not orthogonal");
        }
    }
    Ok(())
}

#[test]
fn random_trees_stay_clear() -> Result<(), GeomError> {
    let profiles: [(IshikawaParams, i32, u32, u32); 4] = [
        (CELL_FISH, 1, 30, 6),
        (CELL_FISH, 1, 8, 25),
        (VECTOR_FISH, 1024, 20000, 8000),
        (VECTOR_FISH, 1024, 6000, 40000),
    ];
    for (params, margin, max_w, max_h) in profiles {
        for seed in 1..=400 {
            check_fish(&random_fish(seed, 40, max_w, max_h), params, margin)?;
        }
    }
    Ok(())
}

#[test]
fn wide_bushes_stay_clear() -> Result<(), GeomError> {
    for children in [1, 2, 7, 30] {
        for params in [CELL_FISH, VECTOR_FISH] {
            let mut nodes = vec![node(None, 6, 3), node(Some(0), 5, 3), node(Some(1), 4, 3)];
            for _ in 0..children {
                nodes.push(node(Some(2), 4, 7));
            }
            nodes.push(node(Some(0), 5, 3));
            check_fish(&nodes, params, 1)?;
        }
    }
    Ok(())
}
