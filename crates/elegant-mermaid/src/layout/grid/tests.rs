use super::{
    Block, Edge, GeomError, Input, Kind, Layout, MAX_DEPTH, MAX_TRACKS, Params, Point, Rect, Size,
    block,
};
use crate::geom;

const PARAMS: Params = Params {
    padding: 8,
    bend_cost: 64,
    line_thickness: 0,
};

fn leaf(parent: Option<usize>, span: i32, w: i32, h: i32) -> Block {
    Block {
        parent,
        kind: Kind::Leaf,
        span,
        columns: 0,
        size: Size { w, h },
    }
}

fn composite(parent: Option<usize>, columns: i32) -> Block {
    Block {
        parent,
        kind: Kind::Composite,
        span: 1,
        columns,
        size: Size { w: 0, h: 0 },
    }
}

fn space(parent: Option<usize>) -> Block {
    Block {
        parent,
        kind: Kind::Space,
        span: 1,
        columns: 0,
        size: Size { w: 0, h: 0 },
    }
}

fn input(columns: i32, blocks: Vec<Block>, edges: Vec<Edge>) -> Input {
    Input {
        columns,
        blocks,
        edges,
    }
}

fn edge(from: usize, to: usize) -> Edge {
    Edge {
        from,
        to,
        label: Size { w: 0, h: 0 },
    }
}

fn labelled(from: usize, to: usize) -> Edge {
    Edge {
        from,
        to,
        label: Size { w: 20, h: 8 },
    }
}

fn run(input: &Input) -> Layout {
    let layout = block(input, PARAMS);
    assert!(layout.is_ok(), "layout failed: {:?}", layout.as_ref().err());
    layout.unwrap_or(Layout {
        rects: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        canvas: Size { w: 0, h: 0 },
    })
}

fn overlaps_for_tests(a: Rect, b: Rect) -> bool {
    a.x < b.x + b.w && b.x < a.x + a.w && a.y < b.y + b.h && b.y < a.y + a.h
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn sizes(count: usize, w: i32, h: i32) -> Vec<Block> {
    (0..count).map(|_| leaf(None, 1, w, h)).collect()
}

#[test]
fn positions_follow_columns() {
    let layout = run(&input(
        3,
        vec![
            leaf(None, 1, 40, 10),
            leaf(None, 2, 100, 20),
            leaf(None, 1, 30, 10),
            leaf(None, 1, 30, 10),
        ],
        Vec::new(),
    ));
    let unit = 50;
    assert_eq!(layout.rects[0], rect(8, 8, unit, 20));
    assert_eq!(layout.rects[1], rect(8 + unit + 8, 8, 2 * unit + 8, 20));
    assert_eq!(layout.rects[2], rect(8, 8 + 20 + 8, unit, 10));
    assert_eq!(layout.rects[3], rect(8 + unit + 8, 8 + 20 + 8, unit, 10));
    assert_eq!(
        layout.canvas,
        Size {
            w: 3 * unit + 4 * 8,
            h: 20 + 10 + 3 * 8
        }
    );
}

#[test]
fn span_is_clipped_to_the_rest_of_the_row() {
    let layout = run(&input(
        2,
        vec![leaf(None, 1, 10, 10), leaf(None, 5, 10, 10)],
        Vec::new(),
    ));
    assert_eq!(layout.rects[0].w, layout.rects[1].w);
    assert_eq!(layout.rects[0].y, layout.rects[1].y);
}

#[test]
fn wide_child_starts_a_new_row_when_it_does_not_fit() {
    let layout = run(&input(3, sizes(4, 10, 10), Vec::new()));
    assert_eq!(layout.rects[0].x, layout.rects[3].x);
    assert!(layout.rects[3].y > layout.rects[0].y);
}

#[test]
fn auto_columns_place_one_row() {
    let layout = run(&input(
        0,
        vec![
            leaf(None, 1, 10, 10),
            leaf(None, 1, 10, 30),
            leaf(None, 2, 10, 10),
        ],
        Vec::new(),
    ));
    for r in &layout.rects[..3] {
        assert_eq!((r.y, r.h), (8, 30));
    }
}

#[test]
fn space_takes_a_slot_but_no_size() {
    let layout = run(&input(
        2,
        vec![space(None), leaf(None, 1, 40, 10), leaf(None, 1, 40, 10)],
        Vec::new(),
    ));
    assert_eq!(layout.rects[0].x, layout.rects[2].x);
    assert!(layout.rects[1].x > layout.rects[0].x);
    assert_eq!(layout.rects[0].h, 10);
}

#[test]
fn space_only_row_adds_no_height() {
    let layout = run(&input(
        1,
        vec![space(None), leaf(None, 1, 10, 10)],
        Vec::new(),
    ));
    assert_eq!(layout.rects[0].h, 0);
    assert_eq!(layout.rects[1].y, 8 + 8);
}

#[test]
fn composite_contains_its_children() {
    let layout = run(&input(
        2,
        vec![
            composite(None, 2),
            leaf(Some(0), 1, 30, 10),
            leaf(Some(0), 1, 30, 10),
            leaf(None, 1, 20, 10),
        ],
        Vec::new(),
    ));
    let frame = layout.rects[0];
    for child in &layout.rects[1..3] {
        assert_eq!(geom::contains(frame, *child), Ok(true));
    }
    assert_eq!(layout.rects[1].y, layout.rects[2].y);
    assert_eq!(layout.rects[1].x, frame.x + 8);
}

#[test]
fn nested_composite_inherits_row_height() {
    let layout = run(&input(
        2,
        vec![
            composite(None, 1),
            leaf(Some(0), 1, 30, 10),
            leaf(Some(0), 1, 30, 10),
            leaf(None, 1, 20, 10),
        ],
        Vec::new(),
    ));
    assert_eq!(layout.rects[0].h, 10 + 10 + 3 * 8);
    assert_eq!(layout.rects[0].h, layout.rects[3].h);
}

#[test]
fn span_widens_the_column_unit() {
    let narrow = run(&input(
        2,
        vec![leaf(None, 2, 10, 10), leaf(None, 1, 10, 10)],
        Vec::new(),
    ));
    let wide = run(&input(
        2,
        vec![leaf(None, 2, 200, 10), leaf(None, 1, 10, 10)],
        Vec::new(),
    ));
    assert!(narrow.canvas.w < wide.canvas.w);
    assert_eq!(wide.rects[0].w, 2 * wide.rects[1].w + 8);
}

#[test]
fn empty_input_has_margins_only() {
    let layout = run(&input(0, Vec::new(), Vec::new()));
    assert_eq!(layout.canvas, Size { w: 8, h: 8 });
    assert_eq!(layout.rects.len(), 1);
}

#[test]
fn invalid_input_is_rejected() {
    let bad = [
        input(0, vec![leaf(Some(0), 1, 1, 1)], Vec::new()),
        input(
            0,
            vec![leaf(None, 1, 1, 1), leaf(Some(0), 1, 1, 1)],
            Vec::new(),
        ),
        input(0, vec![leaf(None, 1, -1, 1)], Vec::new()),
        input(0, vec![leaf(None, 1, 1, 1)], vec![edge(0, 3)]),
        input(
            0,
            vec![leaf(None, 1, 1, 1)],
            vec![Edge {
                from: 0,
                to: 0,
                label: Size { w: -1, h: 0 },
            }],
        ),
    ];
    for case in &bad {
        assert_eq!(block(case, PARAMS).map(|_| ()), Err(GeomError::Domain));
    }
}

#[test]
fn oversized_canvas_overflows() {
    let huge = i32::try_from(geom::COORD_LIMIT - 4).unwrap_or(0);
    let case = input(
        2,
        vec![leaf(None, 1, huge, 10), leaf(None, 1, huge, 10)],
        Vec::new(),
    );
    assert_eq!(block(&case, PARAMS).map(|_| ()), Err(GeomError::Overflow));
}

#[test]
fn too_many_tracks_overflow() {
    let tracks = i32::try_from(MAX_TRACKS + 1).unwrap_or(0);
    let count = usize::try_from(tracks).unwrap_or(0);
    let case = input(tracks, sizes(count, 1, 1), Vec::new());
    assert_eq!(block(&case, PARAMS).map(|_| ()), Err(GeomError::Overflow));
}

#[test]
fn lattice_beyond_its_cap_overflows() {
    let span = i32::try_from(MAX_TRACKS).unwrap_or(0);
    let blocks = (0..700).map(|_| leaf(None, span, 1, 1)).collect();
    let case = input(span, blocks, vec![edge(0, 1)]);
    assert_eq!(block(&case, PARAMS).map(|_| ()), Err(GeomError::Overflow));
}

#[test]
fn deep_nesting_is_rejected() {
    let blocks = (0..MAX_DEPTH + 3)
        .map(|i| composite(i.checked_sub(1), 1))
        .collect();
    let case = input(0, blocks, Vec::new());
    assert_eq!(block(&case, PARAMS).map(|_| ()), Err(GeomError::Domain));
}

#[test]
fn edge_corridor_widens_gaps() {
    let blocks = vec![leaf(None, 1, 20, 10), leaf(None, 1, 20, 10)];
    let plain = run(&input(2, blocks.clone(), Vec::new()));
    let routed = run(&input(2, blocks, vec![edge(0, 1)]));
    let gap = |layout: &Layout| layout.rects[1].x - layout.rects[0].x - layout.rects[0].w;
    assert_eq!(gap(&plain), 8);
    assert_eq!(gap(&routed), 16);
}

#[test]
fn label_widens_the_gap() {
    let blocks = vec![leaf(None, 1, 20, 10), leaf(None, 1, 20, 10)];
    let layout = run(&input(2, blocks, vec![labelled(0, 1)]));
    assert_eq!(
        layout.rects[1].x - layout.rects[0].x - layout.rects[0].w,
        16 + 20
    );
}

fn on_boundary(p: Point, r: Rect) -> bool {
    let inside = p.x >= r.x && p.x <= r.x + r.w && p.y >= r.y && p.y <= r.y + r.h;
    let edge = p.x == r.x || p.x == r.x + r.w || p.y == r.y || p.y == r.y + r.h;
    inside && edge
}

fn assert_route(case: &Input, layout: &Layout, k: usize) {
    let e = case.edges[k];
    let route = &layout.routes[k];
    assert!(route.len() >= 2);
    assert!(geom::is_orthogonal(route));
    assert!(on_boundary(route[0], layout.rects[e.from]));
    assert!(on_boundary(route[route.len() - 1], layout.rects[e.to]));
    for (i, candidate) in case.blocks.iter().enumerate() {
        if candidate.kind != Kind::Leaf || i == e.from || i == e.to {
            continue;
        }
        let hits = geom::polyline_hits_rect(route, layout.rects[i]);
        assert_eq!(hits, Ok(false), "route {k} crosses leaf {i}");
    }
}

#[test]
fn routes_avoid_leaves() {
    let case = input(
        3,
        sizes(6, 30, 10),
        vec![edge(0, 2), edge(0, 5), edge(4, 1), edge(3, 3)],
    );
    let layout = run(&case);
    for k in 0..case.edges.len() {
        assert_route(&case, &layout, k);
    }
}

#[test]
fn routes_between_composite_leaves_stay_valid() {
    let case = input(
        2,
        vec![
            composite(None, 2),
            leaf(Some(0), 1, 30, 10),
            leaf(Some(0), 1, 30, 10),
            composite(None, 1),
            leaf(Some(3), 1, 30, 10),
        ],
        vec![edge(1, 4), edge(4, 2), edge(0, 3), edge(4, 3)],
    );
    let layout = run(&case);
    for k in 0..case.edges.len() {
        assert_route(&case, &layout, k);
    }
}

#[test]
fn self_loop_leaves_and_enters_the_same_box() {
    let layout = run(&input(1, vec![leaf(None, 1, 30, 30)], vec![edge(0, 0)]));
    let route = &layout.routes[0];
    let b = layout.rects[0];
    assert_eq!(route.len(), 4);
    assert_eq!(route[0].x, b.x + b.w);
    assert_eq!(route[3].x, b.x + b.w);
    assert!(route[1].x > route[0].x);
    assert!(route[0].y < route[3].y);
}

fn shares_horizontal_run(a: &[Point], b: &[Point]) -> bool {
    a.windows(2).any(|p| {
        b.windows(2).any(|q| {
            if p[0].y != p[1].y || q[0].y != q[1].y || p[1].y != q[1].y {
                return false;
            }
            let lo = p[0].x.min(p[1].x).max(q[0].x.min(q[1].x));
            let hi = p[0].x.max(p[1].x).min(q[0].x.max(q[1].x));
            lo < hi
        })
    })
}

#[test]
fn parallel_routes_do_not_share_runs() {
    let case = input(4, sizes(4, 30, 10), vec![edge(0, 2), edge(1, 3)]);
    let layout = run(&case);
    assert!(!shares_horizontal_run(&layout.routes[0], &layout.routes[1]));
}

fn assert_label_clear(case: &Input, layout: &Layout, k: usize) {
    let label = layout.labels[k];
    assert_eq!(
        case.edges[k].label,
        Size {
            w: label.w,
            h: label.h
        }
    );
    assert_label_inside_frames(case, layout, label);
    for (i, r) in layout.rects[..case.blocks.len()].iter().enumerate() {
        assert!(!overlaps_for_tests(label, *r), "label {k} overlaps box {i}");
    }
    for (j, other) in layout.labels.iter().enumerate().take(k) {
        assert!(
            !overlaps_for_tests(label, *other),
            "labels {j} and {k} overlap"
        );
    }
    for route in &layout.routes {
        for pair in route.windows(2) {
            let (x0, x1) = (pair[0].x.min(pair[1].x), pair[0].x.max(pair[1].x));
            let (y0, y1) = (pair[0].y.min(pair[1].y), pair[0].y.max(pair[1].y));
            let touches = x0 < label.x + label.w
                && label.x < x1 + PARAMS.line_thickness
                && y0 < label.y + label.h
                && label.y < y1 + PARAMS.line_thickness;
            assert!(!touches, "label {k} touches a route");
        }
    }
}

#[test]
fn labels_avoid_boxes_routes_and_each_other() {
    let case = input(
        3,
        sizes(4, 30, 10),
        vec![labelled(0, 1), labelled(1, 2), labelled(0, 3)],
    );
    let layout = run(&case);
    for k in 0..case.edges.len() {
        assert_label_clear(&case, &layout, k);
    }
}

#[test]
fn crowded_labels_spill_inside_the_canvas() {
    let case = input(
        2,
        sizes(2, 30, 10),
        (0..6).map(|_| labelled(0, 1)).collect(),
    );
    let layout = run(&case);
    for k in 0..case.edges.len() {
        assert_label_clear(&case, &layout, k);
    }
}

#[test]
fn label_beside_a_self_loop_stays_strictly_inside_the_cell_canvas() -> Result<(), GeomError> {
    let case = input(
        0,
        sizes(2, 3, 3),
        vec![
            edge(0, 0),
            Edge {
                from: 1,
                to: 1,
                label: Size { w: 10, h: 1 },
            },
            edge(0, 1),
            edge(1, 0),
        ],
    );
    let params = Params {
        padding: 1,
        bend_cost: 4,
        line_thickness: 1,
    };
    let layout = block(&case, params)?;
    assert_label_inside_frames(&case, &layout, layout.labels[1]);
    Ok(())
}

#[test]
fn spill_margin_is_at_least_one_unit_without_padding() -> Result<(), GeomError> {
    let case = input(
        2,
        sizes(2, 30, 10),
        (0..6).map(|_| labelled(0, 1)).collect(),
    );
    let params = Params {
        padding: 0,
        bend_cost: 64,
        line_thickness: 0,
    };
    let layout = block(&case, params)?;
    for label in &layout.labels {
        assert_label_inside_frames(&case, &layout, *label);
    }
    Ok(())
}

struct XorShift(u32);

impl XorShift {
    fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        usize::try_from(self.0).unwrap_or(0) % n
    }

    fn int(&mut self, base: i32, n: usize) -> i32 {
        base + i32::try_from(self.next(n)).unwrap_or(0)
    }
}

fn random_input(seed: u32) -> Input {
    let mut rng = XorShift(seed.wrapping_mul(2_654_435_761).wrapping_add(1));
    for _ in 0..8 {
        rng.next(2);
    }
    let columns = rng.int(0, 5);
    let mut blocks: Vec<Block> = Vec::new();
    let mut composites: Vec<Option<usize>> = vec![None];
    let wanted = 2 + rng.next(14);
    while blocks.len() < wanted {
        let parent = composites[rng.next(composites.len())];
        let span = rng.int(1, 3);
        match rng.next(6) {
            0 => blocks.push(space(parent)),
            1 => {
                blocks.push(Block {
                    span,
                    ..composite(parent, rng.int(0, 4))
                });
                composites.push(Some(blocks.len() - 1));
            }
            _ => {
                let (w, h) = (rng.int(5, 60), rng.int(4, 20));
                blocks.push(leaf(parent, span, w, h));
            }
        }
    }
    let linkable: Vec<usize> = (0..blocks.len())
        .filter(|i| blocks[*i].kind != Kind::Space)
        .collect();
    let mut edges = Vec::new();
    for _ in 0..rng.next(8) {
        if linkable.is_empty() {
            break;
        }
        let (from, to) = (
            linkable[rng.next(linkable.len())],
            linkable[rng.next(linkable.len())],
        );
        let mut e = edge(from, to);
        if rng.next(3) == 0 {
            e.label = Size {
                w: rng.int(4, 30),
                h: rng.int(4, 10),
            };
        }
        edges.push(e);
    }
    input(columns, blocks, edges)
}

fn assert_invariants(seed: u32, case: &Input, layout: &Layout) {
    let canvas = rect(0, 0, layout.canvas.w, layout.canvas.h);
    for (i, b) in case.blocks.iter().enumerate() {
        assert_eq!(
            geom::contains(canvas, layout.rects[i]),
            Ok(true),
            "seed {seed} box {i}"
        );
        if let Some(parent) = b.parent {
            assert_eq!(
                geom::contains(layout.rects[parent], layout.rects[i]),
                Ok(true),
                "seed {seed} box {i} outside parent"
            );
        }
        for j in 0..i {
            let sibling = case.blocks[j];
            if sibling.parent != b.parent || b.kind == Kind::Space || sibling.kind == Kind::Space {
                continue;
            }
            assert_eq!(
                geom::intersects(layout.rects[i], layout.rects[j]),
                Ok(false),
                "seed {seed} siblings {j} and {i}"
            );
        }
    }
    for k in 0..case.edges.len() {
        assert_route(case, layout, k);
        if case.edges[k].label != (Size { w: 0, h: 0 }) {
            assert_label_inside_frames(case, layout, layout.labels[k]);
        }
    }
}

fn strictly_inside(outer: Rect, inner: Rect) -> bool {
    outer.x < inner.x
        && inner.x + inner.w < outer.x + outer.w
        && outer.y < inner.y
        && inner.y + inner.h < outer.y + outer.h
}

fn assert_label_inside_frames(case: &Input, layout: &Layout, label: Rect) {
    let canvas = rect(0, 0, layout.canvas.w, layout.canvas.h);
    assert!(
        strictly_inside(canvas, label),
        "label {label:?} touches the canvas edge"
    );
    for (i, b) in case.blocks.iter().enumerate() {
        if b.kind != Kind::Composite {
            continue;
        }
        let frame = layout.rects[i];
        assert!(
            !overlaps_for_tests(frame, label) || strictly_inside(frame, label),
            "label {label:?} straddles frame {i}"
        );
    }
}

#[test]
fn random_layouts_keep_their_invariants() {
    for seed in 0..400 {
        let case = random_input(seed);
        let layout = run(&case);
        assert_eq!(layout, run(&case), "seed {seed}");
        assert_invariants(seed, &case, &layout);
    }
}
