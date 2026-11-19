use super::{Gaps, Layout, Node, mindmap, normalize};
use crate::geom::{
    COORD_LIMIT, GeomError, Point, Rect, Size, floor_div, intersects, is_orthogonal,
    polyline_hits_rect,
};

const TEST_GAPS: Gaps = Gaps {
    level: 40,
    sibling: 10,
};

fn leaf(parent: Option<usize>, width: i32, height: i32) -> Node {
    Node {
        parent,
        width,
        height,
    }
}

fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
    Rect { x, y, w, h }
}

fn pt(x: i32, y: i32) -> Point {
    Point { x, y }
}

fn laid(nodes: &[Node], gaps: Gaps) -> Result<Layout, GeomError> {
    mindmap(nodes, gaps)
}

#[test]
fn single_node_sits_centred_on_the_origin() -> Result<(), GeomError> {
    let l = laid(&[leaf(None, 11, 7)], TEST_GAPS)?;
    assert_eq!(l.boxes, [rect(-5, -3, 11, 7)]);
    Ok(())
}

#[test]
fn root_children_alternate_sides() -> Result<(), GeomError> {
    let nodes = [leaf(None, 10, 6), leaf(Some(0), 8, 4), leaf(Some(0), 6, 4)];
    let l = laid(
        &nodes,
        Gaps {
            level: 4,
            sibling: 2,
        },
    )?;
    assert_eq!(
        l.boxes,
        [rect(-5, -3, 10, 6), rect(9, -2, 8, 4), rect(-15, -2, 6, 4)]
    );
    assert_eq!(l.routes[1], [pt(5, 0), pt(9, 0)]);
    assert_eq!(l.routes[2], [pt(-5, 0), pt(-9, 0)]);
    Ok(())
}

#[test]
fn siblings_stack_below_the_contour_and_centre_on_the_parent() -> Result<(), GeomError> {
    let nodes = [
        leaf(None, 10, 6),
        leaf(Some(0), 8, 4),
        leaf(Some(0), 6, 4),
        leaf(Some(0), 8, 4),
    ];
    let l = laid(
        &nodes,
        Gaps {
            level: 4,
            sibling: 2,
        },
    )?;
    assert_eq!(l.boxes[1], rect(9, -5, 8, 4));
    assert_eq!(l.boxes[3], rect(9, 1, 8, 4));
    assert_eq!(l.routes[1], [pt(5, 0), pt(7, 0), pt(7, -3), pt(9, -3)]);
    assert_eq!(l.routes[3], [pt(5, 0), pt(7, 0), pt(7, 3), pt(9, 3)]);
    Ok(())
}

#[test]
fn deeper_box_binds_the_sibling_offset() -> Result<(), GeomError> {
    let mut nodes = [
        leaf(None, 10, 6),
        leaf(Some(0), 4, 2),
        leaf(Some(1), 20, 20),
        leaf(Some(0), 4, 2),
        leaf(Some(0), 10, 2),
    ];
    let gaps = Gaps {
        level: 3,
        sibling: 2,
    };
    let wide = laid(&nodes, gaps)?;
    assert_eq!(wide.boxes[4].y - wide.boxes[1].y, 13);
    nodes[4].width = 4;
    let narrow = laid(&nodes, gaps)?;
    assert_eq!(narrow.boxes[4].y - narrow.boxes[1].y, 4);
    Ok(())
}

#[test]
fn odd_parent_centre_rounds_down() -> Result<(), GeomError> {
    let nodes = [
        leaf(None, 10, 6),
        leaf(Some(0), 10, 3),
        leaf(Some(1), 10, 3),
        leaf(Some(1), 10, 3),
    ];
    let l = laid(
        &nodes,
        Gaps {
            level: 4,
            sibling: 1,
        },
    )?;
    let reference = |i: usize| l.boxes[i].y + l.boxes[i].h / 2;
    assert_eq!(reference(3) - reference(2), 4);
    assert_eq!(
        floor_div(i64::from(reference(2) + reference(3)), 2),
        i64::from(reference(1))
    );
    Ok(())
}

#[test]
fn invalid_input_is_rejected() {
    let cases: [(&str, Vec<Node>); 8] = [
        ("root has parent", vec![leaf(Some(0), 4, 4)]),
        (
            "forward parent",
            vec![leaf(None, 4, 4), leaf(Some(2), 4, 4), leaf(Some(0), 4, 4)],
        ),
        ("zero width", vec![leaf(None, 0, 4)]),
        ("zero height", vec![leaf(None, 4, 0)]),
        ("second root", vec![leaf(None, 4, 4), leaf(None, 4, 4)]),
        (
            "not preorder",
            vec![
                leaf(None, 4, 4),
                leaf(Some(0), 4, 4),
                leaf(Some(0), 4, 4),
                leaf(Some(1), 4, 4),
            ],
        ),
        (
            "parent is itself",
            vec![leaf(None, 4, 4), leaf(Some(1), 4, 4)],
        ),
        (
            "parent out of set",
            vec![leaf(None, 4, 4), leaf(Some(7), 4, 4)],
        ),
    ];
    for (name, nodes) in &cases {
        assert_eq!(laid(nodes, TEST_GAPS), Err(GeomError::Domain), "{name}");
    }
    assert_eq!(
        laid(
            &[leaf(None, 4, 4)],
            Gaps {
                level: 4,
                sibling: 0
            }
        ),
        Err(GeomError::Domain)
    );
}

#[test]
fn empty_input_has_no_boxes() -> Result<(), GeomError> {
    let mut l = laid(&[], TEST_GAPS)?;
    assert!(l.boxes.is_empty());
    assert_eq!(normalize(&mut l, 8)?, Size { w: 16, h: 16 });
    Ok(())
}

#[test]
fn huge_nodes_overflow() {
    let huge = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
    let nodes = [leaf(None, huge, 4), leaf(Some(0), huge, 4)];
    assert_eq!(laid(&nodes, TEST_GAPS), Err(GeomError::Overflow));
}

#[test]
fn normalize_shifts_boxes_and_routes_by_the_margin() -> Result<(), GeomError> {
    let nodes = [
        leaf(None, 10, 6),
        leaf(Some(0), 8, 4),
        leaf(Some(1), 6, 8),
        leaf(Some(0), 6, 4),
    ];
    let mut l = laid(
        &nodes,
        Gaps {
            level: 4,
            sibling: 2,
        },
    )?;
    let before = l.boxes[0];
    let size = normalize(&mut l, 3)?;
    let min_x = l.boxes.iter().map(|b| b.x).min().unwrap_or(0);
    let min_y = l.boxes.iter().map(|b| b.y).min().unwrap_or(0);
    let max_x = l.boxes.iter().map(|b| b.x + b.w).max().unwrap_or(0);
    let max_y = l.boxes.iter().map(|b| b.y + b.h).max().unwrap_or(0);
    assert_eq!((min_x, min_y), (3, 3));
    assert_eq!(
        size,
        Size {
            w: max_x + 3,
            h: max_y + 3
        }
    );
    assert_eq!(before.w, l.boxes[0].w);
    assert_eq!(l.boxes[0].x + l.boxes[0].w, l.routes[1][0].x);
    Ok(())
}

/// The first child is wide and its grandchildren are tall: the box-only contour would
/// seat the first grandchild beside the wide sibling, so the trunk crosses it.
fn crossing_tree() -> Vec<Node> {
    vec![
        leaf(None, 20, 20),
        leaf(Some(0), 80, 20),
        leaf(Some(0), 20, 20),
        leaf(Some(0), 50, 20),
        leaf(Some(3), 20, 30),
        leaf(Some(3), 20, 30),
        leaf(Some(3), 20, 30),
    ]
}

#[test]
fn widened_contour_keeps_routes_off_foreign_boxes() -> Result<(), GeomError> {
    let literal_box = rect(50, -25, 80, 20);
    let literal_route = [pt(100, 15), pt(120, 15), pt(120, -25), pt(140, -25)];
    assert!(
        polyline_hits_rect(&literal_route, literal_box)?,
        "the box-only contour puts the trunk through the wide sibling"
    );
    let nodes = crossing_tree();
    let gaps = Gaps {
        level: 40,
        sibling: 10,
    };
    let l = laid(&nodes, gaps)?;
    require_clear(&nodes, &l)?;
    assert!(l.boxes[4].y >= l.boxes[1].y + l.boxes[1].h + gaps.sibling);
    Ok(())
}

fn require_clear(nodes: &[Node], l: &Layout) -> Result<(), GeomError> {
    for (i, a) in l.boxes.iter().enumerate() {
        for (j, b) in l.boxes.iter().enumerate().skip(i + 1) {
            assert!(!intersects(*a, *b)?, "boxes {i} and {j} overlap");
        }
    }
    for (i, node) in nodes.iter().enumerate().skip(1) {
        for (j, b) in l.boxes.iter().enumerate() {
            let allowed = j == i || Some(j) == node.parent;
            assert!(
                allowed || !polyline_hits_rect(&l.routes[i], *b)?,
                "route {i} crosses box {j}"
            );
        }
    }
    Ok(())
}

struct Stream(u32);

impl Stream {
    fn draw(&mut self, lo: i32, hi: i32) -> i32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        let span = u32::try_from(hi - lo + 1).unwrap_or(1);
        lo + i32::try_from(self.0 % span).unwrap_or(0)
    }
}

fn random_tree(seed: u32) -> Vec<Node> {
    let mut s = Stream(seed + 1);
    let n = usize::try_from(s.draw(2, 30)).unwrap_or(2);
    let mut parents = vec![0_usize; n];
    for (i, parent) in parents.iter_mut().enumerate().skip(1) {
        *parent = usize::try_from(s.draw(0, i32::try_from(i - 1).unwrap_or(0))).unwrap_or(0);
    }
    let sizes: Vec<(i32, i32)> = (0..n).map(|_| (s.draw(20, 140), s.draw(20, 60))).collect();
    let mut children = vec![Vec::new(); n];
    for (i, parent) in parents.iter().enumerate().skip(1) {
        children[*parent].push(i);
    }
    let mut order = Vec::with_capacity(n);
    let mut stack = vec![0_usize];
    while let Some(v) = stack.pop() {
        order.push(v);
        stack.extend(children[v].iter().rev());
    }
    let mut new_index = vec![0_usize; n];
    for (at, old) in order.iter().enumerate() {
        new_index[*old] = at;
    }
    order
        .iter()
        .map(|old| Node {
            parent: (*old != 0).then(|| new_index[parents[*old]]),
            width: sizes[*old].0,
            height: sizes[*old].1,
        })
        .collect()
}

fn sides_of(nodes: &[Node]) -> Vec<bool> {
    let mut right = vec![false; nodes.len()];
    let mut ordinal = 0;
    for (i, node) in nodes.iter().enumerate().skip(1) {
        let parent = node.parent.unwrap_or(0);
        right[i] = right[parent];
        if parent == 0 {
            right[i] = ordinal % 2 == 0;
            ordinal += 1;
        }
    }
    right
}

fn within(nodes: &[Node], mut j: usize, root: usize) -> bool {
    loop {
        if j == root {
            return true;
        }
        match nodes[j].parent {
            Some(parent) => j = parent,
            None => return false,
        }
    }
}

fn span(l: &Layout, right: &[bool], gaps: Gaps, i: usize) -> (i64, i64) {
    let b = l.boxes[i];
    let (x, w, gap) = (i64::from(b.x), i64::from(b.w), i64::from(gaps.level));
    if right[i] {
        (x - gap, x + w)
    } else {
        (x, x + w + gap)
    }
}

fn check_separation(nodes: &[Node], l: &Layout, gaps: Gaps, list: &[usize], seed: u32) {
    let right = sides_of(nodes);
    for (j, sibling) in list.iter().enumerate().skip(1) {
        let mut tight = false;
        for a in 0..nodes.len() {
            if !list[..j].iter().any(|s| within(nodes, a, *s)) {
                continue;
            }
            for b in (0..nodes.len()).filter(|b| within(nodes, *b, *sibling)) {
                let (a0, a1) = span(l, &right, gaps, a);
                let (b0, b1) = span(l, &right, gaps, b);
                if a0 >= b1 || b0 >= a1 {
                    continue;
                }
                let gap =
                    i64::from(l.boxes[b].y) - i64::from(l.boxes[a].y) - i64::from(l.boxes[a].h);
                assert!(gap >= i64::from(gaps.sibling), "seed {seed}: {a} and {b}");
                tight |= gap == i64::from(gaps.sibling);
            }
        }
        assert!(tight, "seed {seed}: sibling {sibling} has slack");
    }
}

#[test]
fn random_trees_satisfy_the_contour_rule_and_stay_clear() -> Result<(), GeomError> {
    for gaps in [
        Gaps {
            level: 40,
            sibling: 10,
        },
        Gaps {
            level: 4,
            sibling: 1,
        },
        Gaps {
            level: 2,
            sibling: 3,
        },
    ] {
        for seed in 0..400 {
            let nodes = random_tree(seed);
            let l = laid(&nodes, gaps)?;
            let right = sides_of(&nodes);
            let mut lists: Vec<Vec<usize>> = vec![Vec::new(), Vec::new()];
            let mut by_parent: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
            for (i, node) in nodes.iter().enumerate().skip(1) {
                let parent = node.parent.unwrap_or(0);
                if parent == 0 {
                    lists[usize::from(!right[i])].push(i);
                } else {
                    by_parent[parent].push(i);
                }
            }
            lists.extend(by_parent);
            for list in &lists {
                check_separation(&nodes, &l, gaps, list, seed);
            }
            require_clear(&nodes, &l)?;
            for route in l.routes.iter().skip(1) {
                assert!(is_orthogonal(route), "seed {seed}");
            }
        }
    }
    Ok(())
}
