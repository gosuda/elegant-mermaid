use super::super::{
    graph::{Edge, Graph, Node, ProperNode},
    normalize::normalize,
    rank::rank,
    route::{route, route_points},
};
use super::*;
#[path = "coords/oracle.rs"]
mod oracle;
use oracle::oracle;
use std::collections::BTreeMap;

const PLAIN: (bool, i32) = (false, -1);
const DUMMY: (bool, i32) = (true, 0);
const CHAIN: (bool, i32) = (false, -2);

fn marks(nodes: &[(bool, i32)], edges: &[(usize, usize)], layers: &[Vec<usize>]) -> Vec<bool> {
    let n = nodes.len();
    let mut rank = vec![0; n];
    let mut pos = vec![0; n];
    for (r, layer) in layers.iter().enumerate() {
        for (j, &v) in layer.iter().enumerate() {
            rank[v] = i32::try_from(r).unwrap();
            pos[v] = j;
        }
    }
    let p = Proper {
        nodes: nodes
            .iter()
            .map(|&(dummy, edge)| ProperNode {
                node: Node::default(),
                dummy,
                label: false,
                edge,
            })
            .collect(),
        edges: edges
            .iter()
            .map(|&(tail, head)| ProperEdge {
                tail,
                head,
                decl: 0,
                original: usize::MAX,
            })
            .collect(),
        rank,
        chains: Vec::new(),
        out: vec![Vec::new(); n],
        r#in: vec![Vec::new(); n],
        params: Params::for_profile("cell").unwrap(),
    };
    conflicts(&p, &pos)
}

#[test]
fn a_plain_segment_crossing_a_border_chain_is_marked() {
    let nodes = [CHAIN, CHAIN, PLAIN, PLAIN];
    let layers = [vec![0, 2], vec![3, 1]];
    assert_eq!(marks(&nodes, &[(0, 1), (2, 3)], &layers), [false, true]);
}

#[test]
fn an_inner_segment_crossing_a_border_chain_is_marked() {
    let nodes = [CHAIN, CHAIN, DUMMY, DUMMY];
    let layers = [vec![0, 2], vec![3, 1]];
    assert_eq!(marks(&nodes, &[(0, 1), (2, 3)], &layers), [false, true]);
}

#[test]
fn a_border_chain_crossing_an_inner_segment_stays_unmarked() {
    let nodes = [CHAIN, CHAIN, DUMMY, DUMMY];
    let layers = [vec![2, 0], vec![1, 3]];
    assert_eq!(marks(&nodes, &[(2, 3), (0, 1)], &layers), [true, false]);
}

#[test]
fn segments_that_do_not_cross_stay_unmarked() {
    let nodes = [CHAIN, CHAIN, PLAIN, PLAIN];
    let layers = [vec![0, 2], vec![1, 3]];
    assert_eq!(marks(&nodes, &[(0, 1), (2, 3)], &layers), [false, false]);
}

#[test]
fn a_plain_segment_crossing_an_inner_segment_is_still_marked() {
    let nodes = [PLAIN, PLAIN, DUMMY, DUMMY];
    let layers = [vec![0, 2], vec![3, 1]];
    assert_eq!(marks(&nodes, &[(0, 1), (2, 3)], &layers), [true, false]);
}

#[test]
fn border_chains_are_never_marked_even_when_they_cross() {
    let nodes = [CHAIN, CHAIN, (false, -3), (false, -3)];
    let layers = [vec![0, 2], vec![3, 1]];
    assert_eq!(marks(&nodes, &[(0, 1), (2, 3)], &layers), [false, false]);
}

#[test]
fn nested_border_padding_is_symmetric() {
    let graph = Graph {
        nodes: vec![
            Node {
                w: 2,
                ..Node::default()
            };
            2
        ],
        edges: Vec::new(),
        params: Params::for_profile("cell").unwrap(),
    };
    let mut p = normalize(&graph, &[0, 0]).unwrap();
    let layers = vec![vec![0, 1]];
    p.nodes[0].edge = -2;
    p.nodes[1].edge = -3;
    let mut paths = vec![Vec::new(); p.nodes.len()];
    paths[0] = vec![10, 11];
    paths[1] = vec![10];
    let marked = vec![false; p.edges.len()];
    let mut pass = Pass::new(&p, &layers, &marked, 2, 0);
    pass.paths = &paths;
    let expected = i64::from(p.nodes[0].node.w) / 2
        + i64::from(p.nodes[1].node.w) / 2
        + i64::from(p.params.cluster_pad);
    assert_eq!(pass.sep(0, 1), expected);
    assert_eq!(pass.sep(1, 0), expected);
}

fn case(index: usize) -> (Proper, Vec<Vec<usize>>) {
    let mut s = (index + 1) as u32;
    let mut draw = |lo: usize, hi: usize| {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        lo + s as usize % (hi - lo + 1)
    };
    let words = [
        "amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor", "iris",
        "juniper", "kelp", "lumen", "maple", "nectar", "onyx", "pine",
    ];
    let n = draw(2, 30);
    let nodes = (0..n)
        .map(|i| {
            let line = format!("n{i}[{}{i}]", words[draw(0, 15)]);
            Node {
                id: String::new(),
                decl: i as i32,
                w: 2048 + 64 * line.len() as i32,
                h: 2304,
            }
        })
        .collect();
    let count = draw(1, n);
    let edges = (0..count)
        .map(|i| {
            let tail = draw(0, n - 2);
            let head = draw(tail + 1, n - 1);
            Edge {
                tail,
                head,
                min_len: 1,
                decl: i as i32,
                reversed: false,
            }
        })
        .collect();
    let g = Graph {
        nodes,
        edges,
        params: Params::for_profile("vector").unwrap(),
    };
    let p = normalize(&g, &rank(&g).unwrap().ranks).unwrap();
    let mut ls = vec![Vec::new(); *p.rank.iter().max().unwrap() as usize + 1];
    for (v, &r) in p.rank.iter().enumerate() {
        ls[r as usize].push(v);
    }
    for l in &mut ls {
        l.sort_by_key(|&v| (p.nodes[v].node.decl, v));
    }
    (p, ls)
}
#[test]
fn layered_coordinates_oracle() {
    for i in 0..200 {
        let (p, ls) = case(i);
        let x = cross_coords(&p, &ls).unwrap();
        assert_eq!(x, oracle(&p, &ls), "case {i}");
        for l in &ls {
            for ab in l.windows(2) {
                assert!(
                    i64::from(x[ab[1]]) - i64::from(x[ab[0]])
                        >= i64::from(p.nodes[ab[0]].node.w) / 2
                            + i64::from(p.nodes[ab[1]].node.w) / 2
                            + 1536,
                    "layered_coordinates_oracle: input violates i64::from(x[ab[1]]) - i64::from(x[ab[0]]) >= i64::from(p.nodes[ab[0]].node.w) / 2 + i64::from(p.nodes[ab[1]].node.w) / 2 + 1536; observed {:?}",
                    p
                );
            }
        }
        let r = route(&p, &ls, &x).unwrap();
        let (y, top) = rank_coords(&p, &ls, &r).unwrap();
        let (routes, _) = route_points(&p, &ls, &x, &y, &top, &r).unwrap();
        assert_slot_geometry(&p, &ls, &r, &top);
        for e in routes {
            assert!(
                e.points
                    .windows(2)
                    .all(|p| p[0].x == p[1].x || p[0].y == p[1].y),
                "layered_coordinates_oracle: input violates e.points .windows(2) .all(|p| p[0].x == p[1].x || p[0].y == p[1].y); observed {:?}",
                e
            );
            let chain = &p.chains[e.original];
            let a = chain[0];
            let b = chain[chain.len() - 1];
            assert_eq!(e.points[0].y, y[a] + p.nodes[a].node.h);
            assert_eq!(e.points.last().unwrap().y, y[b]);
            for (v, n) in p.nodes.iter().enumerate() {
                if n.dummy || v == a || v == b {
                    continue;
                }
                let rect = crate::geom::Rect {
                    x: x[v] - n.node.w / 2,
                    y: y[v],
                    w: n.node.w,
                    h: n.node.h,
                };
                assert!(
                    !crate::geom::polyline_hits_rect(&e.points, rect).unwrap(),
                    "layered_coordinates_oracle: input violates !crate::geom::polyline_hits_rect(&e.points, rect).unwrap(); observed {:?}",
                    e
                );
            }
        }
    }
}
fn assert_slot_geometry(p: &Proper, ls: &[Vec<usize>], r: &Routing, top: &[i32]) {
    for (rank, gap) in r.gaps.iter().enumerate() {
        assert!(
            top[rank + 1] >= top[rank] + heights(p, ls)[rank],
            "assert_slot_geometry: input violates top[rank + 1] >= top[rank] + heights(p, ls)[rank]; observed {:?}",
            top
        );
        for (j, a) in gap.segments.iter().enumerate() {
            for b in &gap.segments[j + 1..] {
                let overlap = a.source_x.min(a.target_x).max(b.source_x.min(b.target_x))
                    <= a.source_x.max(a.target_x).min(b.source_x.max(b.target_x));
                if overlap && a.source_x != a.target_x && b.source_x != b.target_x {
                    assert_ne!(a.slot, b.slot);
                }
            }
        }
    }
}
#[test]
fn layered_coordinate_twin_vectors() {
    let expected = [
        vec![0, 4224, 4224, 8448],
        vec![0, 4224, 8480, 2160, 6352, 6352],
        vec![0, 8512, 0, 4288, 12768, 8512, 4288, 4288, 8512],
        vec![
            8448, 4224, 12672, 16896, 21152, 25472, 16896, 21120, 25344, 21120,
        ],
        vec![
            4384, 8608, 12832, 12832, 17088, 12832, 21344, 25568, 29792, 17088, 21472, 29792,
        ],
    ];
    let tops = [
        vec![0, 5376],
        vec![0, 6144, 12288],
        vec![0, 5376, 11520, 17664],
        vec![0, 6912, 13056],
        vec![0, 7680, 13056],
    ];
    let ys = [
        vec![0, 0, 5376, 0],
        vec![0, 0, 0, 6144, 6144, 12288],
        vec![0, 0, 5376, 5376, 0, 5376, 11520, 17664, 12672],
        vec![0, 6912, 0, 0, 0, 0, 6912, 6912, 6912, 13056],
        vec![0, 0, 0, 7680, 0, 13056, 0, 0, 0, 7680, 7680, 7680],
    ];
    let go_routes: &[&[&[(i32, i32)]]] = &[
        &[&[(4224, 2304), (4224, 5376)]],
        &[
            &[(6352, 8448), (6352, 9600), (6821, 9600), (6821, 12288)],
            &[(2160, 8448), (2160, 9600), (5882, 9600), (5882, 12288)],
            &[(6352, 8448), (6352, 9600), (6821, 9600), (6821, 12288)],
            &[(4224, 2304), (4224, 3456), (5904, 3456), (5904, 6144)],
            &[(8480, 2304), (8480, 3456), (6800, 3456), (6800, 6144)],
        ],
        &[
            &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
            &[(8064, 7680), (8064, 8832), (4736, 8832), (4736, 11520)],
            &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
            &[(0, 2304), (0, 5376)],
            &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
            &[(8512, 2304), (8512, 5376)],
            &[(4288, 7680), (4288, 8832), (3840, 8832), (3840, 11520)],
            &[
                (8960, 7680),
                (8960, 8832),
                (8512, 8832),
                (8512, 12672),
                (8512, 14976),
                (4725, 14976),
                (4725, 17664),
            ],
        ],
        &[
            &[(25472, 2304), (25472, 3456), (17344, 3456), (17344, 6912)],
            &[
                (16896, 9216),
                (16896, 10368),
                (20672, 10368),
                (20672, 13056),
            ],
            &[(8896, 2304), (8896, 4224), (21120, 4224), (21120, 6912)],
            &[
                (25344, 9216),
                (25344, 10368),
                (21568, 10368),
                (21568, 13056),
            ],
            &[
                (25344, 9216),
                (25344, 10368),
                (21568, 10368),
                (21568, 13056),
            ],
            &[(16896, 2304), (16896, 3456), (16448, 3456), (16448, 6912)],
            &[(8000, 2304), (8000, 3456), (4224, 3456), (4224, 6912)],
        ],
        &[
            &[(29792, 2304), (29792, 7680)],
            &[(13280, 2304), (13280, 4992), (16629, 4992), (16629, 7680)],
            &[(16629, 2304), (16629, 4224), (17546, 4224), (17546, 7680)],
            &[(16629, 2304), (16629, 4224), (17546, 4224), (17546, 7680)],
            &[(17546, 2304), (17546, 3456), (21472, 3456), (21472, 7680)],
            &[(12832, 9984), (12832, 13056)],
            &[(12384, 2304), (12384, 3456), (12832, 3456), (12832, 7680)],
        ],
    ];
    for (i, want) in expected.iter().enumerate() {
        let (p, ls) = case(i);
        let x = cross_coords(&p, &ls).unwrap();
        assert_eq!(&x, want);
        let r = route(&p, &ls, &x).unwrap();
        let (y, top) = rank_coords(&p, &ls, &r).unwrap();
        assert_eq!(top, tops[i]);
        assert_eq!(y, ys[i]);
        let (routes, _) = route_points(&p, &ls, &x, &y, &top, &r).unwrap();
        assert_eq!(routes.len(), go_routes[i].len());
        for (edge, want) in routes.iter().zip(go_routes[i]) {
            assert_eq!(
                edge.points.iter().map(|p| (p.x, p.y)).collect::<Vec<_>>(),
                *want
            );
        }
        println!("case {i}: x={x:?} y={y:?} top={top:?} routes={routes:?}");
    }
}

fn label_node(p: &mut Proper, v: usize) {
    p.nodes[v].label = true;
    p.nodes[v].node.w = 1024;
    p.nodes[v].node.h = 1280;
}
fn tops(p: &Proper, layers: &[Vec<usize>]) -> Vec<i32> {
    let x = cross_coords(p, layers).unwrap();
    let r = route(p, layers, &x).unwrap();
    rank_coords(p, layers, &r).unwrap().1
}
fn two_nodes(min_len: i32) -> Graph {
    let node = |decl: i32| Node {
        id: String::new(),
        decl,
        w: 2048,
        h: 1280,
    };
    Graph {
        nodes: vec![node(0), node(1)],
        edges: vec![Edge {
            tail: 0,
            head: 1,
            min_len,
            decl: 0,
            reversed: false,
        }],
        params: Params::for_profile("vector").unwrap(),
    }
}
#[test]
fn label_rank_halves_rank_gap() {
    let graph = two_nodes(2);
    let layers = vec![vec![0], vec![2], vec![1]];
    let mut p = normalize(&graph, &[0, 2]).unwrap();
    assert_eq!(tops(&p, &layers), [0, 4352, 7424]);
    label_node(&mut p, 2);
    assert_eq!(tops(&p, &layers), [0, 3584, 7168]);
}
#[test]
fn real_node_keeps_full_rank_gap() {
    let node = |decl: i32| Node {
        id: String::new(),
        decl,
        w: 2048,
        h: 1280,
    };
    let edge = |tail, head, decl| Edge {
        tail,
        head,
        min_len: 1,
        decl,
        reversed: false,
    };
    let graph = Graph {
        nodes: vec![node(0), node(1), node(2)],
        edges: vec![edge(0, 1, 0), edge(1, 2, 1), edge(0, 2, 2)],
        params: Params::for_profile("vector").unwrap(),
    };
    let mut p = normalize(&graph, &[0, 1, 2]).unwrap();
    label_node(&mut p, 3);
    assert_eq!(tops(&p, &[vec![0], vec![1, 3], vec![2]])[1], 5120);
}
#[test]
fn half_gap_keeps_slot_lines_above_next_rank() {
    for profile in ["vector", "cell"] {
        let params = Params::for_profile(profile).unwrap();
        assert!(params.slot / 2 < (params.rank_gap + 1) / 2, "{profile}");
    }
    for i in 0..100 {
        let (mut p, ls) = case(i);
        let middles: Vec<usize> = p
            .chains
            .iter()
            .filter(|chain| chain.len() >= 3)
            .map(|chain| chain[(chain.len() - 1) / 2])
            .collect();
        for v in middles {
            label_node(&mut p, v);
        }
        let x = cross_coords(&p, &ls).unwrap();
        let r = route(&p, &ls, &x).unwrap();
        let (_, top) = rank_coords(&p, &ls, &r).unwrap();
        let h = heights(&p, &ls);
        for (k, gap) in r.gaps.iter().enumerate() {
            let line = top[k] + h[k] + p.params.slot * gap.slots + p.params.slot / 2;
            assert!(gap.slots == 0 || line < top[k + 1], "case {i} gap {k}");
        }
    }
}
