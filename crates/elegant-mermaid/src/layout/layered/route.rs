use super::{
    LayoutError,
    coords::{heights, narrow, params, positions},
    graph::Proper,
};
use crate::geom::{Point, Rect};
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutingSegment {
    pub tail: usize,
    pub head: usize,
    pub decl: i32,
    pub slot: i32,
    pub source_x: i32,
    pub target_x: i32,
    pub edges: Vec<usize>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RoutingGap {
    pub segments: Vec<RoutingSegment>,
    pub slots: i32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Routing {
    pub gaps: Vec<RoutingGap>,
    pub source_x: Vec<i32>,
    pub target_x: Vec<i32>,
    pub segment: Vec<usize>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdgeRoute {
    pub original: usize,
    pub points: Vec<Point>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Box {
    pub id: String,
    pub rect: Rect,
}
fn assign_ports(
    p: &Proper,
    v: usize,
    edges: &[usize],
    x: &[i32],
    out: &mut [i32],
) -> Result<(), LayoutError> {
    let other = |i: usize| {
        let e = p.edges[i];
        if e.tail == v { e.head } else { e.tail }
    };
    let mut ns: Vec<_> = edges.iter().map(|&i| other(i)).collect();
    ns.sort_unstable();
    ns.dedup();
    ns.sort_by_key(|&w| (x[w], p.nodes[w].node.decl, w));
    let w = i64::from(p.nodes[v].node.w);
    let left = i64::from(x[v]) - w / 2;
    if p.nodes[v].label {
        for &i in edges {
            out[i] = narrow(left)?;
        }
        return Ok(());
    }
    for &i in edges {
        let j = ns
            .iter()
            .position(|&n| n == other(i))
            .ok_or(LayoutError::Domain)?;
        let numerator = i64::try_from(j + 1)
            .map_err(|_| LayoutError::Overflow)?
            .checked_mul(w)
            .ok_or(LayoutError::Overflow)?;
        let denominator = i64::try_from(ns.len() + 1).map_err(|_| LayoutError::Overflow)?;
        out[i] = narrow(left + numerator / denominator)?;
    }
    Ok(())
}
fn conflict(a: &RoutingSegment, b: &RoutingSegment) -> bool {
    a.source_x != a.target_x
        && b.source_x != b.target_x
        && a.source_x.min(a.target_x).max(b.source_x.min(b.target_x))
            <= a.source_x.max(a.target_x).min(b.source_x.max(b.target_x))
}
fn arc_key(s: &RoutingSegment, index: usize) -> (bool, i64, i32, usize) {
    let right = s.target_x > s.source_x;
    let x = i64::from(s.source_x);
    (right, if right { -x } else { x }, s.decl, index)
}
pub(crate) fn number_gap(g: &mut RoutingGap) -> Result<(), LayoutError> {
    let n = g.segments.len();
    let mut incoming = vec![0; n];
    let mut out = vec![Vec::new(); n];
    let mut done = vec![false; n];
    for (i, a) in g.segments.iter().enumerate() {
        for (j, b) in g.segments.iter().enumerate() {
            if arc_key(a, i) < arc_key(b, j) && conflict(a, b) {
                out[i].push(j);
                incoming[j] += 1;
            }
        }
    }
    for _ in 0..n {
        let v = (0..n)
            .filter(|&i| !done[i] && incoming[i] == 0)
            .min_by_key(|&i| (g.segments[i].decl, i))
            .ok_or(LayoutError::Domain)?;
        done[v] = true;
        if g.segments[v].source_x != g.segments[v].target_x {
            g.segments[v].slot = g.segments[v].slot.max(0);
            g.slots = g.slots.max(
                g.segments[v]
                    .slot
                    .checked_add(1)
                    .ok_or(LayoutError::Overflow)?,
            );
        }
        for &w in &out[v] {
            incoming[w] -= 1;
            g.segments[w].slot = g.segments[w].slot.max(
                g.segments[v]
                    .slot
                    .checked_add(1)
                    .ok_or(LayoutError::Overflow)?,
            );
        }
    }
    Ok(())
}
pub fn route(p: &Proper, layers: &[Vec<usize>], x: &[i32]) -> Result<Routing, LayoutError> {
    route_selected(p, layers, x, &[])
}

pub fn route_selected(
    p: &Proper,
    layers: &[Vec<usize>],
    x: &[i32],
    reversed: &[bool],
) -> Result<Routing, LayoutError> {
    positions(p, layers)?;
    params(p)?;
    if x.len() != p.nodes.len() {
        return Err(LayoutError::Domain);
    }
    let mut r = Routing {
        gaps: vec![RoutingGap::default(); layers.len().saturating_sub(1)],
        source_x: vec![0; p.edges.len()],
        target_x: vec![0; p.edges.len()],
        segment: vec![usize::MAX; p.edges.len()],
    };
    let mut incoming = vec![Vec::new(); p.nodes.len()];
    let mut outgoing = vec![Vec::new(); p.nodes.len()];
    for (i, e) in p.edges.iter().enumerate() {
        incoming[e.head].push(i);
        outgoing[e.tail].push(i);
    }
    for v in 0..p.nodes.len() {
        assign_ports(p, v, &outgoing[v], x, &mut r.source_x)?;
        assign_ports(p, v, &incoming[v], x, &mut r.target_x)?;
    }
    for (i, e) in p.edges.iter().enumerate() {
        if reversed.get(e.original).copied().unwrap_or(false) {
            continue;
        }
        let rank = usize::try_from(p.rank[e.tail]).map_err(|_| LayoutError::Domain)?;
        let g = &mut r.gaps[rank];
        if let Some(j) = g
            .segments
            .iter()
            .position(|s| s.tail == e.tail && s.head == e.head)
        {
            g.segments[j].edges.push(i);
            g.segments[j].decl = g.segments[j].decl.min(e.decl);
            r.segment[i] = j;
        } else {
            r.segment[i] = g.segments.len();
            g.segments.push(RoutingSegment {
                tail: e.tail,
                head: e.head,
                decl: e.decl,
                slot: -1,
                source_x: r.source_x[i],
                target_x: r.target_x[i],
                edges: vec![i],
            });
        }
    }
    for g in &mut r.gaps {
        number_gap(g)?;
    }
    Ok(r)
}
pub fn route_points(
    p: &Proper,
    layers: &[Vec<usize>],
    x: &[i32],
    y: &[i32],
    rank_top: &[i32],
    r: &Routing,
) -> Result<(Vec<EdgeRoute>, Vec<Box>), LayoutError> {
    positions(p, layers)?;
    let d = params(p)?;
    if x.len() != p.nodes.len()
        || y.len() != p.nodes.len()
        || rank_top.len() != layers.len()
        || r.source_x.len() != p.edges.len()
        || r.target_x.len() != p.edges.len()
        || r.segment.len() != p.edges.len()
    {
        return Err(LayoutError::Domain);
    }
    let h = heights(p, layers);
    let mut routes: Vec<_> = (0..p.chains.len())
        .map(|original| EdgeRoute {
            original,
            points: Vec::new(),
        })
        .collect();
    for (i, e) in p.edges.iter().enumerate() {
        if r.segment[i] == usize::MAX {
            continue;
        }
        let a = Point {
            x: r.source_x[i],
            y: narrow(i64::from(y[e.tail]) + i64::from(p.nodes[e.tail].node.h))?,
        };
        let b = Point {
            x: r.target_x[i],
            y: y[e.head],
        };
        let mut points = vec![a];
        let rank = usize::try_from(p.rank[e.tail]).map_err(|_| LayoutError::Domain)?;
        let segment = r
            .gaps
            .get(rank)
            .and_then(|gap| gap.segments.get(r.segment[i]))
            .ok_or(LayoutError::Domain)?;
        if segment.slot >= 0 {
            let offset = i64::from(d.slot)
                .checked_mul(i64::from(segment.slot) + 1)
                .ok_or(LayoutError::Overflow)?;
            let mid = narrow(
                i64::from(rank_top[rank]) + i64::from(h[rank]) + offset + i64::from(d.slot) / 2,
            )?;
            points.push(Point { x: a.x, y: mid });
            points.push(Point { x: b.x, y: mid });
        }
        points.push(b);
        let out = &mut routes
            .get_mut(e.original)
            .ok_or(LayoutError::Domain)?
            .points;
        for pt in points {
            if out.last() != Some(&pt) {
                out.push(pt);
            }
        }
    }
    Ok((routes, Vec::new()))
}

#[cfg(test)]
mod tests {
    use super::super::{
        coords::{cross_coords, rank_coords},
        graph::{Edge, Graph, Node, Params},
        normalize::normalize,
        rank::rank,
    };
    use super::*;
    fn hand(n: usize, edges: &[(usize, usize)]) -> Result<(Proper, Vec<Vec<usize>>), LayoutError> {
        let g = Graph {
            nodes: (0..n)
                .map(|i| {
                    Ok(Node {
                        decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
                        w: 2048,
                        h: 1280,
                        ..Node::default()
                    })
                })
                .collect::<Result<_, _>>()?,
            edges: edges
                .iter()
                .enumerate()
                .map(|(i, &(tail, head))| {
                    Ok(Edge {
                        tail,
                        head,
                        decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
                        min_len: 1,
                        reversed: false,
                    })
                })
                .collect::<Result<_, _>>()?,
            params: Params::for_profile("vector")?,
        };
        let p = normalize(&g, &rank(&g)?.ranks)?;
        let mut layers = Vec::<Vec<usize>>::new();
        for (v, &r) in p.rank.iter().enumerate() {
            let r = usize::try_from(r).map_err(|_| LayoutError::Domain)?;
            layers.resize_with(layers.len().max(r + 1), Vec::new);
            layers[r].push(v);
        }
        Ok((p, layers))
    }
    #[test]
    fn layered_straight_route() -> Result<(), LayoutError> {
        let (p, l) = hand(2, &[(0, 1)])?;
        let x = cross_coords(&p, &l)?;
        let r = route(&p, &l, &x)?;
        let (y, t) = rank_coords(&p, &l, &r)?;
        let (es, _) = route_points(&p, &l, &x, &y, &t, &r)?;
        assert_eq!(x, [0, 0]);
        assert_eq!(y, [0, 4352]);
        assert_eq!(
            es[0].points,
            [Point { x: 0, y: 1280 }, Point { x: 0, y: 4352 }]
        );
        Ok(())
    }
    #[test]
    fn layered_diamond_ports() -> Result<(), LayoutError> {
        let (p, l) = hand(4, &[(0, 1), (0, 2), (1, 3), (2, 3)])?;
        let x = cross_coords(&p, &l)?;
        assert_eq!(x, [1792, 0, 3584, 1792]);
        let r = route(&p, &l, &x)?;
        assert_eq!(r.source_x, [1450, 2133, 0, 3584]);
        assert_eq!(r.target_x, [0, 3584, 1450, 2133]);
        assert!(r.gaps.iter().all(|g| g.slots == 1));
        let (y, t) = rank_coords(&p, &l, &r)?;
        let (es, _) = route_points(&p, &l, &x, &y, &t, &r)?;
        let expected = [
            [(1450, 1280), (1450, 2432), (0, 2432), (0, 5120)],
            [(2133, 1280), (2133, 2432), (3584, 2432), (3584, 5120)],
            [(0, 6400), (0, 7552), (1450, 7552), (1450, 10240)],
            [(3584, 6400), (3584, 7552), (2133, 7552), (2133, 10240)],
        ];
        for (e, want) in es.iter().zip(expected) {
            assert_eq!(e.points, want.map(|(x, y)| Point { x, y }));
        }
        Ok(())
    }
    #[test]
    fn layered_three_ports() -> Result<(), LayoutError> {
        let (p, l) = hand(4, &[(0, 1), (0, 2), (0, 3)])?;
        assert_eq!(
            route(&p, &l, &[2000, 0, 2000, 4000])?.source_x,
            [1488, 2000, 2512]
        );
        Ok(())
    }
    fn seg(source_x: i32, target_x: i32, decl: i32) -> RoutingSegment {
        RoutingSegment {
            tail: 0,
            head: 0,
            decl,
            slot: -1,
            source_x,
            target_x,
            edges: Vec::new(),
        }
    }
    #[test]
    fn layered_arc_key_direction() {
        let cases = [
            (seg(900, 100, 5), seg(100, 900, 0)),
            (seg(300, 0, 1), seg(400, 100, 0)),
            (seg(400, 900, 1), seg(300, 800, 0)),
            (seg(300, 900, 0), seg(300, 800, 1)),
            (seg(300, 900, 4), seg(300, 800, 4)),
            (seg(300, 300, 7), seg(100, 900, 0)),
        ];
        for (a, b) in &cases {
            assert!(arc_key(a, 0) < arc_key(b, 1), "{a:?} {b:?}");
            assert!(arc_key(b, 1) > arc_key(a, 0), "{a:?} {b:?}");
        }
    }
    #[test]
    fn layered_gap_direction() -> Result<(), LayoutError> {
        let mut g = RoutingGap {
            segments: vec![
                seg(100, 900, 3),
                seg(100, 900, 3),
                seg(700, 200, 0),
                seg(300, 300, 1),
            ],
            slots: 0,
        };
        number_gap(&mut g)?;
        let slots: Vec<i32> = g.segments.iter().map(|s| s.slot).collect();
        assert_eq!(slots, [1, 2, 0, -1]);
        assert_eq!(g.slots, 3);
        Ok(())
    }
    fn number_by_old_key(g: &mut RoutingGap) {
        let mut order: Vec<usize> = (0..g.segments.len()).collect();
        order.sort_by_key(|&i| (g.segments[i].source_x, g.segments[i].decl, i));
        g.slots = 0;
        for (n, &i) in order.iter().enumerate() {
            if g.segments[i].source_x == g.segments[i].target_x {
                continue;
            }
            let slot = order[..n]
                .iter()
                .filter(|&&u| conflict(&g.segments[u], &g.segments[i]))
                .map(|&u| g.segments[u].slot + 1)
                .max()
                .unwrap_or(0);
            g.segments[i].slot = slot;
            g.slots = g.slots.max(slot + 1);
        }
    }
    fn orient(a: Point, b: Point, c: Point) -> i64 {
        let cross = (i64::from(b.x) - i64::from(a.x)) * (i64::from(c.y) - i64::from(a.y))
            - (i64::from(b.y) - i64::from(a.y)) * (i64::from(c.x) - i64::from(a.x));
        cross.signum()
    }
    fn crosses(s: &[Point], t: &[Point]) -> bool {
        orient(s[0], s[1], t[0]) * orient(s[0], s[1], t[1]) == -1
            && orient(t[0], t[1], s[0]) * orient(t[0], t[1], s[1]) == -1
    }
    fn crossings(routes: &[EdgeRoute]) -> usize {
        let mut count = 0;
        for (i, a) in routes.iter().enumerate() {
            for b in &routes[i + 1..] {
                count += a
                    .points
                    .windows(2)
                    .flat_map(|s| b.points.windows(2).filter(move |t| crosses(s, t)))
                    .count();
            }
        }
        count
    }
    fn edge_slots(p: &Proper, r: &Routing) -> Result<Vec<i32>, LayoutError> {
        (0..p.edges.len())
            .map(|i| {
                let gap =
                    usize::try_from(p.rank[p.edges[i].tail]).map_err(|_| LayoutError::Domain)?;
                Ok(r.gaps[gap].segments[r.segment[i]].slot)
            })
            .collect()
    }
    fn routed_crossings(
        p: &Proper,
        l: &[Vec<usize>],
        x: &[i32],
        r: &Routing,
    ) -> Result<usize, LayoutError> {
        let (y, t) = rank_coords(p, l, r)?;
        let (routes, _) = route_points(p, l, x, &y, &t, r)?;
        Ok(crossings(&routes))
    }
    fn fan(
        edges: &[(usize, usize)],
        x: &[i32],
        want: &[i32],
        old: &[i32],
    ) -> Result<(), LayoutError> {
        let (p, l) = hand(5, edges)?;
        let r = route(&p, &l, x)?;
        assert_eq!(edge_slots(&p, &r)?, want);
        assert_eq!(routed_crossings(&p, &l, x, &r)?, 0);
        let mut r = route(&p, &l, x)?;
        r.gaps.iter_mut().for_each(number_by_old_key);
        assert_eq!(edge_slots(&p, &r)?, old);
        assert_eq!(routed_crossings(&p, &l, x, &r)?, 2);
        Ok(())
    }
    #[test]
    fn layered_fan_out_slot_order() -> Result<(), LayoutError> {
        fan(
            &[(0, 1), (0, 2), (0, 3), (0, 4)],
            &[5000, 0, 2000, 8000, 10000],
            &[0, 1, 1, 0],
            &[0, 1, 0, 1],
        )
    }
    #[test]
    fn layered_fan_in_slot_order() -> Result<(), LayoutError> {
        fan(
            &[(0, 4), (1, 4), (2, 4), (3, 4)],
            &[0, 2000, 8000, 10000, 5000],
            &[1, 0, 0, 1],
            &[0, 1, 0, 1],
        )
    }
    #[test]
    fn layered_coordinate_overflow() -> Result<(), LayoutError> {
        let (mut p, l) = hand(4, &[(0, 1), (0, 2), (0, 3)])?;
        p.params.node_gap = i32::MAX;
        assert_eq!(cross_coords(&p, &l), Err(LayoutError::Overflow));
        let (p, l) = hand(2, &[(0, 1)])?;
        let mut r = route(&p, &l, &[0, 0])?;
        r.gaps[0].slots = i32::MAX;
        assert_eq!(rank_coords(&p, &l, &r), Err(LayoutError::Overflow));
        Ok(())
    }
}
