use super::{
    LayoutError,
    graph::{Graph, Proper},
    route::{self, EdgeRoute, Routing, RoutingSegment},
};
use crate::geom::{Point, Rect};

pub struct Lane {
    edge: usize,
    x: i32,
    source: i32,
    target: i32,
    upper: usize,
    lower: usize,
    source_run: usize,
    target_run: usize,
}
pub struct LaneInput<'a> {
    pub graph: &'a Graph,
    pub proper: &'a Proper,
    pub x: &'a [i32],
    pub extents: &'a [i32],
    pub sizes: &'a [(i32, i32)],
}
pub struct LanePlacement<'a> {
    pub graph: &'a Graph,
    pub proper: &'a Proper,
    pub layers: &'a [Vec<usize>],
    pub y: &'a [i32],
    pub top: &'a [i32],
    pub routing: &'a Routing,
    pub sizes: &'a [(i32, i32)],
}
fn narrow(n: i64) -> Result<i32, LayoutError> {
    i32::try_from(n).map_err(|_| LayoutError::Overflow)
}

pub fn number(
    input: LaneInput<'_>,
    r: &mut Routing,
    all: &Routing,
) -> Result<Vec<Lane>, LayoutError> {
    let LaneInput {
        graph: g,
        proper: p,
        x,
        extents,
        sizes,
    } = input;
    let mut right = 0i64;
    for (i, n) in p.nodes.iter().enumerate() {
        right = right.max(
            i64::from(x[i]) - i64::from(n.node.w) / 2
                + i64::from(n.node.w)
                + i64::from(extents.get(i).copied().unwrap_or(0)),
        );
    }
    let max_label = g
        .edges
        .iter()
        .zip(sizes)
        .filter(|(e, _)| e.reversed)
        .map(|(_, s)| s.0)
        .max()
        .unwrap_or(0);
    let mut lanes = Vec::new();
    for (i, edge) in g
        .edges
        .iter()
        .enumerate()
        .filter(|(_, e)| e.reversed && !e.self_loop())
    {
        let first = p
            .edges
            .iter()
            .position(|e| e.original == i)
            .ok_or(LayoutError::Domain)?;
        let last = p
            .edges
            .iter()
            .rposition(|e| e.original == i)
            .ok_or(LayoutError::Domain)?;
        let source = all.target_x[last];
        let target = all.source_x[first];
        let upper = usize::try_from(p.rank[edge.tail] - 1).map_err(|_| LayoutError::Domain)?;
        let lower = usize::try_from(p.rank[edge.head]).map_err(|_| LayoutError::Domain)?;
        let lane = narrow(
            right
                + i64::from(g.params.slot)
                + i64::try_from(lanes.len()).map_err(|_| LayoutError::Overflow)?
                    * (2 * i64::from(g.params.slot) + i64::from(max_label)),
        )?;
        let source_run = r.gaps[upper].segments.len();
        r.gaps[upper].segments.push(RoutingSegment {
            tail: edge.tail,
            head: edge.head,
            decl: edge.decl,
            slot: -1,
            source_x: leading_boundary(p, x, edge.tail, source),
            target_x: lane,
            edges: Vec::new(),
        });
        let target_run = r.gaps[lower].segments.len();
        r.gaps[lower].segments.push(RoutingSegment {
            tail: edge.tail,
            head: edge.head,
            decl: edge.decl,
            slot: -1,
            source_x: leading_boundary(p, x, edge.head, target),
            target_x: lane,
            edges: Vec::new(),
        });
        lanes.push(Lane {
            edge: i,
            x: lane,
            source,
            target,
            upper,
            lower,
            source_run,
            target_run,
        });
    }
    for gap in &mut r.gaps {
        gap.slots = 0;
        for segment in &mut gap.segments {
            segment.slot = -1;
        }
        route::number_gap(gap)?;
    }
    Ok(lanes)
}

pub fn place(
    input: LanePlacement<'_>,
    lanes: &[Lane],
    routes: &mut [EdgeRoute],
) -> Result<Vec<(usize, Rect)>, LayoutError> {
    let LanePlacement {
        graph: g,
        proper: p,
        layers,
        y,
        top,
        routing,
        sizes,
    } = input;
    let heights = super::coords::heights(p, layers);
    let line = |gap: usize, run: usize| -> Result<i32, LayoutError> {
        narrow(
            i64::from(top[gap])
                + i64::from(heights[gap])
                + i64::from(g.params.slot) * (i64::from(routing.gaps[gap].segments[run].slot) + 1)
                + i64::from(g.params.slot) / 2,
        )
    };
    let mut labels = Vec::new();
    for lane in lanes {
        let edge = g.edges[lane.edge];
        let cs = line(lane.upper, lane.source_run)?;
        let ct = line(lane.lower, lane.target_run)?;
        routes[lane.edge].points = vec![
            Point {
                x: lane.source,
                y: y[edge.tail],
            },
            Point {
                x: lane.source,
                y: cs,
            },
            Point { x: lane.x, y: cs },
            Point { x: lane.x, y: ct },
            Point {
                x: lane.target,
                y: ct,
            },
            Point {
                x: lane.target,
                y: narrow(i64::from(y[edge.head]) + i64::from(g.nodes[edge.head].h))?,
            },
        ];
        labels.push((
            lane.edge,
            Rect {
                x: narrow(i64::from(lane.x) + i64::from(g.params.slot))?,
                y: narrow(
                    crate::geom::floor_div(i64::from(ct) + i64::from(cs), 2)
                        - i64::from(sizes[lane.edge].1) / 2,
                )?,
                w: sizes[lane.edge].0,
                h: sizes[lane.edge].1,
            },
        ));
    }
    Ok(labels)
}

fn leading_boundary(p: &Proper, x: &[i32], node: usize, port: i32) -> i32 {
    let anchor = &p.nodes[node];
    if anchor.node.h != 0 || anchor.node.id.is_empty() {
        return port;
    }
    p.nodes
        .iter()
        .enumerate()
        .filter(|(i, candidate)| {
            candidate.edge == -2
                && candidate.node.decl == anchor.node.decl
                && p.rank[*i] == p.rank[node]
        })
        .map(|(i, _)| x[i])
        .min()
        .unwrap_or(port)
}
