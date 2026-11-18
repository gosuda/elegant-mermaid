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
    /// Per-original-edge reserved lane x, indexed by `graph.edges` position.
    /// `None` keeps the ordinary global lane placement. A `Some` slice must
    /// hold exactly `graph.edges.len()` entries; only reversed non-self-loop
    /// edges with a `Some` entry use their reserved x, the rest fall back.
    pub reserved_x: Option<&'a [Option<i32>]>,
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
        ..
    } = input;
    if let Some(reserved) = input.reserved_x
        && reserved.len() != g.edges.len()
    {
        return Err(LayoutError::Domain);
    }
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
    collect_lanes(&mut lanes, input, r, all, (right, max_label))?;
    for gap in &mut r.gaps {
        gap.slots = 0;
        for segment in &mut gap.segments {
            segment.slot = -1;
        }
        route::number_gap(gap)?;
    }
    Ok(lanes)
}

fn collect_lanes(
    lanes: &mut Vec<Lane>,
    input: LaneInput<'_>,
    r: &mut Routing,
    all: &Routing,
    spacing: (i64, i32),
) -> Result<(), LayoutError> {
    let LaneInput {
        graph: g,
        proper: p,
        x,
        reserved_x,
        ..
    } = input;
    let (right, max_label) = spacing;
    let mut fallback = 0usize;
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
        let lane = match reserved_x.and_then(|rx| rx[i]) {
            Some(reserved) => reserved,
            None => {
                let lane = narrow(
                    right
                        + i64::from(g.params.slot)
                        + i64::try_from(fallback).map_err(|_| LayoutError::Overflow)?
                            * (2 * i64::from(g.params.slot) + i64::from(max_label)),
                )?;
                fallback += 1;
                lane
            }
        };
        let source_run = r.gaps[upper].segments.len();
        r.gaps[upper].segments.push(RoutingSegment {
            tail: edge.tail,
            head: edge.head,
            decl: edge.decl,
            slot: -1,
            source_x: leading_boundary(p, x, edge.tail, source)?,
            target_x: lane,
            edges: Vec::new(),
        });
        let target_run = r.gaps[lower].segments.len();
        r.gaps[lower].segments.push(RoutingSegment {
            tail: edge.tail,
            head: edge.head,
            decl: edge.decl,
            slot: -1,
            source_x: leading_boundary(p, x, edge.head, target)?,
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
    Ok(())
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

fn leading_boundary(p: &Proper, x: &[i32], node: usize, port: i32) -> Result<i32, LayoutError> {
    let anchor = &p.nodes[node];
    if anchor.node.h != 0 || anchor.node.id.is_empty() {
        return Ok(port);
    }
    let mut frame_left = None::<i64>;
    for (i, candidate) in p.nodes.iter().enumerate() {
        if candidate.edge == -2 && candidate.node.decl == anchor.node.decl {
            let left = i64::from(x[i]) - i64::from(candidate.node.w) / 2;
            frame_left = Some(frame_left.map_or(left, |lowest| lowest.min(left)));
        }
    }
    frame_left.map_or(Ok(port), narrow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::layered::graph::{Node, Params, Proper, ProperNode};
    use crate::{LayoutOptions, Profile, layout, parse};

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    const SOURCE: &str = "flowchart TB\n  n1[T]\n  subgraph g2[g2]\n    n3[X]\n  end\n  n3 --> n1\n  g2 --> n3\n  n1 --> g2\n";

    fn border(id: &str, decl: i32, w: i32, edge: i32) -> ProperNode {
        ProperNode {
            node: Node {
                id: id.to_owned(),
                decl,
                w,
                h: 0,
            },
            dummy: false,
            label: false,
            edge,
        }
    }

    #[test]
    fn layered_leading_boundary_is_the_frame_left_edge() -> TestResult {
        let p = Proper {
            nodes: vec![
                border("g", 0, 0, -4),
                border("", 0, 512, -2),
                border("", 0, 512, -2),
                border("", 0, 640, -2),
                border("", 1, 512, -2),
                border("", 0, 512, -3),
            ],
            edges: Vec::new(),
            rank: vec![0, 0, 1, 2, 0, 0],
            chains: Vec::new(),
            out: Vec::new(),
            r#in: Vec::new(),
            params: Params::for_profile("vector")?,
        };
        let x = [0, 3000, 2900, 3100, 100, 100];
        let frame_left = p
            .nodes
            .iter()
            .zip(x)
            .filter(|(n, _)| n.edge == -2 && n.node.decl == 0)
            .map(|(n, x)| x - n.node.w / 2)
            .min()
            .ok_or("no left border")?;
        assert_eq!(leading_boundary(&p, &x, 0, -999)?, frame_left);
        assert_eq!(leading_boundary(&p, &x, 5, -999)?, -999);
        Ok(())
    }

    fn channel_runs(points: &[Point], frame_left: i32, frame_top: i32) -> Vec<(i32, i32)> {
        points
            .windows(2)
            .filter(|w| {
                w[0].y == w[1].y
                    && w[0].y > frame_top
                    && w[0].x != w[1].x
                    && (w[0].x == frame_left || w[1].x == frame_left)
            })
            .map(|w| (w[0].y, w[0].x.max(w[1].x)))
            .collect()
    }

    fn orient(a: Point, b: Point, c: Point) -> i64 {
        (i64::from(b.x - a.x) * i64::from(c.y - a.y) - i64::from(b.y - a.y) * i64::from(c.x - a.x))
            .signum()
    }

    fn crossings(p: &[Point], q: &[Point]) -> usize {
        let mut count = 0;
        for a in p.windows(2) {
            for b in q.windows(2) {
                if orient(a[0], a[1], b[0]) * orient(a[0], a[1], b[1]) == -1
                    && orient(b[0], b[1], a[0]) * orient(b[0], b[1], a[1]) == -1
                {
                    count += 1;
                }
            }
        }
        count
    }

    #[test]
    fn layered_reversed_run_at_group_top_starts_at_frame_left() -> TestResult {
        for profile in [Profile::Vector, Profile::Cell] {
            let options = LayoutOptions {
                profile,
                thoroughness: 1,
                ..LayoutOptions::default()
            };
            let scene = layout(&parse(SOURCE), &options)?;
            let rect = |id: &str| scene.boxes().iter().find(|b| b.id == id).map(|b| b.rect);
            let route = |id: &str| {
                scene
                    .routes()
                    .iter()
                    .find(|r| r.id == id)
                    .map(|r| r.points.as_slice())
            };
            let (frame, n1) = (rect("g2").ok_or("no g2")?, rect("n1").ok_or("no n1")?);
            let (e1, e2) = (route("e1").ok_or("no e1")?, route("e2").ok_or("no e2")?);
            assert!(
                n1.y > frame.y,
                "{profile:?}: n1 must lie below g2 so that e2 is drawn upward as a reversed run"
            );
            let first = channel_runs(e1, frame.x, frame.y);
            let second = channel_runs(e2, frame.x, frame.y);
            assert_eq!(
                (first.len(), second.len()),
                (1, 1),
                "{profile:?}: each route needs one channel run on the frame_left gutter"
            );
            assert!(
                first[0].0 < second[0].0,
                "{profile:?}: both runs start at frame_left and go right, so the lower decl (e1) takes the lower slot line: {first:?} {second:?}"
            );
            let descent = e1.last().ok_or("empty e1")?;
            assert!(
                descent.x > frame.x && descent.x < second[0].1 && descent.y > second[0].0,
                "{profile:?}: e1 must descend through the e2 run"
            );
            assert_eq!(
                crossings(e1, e2),
                1,
                "{profile:?}: e1 descends through the higher e2 slot line"
            );
        }
        Ok(())
    }
}
