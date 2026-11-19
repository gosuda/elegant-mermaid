use super::{
    LayoutError,
    clusters::Cluster,
    graph::{Graph, Proper},
    route::{EdgeRoute, Routing},
};
use crate::geom::{Point, Rect};

pub fn number(
    clusters: &[Cluster],
    p: &Proper,
    x: &[i32],
    routing: &mut Routing,
) -> Result<(), LayoutError> {
    for gap in &mut routing.gaps {
        for segment in &mut gap.segments {
            let Some(cluster) = clusters.iter().find(|c| {
                c.node == segment.tail && segment.edges.iter().any(|&i| p.edges[i].tail == c.node)
            }) else {
                continue;
            };
            segment.source_x = cluster
                .left
                .iter()
                .map(|&v| i64::from(x[v]) - i64::from(p.nodes[v].node.w) / 2)
                .min()
                .ok_or(LayoutError::Domain)
                .and_then(super::coords::narrow)?;
        }
        gap.slots = 0;
        for segment in &mut gap.segments {
            segment.slot = -1;
        }
        super::route::number_gap(gap)?;
    }
    Ok(())
}

pub fn place(clusters: &[Cluster], semantic: &Graph, boxes: &[Rect], routes: &mut [EdgeRoute]) {
    for (edge, route) in semantic.edges.iter().zip(routes) {
        if route.points.len() < 2 {
            continue;
        }
        if let Some(cluster) = clusters.iter().find(|c| c.node == edge.tail) {
            source(&mut route.points, boxes[cluster.node]);
        }
        if let Some(cluster) = clusters.iter().find(|c| c.node == edge.head) {
            route.points.reverse();
            source(&mut route.points, boxes[cluster.node]);
            route.points.reverse();
        }
    }
}

fn source(points: &mut Vec<Point>, frame: Rect) {
    let port = points[0];
    let adjacent = points[1];
    if port.y != frame.y || adjacent.y <= frame.y {
        return;
    }
    let mut routed = Vec::with_capacity(points.len() + 2);
    routed.push(port);
    routed.push(Point {
        x: frame.x,
        y: frame.y,
    });
    routed.push(Point {
        x: frame.x,
        y: adjacent.y,
    });
    let continuation = if points.get(2).is_some_and(|point| point.y == adjacent.y) {
        2
    } else {
        1
    };
    routed.extend_from_slice(&points[continuation..]);
    routed.dedup();
    *points = routed;
}
