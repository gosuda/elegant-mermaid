use super::{
    LayoutError,
    graph::Graph,
    pipeline::{Component, Measurements},
};
use crate::{
    geom::{Point, Rect},
    layout::input::Input,
    scene::{BoxRole, Direction},
};

#[derive(Clone, Copy)]
struct Transform {
    direction: Direction,
    offset: Point,
}
impl Transform {
    fn point(self, point: Point) -> Result<Point, LayoutError> {
        let x = i64::from(point.x);
        let y = i64::from(point.y);
        let (x, y) = match self.direction {
            Direction::Tb => (x, y),
            Direction::Bt => (x, -y),
            Direction::Lr => (y, x),
            Direction::Rl => (-y, x),
        };
        Ok(Point {
            x: narrow(x + i64::from(self.offset.x))?,
            y: narrow(y + i64::from(self.offset.y))?,
        })
    }
    fn rect(self, rect: Rect) -> Result<Rect, LayoutError> {
        let a = self.point(Point {
            x: rect.x,
            y: rect.y,
        })?;
        let b = self.point(Point {
            x: narrow(i64::from(rect.x) + i64::from(rect.w))?,
            y: narrow(i64::from(rect.y) + i64::from(rect.h))?,
        })?;
        Ok(Rect {
            x: a.x.min(b.x),
            y: a.y.min(b.y),
            w: narrow((i64::from(a.x) - i64::from(b.x)).abs())?,
            h: narrow((i64::from(a.y) - i64::from(b.y)).abs())?,
        })
    }
}
struct PlacedBox<'a> {
    id: &'a str,
    role: BoxRole,
    rect: Rect,
}
struct PlacedRoute<'a> {
    from: &'a str,
    to: &'a str,
    points: &'a [Point],
    transform: Transform,
}
struct Geometry<'a> {
    boxes: Vec<PlacedBox<'a>>,
    routes: Vec<PlacedRoute<'a>>,
    labels: Vec<Rect>,
}

pub(super) fn score(
    graph: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
    part: &Component,
) -> Result<i64, LayoutError> {
    let geometry = expand(graph, input, measurements, part)?;
    let (mut extent, mut count) = (0i64, 0i64);
    for item in geometry
        .boxes
        .iter()
        .filter(|item| item.role == BoxRole::Node)
    {
        extent = extent
            .checked_add((i64::from(item.rect.w) + i64::from(item.rect.h)) / 2)
            .ok_or(LayoutError::Overflow)?;
        count += 1;
    }
    let mean = (extent / count.max(1)).max(1);
    let mut crossings = 0i64;
    let mut bends = 0i64;
    let mut length = 0i64;
    let mut against = 0i64;
    for (index, route) in geometry.routes.iter().enumerate() {
        let (route_bends, route_length) = route_stats(route.points)?;
        bends = bends
            .checked_add(route_bends)
            .ok_or(LayoutError::Overflow)?;
        length = length
            .checked_add(route_length)
            .ok_or(LayoutError::Overflow)?;
        for other in &geometry.routes[..index] {
            crossings = crossings
                .checked_add(route_crossings(route, other)?)
                .ok_or(LayoutError::Overflow)?;
        }
        let from = geometry
            .boxes
            .iter()
            .find(|item| item.id == route.from)
            .ok_or(LayoutError::Domain)?
            .rect;
        let to = geometry
            .boxes
            .iter()
            .find(|item| item.id == route.to)
            .ok_or(LayoutError::Domain)?
            .rect;
        let (a, b) = match input.direction {
            Direction::Tb | Direction::Bt => (
                2 * i64::from(from.y) + i64::from(from.h),
                2 * i64::from(to.y) + i64::from(to.h),
            ),
            Direction::Lr | Direction::Rl => (
                2 * i64::from(from.x) + i64::from(from.w),
                2 * i64::from(to.x) + i64::from(to.w),
            ),
        };
        let delta = if matches!(input.direction, Direction::Bt | Direction::Rl) {
            a - b
        } else {
            b - a
        };
        if delta < 0 {
            against += 1;
        }
    }
    let area = area(&geometry)?;
    crate::scene::metrics::soft_cost(&crate::scene::metrics::Metrics {
        nodes: count,
        mean_node_extent: mean,
        crossings,
        bends,
        against_flow_edges: against,
        total_route_length: length,
        canvas_area: area,
        ..Default::default()
    })
    .map_err(|_| LayoutError::Overflow)
}

fn expand<'a>(
    graph: &'a Graph,
    input: &'a Input,
    measurements: &'a Measurements<'_, '_>,
    part: &'a Component,
) -> Result<Geometry<'a>, LayoutError> {
    let transform = Transform {
        direction: input.direction,
        offset: Point { x: 0, y: 0 },
    };
    let mut geometry = Geometry {
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
    };
    for (node, rect) in graph.nodes.iter().zip(&part.boxes) {
        let model = input
            .boxes
            .get(usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?)
            .ok_or(LayoutError::Domain)?;
        geometry.boxes.push(PlacedBox {
            id: &node.id,
            role: model.role,
            rect: transform.rect(*rect)?,
        });
    }
    for (edge, route) in graph
        .edges
        .iter()
        .zip(&part.routes)
        .filter(|(edge, _)| edge.decl != i32::MAX)
    {
        geometry.routes.push(PlacedRoute {
            from: &graph.nodes[edge.tail].id,
            to: &graph.nodes[edge.head].id,
            points: &route.points,
            transform,
        });
    }
    for (_, rect) in &part.labels {
        geometry.labels.push(transform.rect(*rect)?);
    }
    for (node, rect) in &part.titles {
        if input
            .labels
            .iter()
            .any(|label| label.owner == graph.nodes[*node].id)
        {
            geometry.labels.push(transform.rect(*rect)?);
        }
    }
    let pad = super::pipeline::constant(input.profile, "cluster_pad");
    for fixed in measurements.fixed {
        let Some(index) = graph.nodes.iter().position(|node| node.id == fixed.id) else {
            continue;
        };
        let frame = transform.rect(part.boxes[index])?;
        let title = part
            .titles
            .iter()
            .find(|(node, _)| *node == index)
            .ok_or(LayoutError::Domain)?
            .1;
        let offset =
            super::isolate::content_offset(frame, transform.rect(title)?, fixed.direction, pad)?;
        let child_transform = Transform {
            direction: Direction::Tb,
            offset,
        };
        for item in fixed.scene.boxes() {
            geometry.boxes.push(PlacedBox {
                id: &item.id,
                role: item.role,
                rect: child_transform.rect(item.rect)?,
            });
        }
        for route in fixed.scene.routes() {
            geometry.routes.push(PlacedRoute {
                from: &route.from,
                to: &route.to,
                points: &route.points,
                transform: child_transform,
            });
        }
        for label in fixed.scene.labels() {
            geometry.labels.push(child_transform.rect(label.rect)?);
        }
    }
    Ok(geometry)
}

fn route_stats(points: &[Point]) -> Result<(i64, i64), LayoutError> {
    let (mut bends, mut length) = (0i64, 0i64);
    let mut previous: Option<(i128, i128)> = None;
    for pair in points.windows(2).filter(|pair| pair[0] != pair[1]) {
        let dx = i128::from(pair[1].x) - i128::from(pair[0].x);
        let dy = i128::from(pair[1].y) - i128::from(pair[0].y);
        let squared = i64::try_from(dx * dx + dy * dy).map_err(|_| LayoutError::Overflow)?;
        length = length
            .checked_add(crate::geom::isqrt(squared)?)
            .ok_or(LayoutError::Overflow)?;
        if let Some((px, py)) = previous {
            let cross = i64::try_from(px * dy - py * dx).map_err(|_| LayoutError::Overflow)?;
            let dot = i64::try_from(px * dx + py * dy).map_err(|_| LayoutError::Overflow)?;
            if cross != 0 || dot < 0 {
                bends += 1;
            }
        }
        previous = Some((dx, dy));
    }
    Ok((bends, length))
}

fn route_crossings(a: &PlacedRoute<'_>, b: &PlacedRoute<'_>) -> Result<i64, LayoutError> {
    let mut count = 0i64;
    for x in a.points.windows(2).filter(|pair| pair[0] != pair[1]) {
        let x0 = a.transform.point(x[0])?;
        let x1 = a.transform.point(x[1])?;
        for y in b.points.windows(2).filter(|pair| pair[0] != pair[1]) {
            let y0 = b.transform.point(y[0])?;
            let y1 = b.transform.point(y[1])?;
            if orientation(x0, x1, y0)? * orientation(x0, x1, y1)? == -1
                && orientation(y0, y1, x0)? * orientation(y0, y1, x1)? == -1
            {
                count = count.checked_add(1).ok_or(LayoutError::Overflow)?;
            }
        }
    }
    Ok(count)
}
fn orientation(a: Point, b: Point, c: Point) -> Result<i64, LayoutError> {
    let cross = (i128::from(b.x) - i128::from(a.x)) * (i128::from(c.y) - i128::from(a.y))
        - (i128::from(b.y) - i128::from(a.y)) * (i128::from(c.x) - i128::from(a.x));
    Ok(i64::try_from(cross)
        .map_err(|_| LayoutError::Overflow)?
        .signum())
}

fn area(geometry: &Geometry<'_>) -> Result<i64, LayoutError> {
    let mut bounds: Option<(i64, i64, i64, i64)> = None;
    let mut add = |x: i64, y: i64| {
        bounds = Some(match bounds {
            Some((left, top, right, bottom)) => {
                (left.min(x), top.min(y), right.max(x), bottom.max(y))
            }
            None => (x, y, x, y),
        });
    };
    for rect in geometry
        .boxes
        .iter()
        .map(|item| item.rect)
        .chain(geometry.labels.iter().copied())
    {
        add(i64::from(rect.x), i64::from(rect.y));
        add(
            i64::from(rect.x) + i64::from(rect.w),
            i64::from(rect.y) + i64::from(rect.h),
        );
    }
    for route in &geometry.routes {
        for &point in route.points {
            let point = route.transform.point(point)?;
            add(i64::from(point.x), i64::from(point.y));
        }
    }
    let Some((left, top, right, bottom)) = bounds else {
        return Ok(0);
    };
    (right - left)
        .checked_mul(bottom - top)
        .ok_or(LayoutError::Overflow)
}
fn narrow(value: i64) -> Result<i32, LayoutError> {
    i32::try_from(value).map_err(|_| LayoutError::Overflow)
}

#[cfg(test)]
#[path = "step14_cost_tests.rs"]
mod step14_tests;
