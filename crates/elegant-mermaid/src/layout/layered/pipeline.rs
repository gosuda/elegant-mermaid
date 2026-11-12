use super::{
    LayoutError, coords, cycles,
    graph::{Edge, Graph, Node, Params},
    normalize, order, rank, route,
};
use crate::layout::input::Input;
use crate::{
    geom::{Point, Rect, Size},
    measure::{self, Metric, Role},
    scene::*,
};

pub struct EdgeOptions<'a> {
    pub marker_start: Option<MarkerName>,
    pub marker_end: Option<MarkerName>,
    pub stroke: &'a str,
    pub min_length: i32,
}

fn constant(profile: Profile, name: &str) -> i32 {
    let prefix = profile.as_str();
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|r| {
            r.name
                .strip_prefix(prefix)
                .and_then(|s| s.strip_prefix('.'))
                == Some(name)
        })
        .map_or(0, |r| r.value)
}
fn narrow(n: i64) -> Result<i32, LayoutError> {
    i32::try_from(n).map_err(|_| LayoutError::Overflow)
}
fn text(input: &Input, index: usize) -> &str {
    let b = &input.boxes[index];
    input
        .labels
        .iter()
        .find(|l| l.owner == b.id)
        .map_or(&b.id, |l| &l.text)
}
fn measured<'a>(
    input: &'a Input,
    edges: &[EdgeOptions<'_>],
) -> Result<(Graph, Vec<Vec<measure::Line<'a>>>), LayoutError> {
    let p = input.profile;
    let metric = if p == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(Role::Label)
    };
    let mut graph = Graph {
        nodes: Vec::new(),
        edges: Vec::new(),
        params: Params::for_profile(p.as_str())?,
    };
    let mut lines = Vec::new();
    for (i, b) in input.boxes.iter().enumerate() {
        let ls = measure::wrap(
            text(input, i),
            measure::wrap_target(
                metric,
                0,
                i32::try_from(input.options.max_width).map_err(|_| LayoutError::Overflow)?,
            ),
            metric,
        )?;
        let tw = ls.iter().map(|l| l.width).max().unwrap_or(0);
        let w = narrow(
            i64::from(tw)
                + 2 * i64::from(constant(p, "node_pad_x"))
                + 2 * i64::from(constant(p, "node_border")),
        )?;
        let h = narrow(
            i64::try_from(ls.len()).map_err(|_| LayoutError::Overflow)?
                * i64::from(constant(p, "line_h"))
                + 2 * i64::from(constant(p, "node_pad_y"))
                + 2 * i64::from(constant(p, "node_border")),
        )?;
        graph.nodes.push(Node {
            id: b.id.clone(),
            decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
            w: w.max(constant(p, "node_min_w")),
            h: h.max(constant(p, "node_min_h")),
        });
        lines.push(ls);
    }
    for (i, r) in input.routes.iter().enumerate() {
        let tail = graph
            .nodes
            .iter()
            .position(|n| n.id == r.from)
            .ok_or(LayoutError::Domain)?;
        let head = graph
            .nodes
            .iter()
            .position(|n| n.id == r.to)
            .ok_or(LayoutError::Domain)?;
        graph.edges.push(Edge {
            tail,
            head,
            min_len: edges[i].min_length.max(1),
            decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
            reversed: false,
        });
    }
    size_ports(&mut graph)?;
    if matches!(input.direction, Direction::Lr | Direction::Rl) {
        for n in &mut graph.nodes {
            std::mem::swap(&mut n.w, &mut n.h);
        }
    }
    Ok((graph, lines))
}
fn size_ports(g: &mut Graph) -> Result<(), LayoutError> {
    for i in 0..g.nodes.len() {
        let mut top = std::collections::BTreeSet::new();
        let mut bottom = std::collections::BTreeSet::new();
        for e in &g.edges {
            if e.head == i {
                top.insert(e.tail);
            }
            if e.tail == i {
                bottom.insert(e.head);
            }
        }
        let count =
            i64::try_from(top.len().max(bottom.len()) + 1).map_err(|_| LayoutError::Overflow)?;
        g.nodes[i].w = g.nodes[i]
            .w
            .max(narrow(count * i64::from(g.params.port_gap))?);
    }
    Ok(())
}
fn component(g: &Graph, members: &[usize]) -> Graph {
    Graph {
        nodes: members.iter().map(|&i| g.nodes[i].clone()).collect(),
        edges: g
            .edges
            .iter()
            .filter_map(|e| {
                Some(Edge {
                    tail: members.iter().position(|i| *i == e.tail)?,
                    head: members.iter().position(|i| *i == e.head)?,
                    ..*e
                })
            })
            .collect(),
        params: g.params,
    }
}
fn component_layout(g: &Graph) -> Result<(Vec<Rect>, Vec<route::EdgeRoute>, bool), LayoutError> {
    let ranks = rank::rank(g)?;
    let p = normalize::normalize(g, &ranks.ranks)?;
    let ordered = order::order_with_budget(&p, order::OrderOptions::default())?;
    let x = coords::cross_coords(&p, &ordered.layers)?;
    let r = route::route(&p, &ordered.layers, &x)?;
    let (y, top) = coords::rank_coords(&p, &ordered.layers, &r)?;
    let (routes, _) = route::route_points(&p, &ordered.layers, &x, &y, &top, &r)?;
    let boxes = g
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| Rect {
            x: x[i] - n.w / 2,
            y: y[i],
            w: n.w,
            h: n.h,
        })
        .collect();
    Ok((
        boxes,
        routes,
        ranks.budget_exhausted || ordered.budget_exhausted,
    ))
}
fn bounds(
    boxes: &[Rect],
    routes: &[route::EdgeRoute],
) -> Result<(i32, i32, i32, i32), LayoutError> {
    let mut min_x = boxes.first().map_or(0, |b| b.x);
    let mut min_y = boxes.first().map_or(0, |b| b.y);
    let mut right = 0;
    let mut bottom = 0;
    for b in boxes {
        min_x = min_x.min(b.x);
        min_y = min_y.min(b.y);
        right = right.max(narrow(i64::from(b.x) + i64::from(b.w))?);
        bottom = bottom.max(narrow(i64::from(b.y) + i64::from(b.h))?);
    }
    for r in routes {
        for p in &r.points {
            min_x = min_x.min(p.x);
            min_y = min_y.min(p.y);
            right = right.max(p.x);
            bottom = bottom.max(p.y);
        }
    }
    Ok((min_x, min_y, right, bottom))
}
pub fn layout_family(
    input: &Input,
    edges: &[EdgeOptions<'_>],
) -> Result<(Scene, bool), LayoutError> {
    if edges.len() != input.routes.len() {
        return Err(LayoutError::Domain);
    }
    let (mut g, lines) = measured(input, edges)?;
    let reversed = cycles::break_cycles(&g)?;
    for (e, reversed) in g.edges.iter_mut().zip(reversed) {
        e.reversed = reversed;
    }
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let mut dump = Dump::new(input.kind, options);
    dump.boxes = input
        .boxes
        .iter()
        .map(|b| SceneBox {
            id: b.id.clone(),
            role: b.role,
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            parent: b.parent.clone(),
            exclusive: b.exclusive,
        })
        .collect();
    dump.routes = input
        .routes
        .iter()
        .map(|r| SceneRoute {
            id: r.id.clone(),
            from: r.from.clone(),
            to: r.to.clone(),
            orthogonal: true,
            points: Vec::new(),
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        })
        .collect();
    let mut canvas = Size { w: 0, h: 0 };
    let mut cursor = 0;
    let mut budget = false;
    for members in rank::components(&g)? {
        let cg = component(&g, &members);
        let (boxes, routes, exhausted) = component_layout(&cg)?;
        budget |= exhausted;
        let (mx, my, right, bottom) = bounds(&boxes, &routes)?;
        for (i, b) in boxes.iter().enumerate() {
            dump.boxes[members[i]].rect = Rect {
                x: narrow(i64::from(b.x) + i64::from(cursor) - i64::from(mx))?,
                y: narrow(i64::from(b.y) - i64::from(my))?,
                ..*b
            };
        }
        for (e, r) in cg.edges.iter().zip(routes) {
            let mut points = r.points;
            if e.reversed {
                points.reverse();
            }
            for p in &mut points {
                p.x = narrow(i64::from(p.x) + i64::from(cursor) - i64::from(mx))?;
                p.y = narrow(i64::from(p.y) - i64::from(my))?;
            }
            dump.routes[usize::try_from(e.decl).map_err(|_| LayoutError::Domain)?].points = points;
        }
        cursor = narrow(
            i64::from(cursor) + i64::from(right) - i64::from(mx) + i64::from(g.params.node_gap),
        )?;
        canvas.w = cursor - g.params.node_gap;
        canvas.h = canvas.h.max(narrow(i64::from(bottom) - i64::from(my))?);
    }
    orient(&mut dump, &mut canvas);
    let items = assemble(&dump, &lines, edges);
    Ok((Scene::new(canvas, dump, items), budget))
}
fn point(p: Point, d: Direction, h: i32) -> Point {
    match d {
        Direction::Bt => Point { x: p.x, y: h - p.y },
        Direction::Lr => Point { x: p.y, y: p.x },
        Direction::Rl => Point { x: h - p.y, y: p.x },
        _ => p,
    }
}
fn orient(dump: &mut Dump, canvas: &mut Size) {
    let d = dump.options.direction;
    let h = canvas.h;
    for b in &mut dump.boxes {
        let r = &mut b.rect;
        let mut p = point(Point { x: r.x, y: r.y }, d, h);
        match d {
            Direction::Bt => p.y -= r.h,
            Direction::Lr => std::mem::swap(&mut r.w, &mut r.h),
            Direction::Rl => {
                std::mem::swap(&mut r.w, &mut r.h);
                p.x -= r.w;
            }
            _ => {}
        }
        r.x = p.x;
        r.y = p.y;
    }
    for r in &mut dump.routes {
        for p in &mut r.points {
            *p = point(*p, d, h);
        }
    }
    if matches!(d, Direction::Lr | Direction::Rl) {
        std::mem::swap(&mut canvas.w, &mut canvas.h);
    }
}
fn assemble(
    dump: &Dump,
    lines: &[Vec<measure::Line<'_>>],
    edges: &[EdgeOptions<'_>],
) -> Vec<Group> {
    let mut groups = Vec::new();
    for (r, edge) in dump.routes.iter().zip(edges) {
        groups.push(Group {
            role: GroupRole::Edge,
            owner: r.id.clone(),
            items: edge_items(r, edge, dump.options.profile),
        });
    }
    for (i, b) in dump.boxes.iter().enumerate() {
        let lh = constant(dump.options.profile, "line_h");
        let height = lines[i].iter().fold(0, |height, _| height + lh);
        let rect = Rect {
            y: b.rect.y + (b.rect.h - height) / 2,
            h: height,
            ..b.rect
        };
        groups.push(Group {
            role: GroupRole::Node,
            owner: b.id.clone(),
            items: vec![
                Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Node),
                    rect: b.rect,
                }),
                Item::Text(TextItem {
                    rect,
                    role: TextRole::Label,
                    size: 14,
                    align: Align::Middle,
                    style: TextStyle::Text,
                    series: 0,
                    lines: lines[i].iter().map(|l| vec![Run::plain(l.text)]).collect(),
                }),
            ],
        });
    }
    groups
}

fn marker_axis(a: Point, b: Point) -> MarkerAxis {
    let dx = i64::from(b.x) - i64::from(a.x);
    let dy = i64::from(b.y) - i64::from(a.y);
    match (dx.abs() >= dy.abs(), dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

fn edge_items(route: &SceneRoute, edge: &EdgeOptions<'_>, profile: Profile) -> Vec<Item> {
    if edge.stroke == "invisible" {
        return Vec::new();
    }
    let mut shape = Shape::plain(ShapeStyle::Edge);
    match edge.stroke {
        "thick" => shape.width = Width::Emphasis,
        "dotted" => shape.line = Line::Dotted,
        "dashed" => shape.line = Line::Dashed,
        _ => {}
    }
    let mut items = vec![Item::Polyline(PolylineItem {
        shape,
        points: route.points.clone(),
        corner: constant(profile, "corner_radius"),
    })];
    if route.points.len() < 2 {
        return items;
    }
    let end = route.points.len() - 1;
    if let Some(marker) = edge.marker_start {
        items.push(Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[0],
            axis: marker_axis(route.points[1], route.points[0]),
        }));
    }
    if let Some(marker) = edge.marker_end {
        items.push(Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[end],
            axis: marker_axis(route.points[end - 1], route.points[end]),
        }));
    }
    items
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pipeline_bounds_include_route_points() {
        let boxes = [Rect {
            x: 0,
            y: 0,
            w: 3,
            h: 3,
        }];
        let routes = [route::EdgeRoute {
            original: 0,
            points: vec![Point { x: 8, y: 5 }],
        }];
        assert_eq!(bounds(&boxes, &routes), Ok((0, 0, 8, 5)));
    }
}
