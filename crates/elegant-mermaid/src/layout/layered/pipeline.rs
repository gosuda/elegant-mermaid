use super::{
    LayoutError, cycles,
    graph::{Edge, Graph, Node, Params},
    normalize, order, rank, route,
};
use crate::layout::input::{Input, SizeRule};
use crate::{
    geom::{Point, Rect, Size},
    measure::{self, Metric, Role},
    scene::*,
};

#[path = "pipeline/scene_items.rs"]
mod scene_items;
use scene_items::assemble;
#[path = "pipeline/attachment_geometry.rs"]
mod attachment_geometry;
#[path = "pipeline/attachment_metadata.rs"]
pub(super) mod attachment_metadata;
#[path = "pipeline/attachment_parts.rs"]
mod attachment_parts;
#[path = "pipeline/attachment_routes.rs"]
mod attachment_routes;
#[path = "pipeline/attachments.rs"]
mod attachments;
#[path = "pipeline/endpoint_sides.rs"]
mod endpoint_sides;
pub(crate) use endpoint_sides::reroute_endpoints;
#[path = "pipeline/component_core.rs"]
mod component_core;
#[path = "pipeline/component_input.rs"]
mod component_input;
use component_core::component_core;
pub(super) use component_core::{Component, Measurements};

#[derive(Clone, Copy)]
pub struct EdgeOptions<'a> {
    pub marker_start: Option<MarkerName>,
    pub marker_end: Option<MarkerName>,
    pub stroke: &'a str,
    pub min_length: i32,
}

pub(super) fn constant(profile: Profile, name: &str) -> i32 {
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
pub(super) fn margin(input: &Input) -> i32 {
    match input.spacing.canvas_margin {
        0 => constant(input.profile, "canvas_margin"),
        value => value,
    }
}
fn narrow(n: i64) -> Result<i32, LayoutError> {
    i32::try_from(n).map_err(|_| LayoutError::Overflow)
}
fn kind_wrapping_width(profile: Profile, kind: &str) -> i32 {
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|r| {
            r.name
                .strip_prefix(profile.as_str())
                .and_then(|s| s.strip_prefix('.'))
                .and_then(|s| s.strip_prefix(kind))
                == Some(".wrapping_width")
        })
        .map_or(0, |r| r.value)
}
fn text(input: &Input, index: usize) -> &str {
    let b = &input.boxes[index];
    input
        .labels
        .iter()
        .find(|l| l.owner == b.id)
        .map_or(&b.text, |l| &l.text)
}
fn measured<'a>(
    input: &'a Input,
    edges: &[EdgeOptions<'_>],
) -> Result<(Graph, Vec<Vec<measure::StyledLine<'a>>>), LayoutError> {
    let p = input.profile;
    let metric = if p == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(Role::Label)
    };
    let metric = crate::scene::configured_metric(metric, &input.options.config);
    let params = Params::for_profile(p.as_str())?.spaced(input.spacing);
    let mut lines = Vec::new();
    let target = measure::wrap_target(
        metric,
        kind_wrapping_width(p, input.kind),
        if p == Profile::Cell {
            i32::try_from(input.options.max_width).map_err(|_| LayoutError::Overflow)?
        } else {
            0
        },
    );
    let mut graph = Graph {
        nodes: Vec::new(),
        edges: Vec::new(),
        params,
    };
    measure_nodes(input, metric, target, &mut graph, &mut lines)?;
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
            min_len: edges[i]
                .min_length
                .max(if input.labels.iter().any(|l| l.owner == r.id) {
                    2
                } else {
                    1
                }),
            decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
            reversed: false,
        });
    }
    if matches!(input.direction, Direction::Lr | Direction::Rl) {
        for n in &mut graph.nodes {
            std::mem::swap(&mut n.w, &mut n.h);
        }
    }
    Ok((graph, lines))
}

fn measure_nodes<'a>(
    input: &'a Input,
    metric: Metric,
    target: i32,
    graph: &mut Graph,
    lines: &mut Vec<Vec<measure::StyledLine<'a>>>,
) -> Result<(), LayoutError> {
    let p = input.profile;
    for (i, b) in input.boxes.iter().enumerate() {
        let ls = measure::styled_lines(text(input, i), target, metric)?;
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
        let rule = input.sizes.get(i).copied().unwrap_or_default();
        let content = match rule {
            SizeRule::Measured => Size { w, h },
            SizeRule::Content(size) if size.w == 0 && size.h == 0 => Size { w, h },
            SizeRule::Content(size) | SizeRule::Exact(size) => size,
        };
        if content.w < 0 || content.h < 0 {
            return Err(LayoutError::Domain);
        }
        graph.nodes.push(Node {
            id: b.id.clone(),
            decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
            w: if b.role == BoxRole::Group {
                tw
            } else if matches!(rule, SizeRule::Exact(_)) {
                content.w
            } else {
                content.w.max(constant(p, "node_min_w"))
            },
            h: if b.role == BoxRole::Group {
                narrow(
                    i64::try_from(ls.len().max(1)).map_err(|_| LayoutError::Overflow)?
                        * i64::from(constant(p, "line_h")),
                )?
            } else if matches!(rule, SizeRule::Exact(_)) {
                content.h
            } else {
                content.h.max(constant(p, "node_min_h"))
            },
        });
        lines.push(ls);
    }
    Ok(())
}
fn size_ports(
    proper: &mut super::graph::Proper,
    graph: &mut Graph,
    input: &Input,
) -> Result<(), LayoutError> {
    for (index, node) in graph.nodes.iter_mut().enumerate() {
        let declaration = usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?;
        if matches!(input.sizes.get(declaration), Some(SizeRule::Exact(_))) {
            continue;
        }
        if !input
            .boxes
            .get(declaration)
            .is_some_and(|b| b.role == BoxRole::Node)
        {
            continue;
        }
        let top: std::collections::BTreeSet<_> = proper.r#in[index]
            .iter()
            .map(|&edge| proper.edges[edge].tail)
            .collect();
        let bottom: std::collections::BTreeSet<_> = proper.out[index]
            .iter()
            .map(|&edge| proper.edges[edge].head)
            .collect();
        let count =
            i64::try_from(top.len().max(bottom.len()) + 1).map_err(|_| LayoutError::Overflow)?;
        node.w = node
            .w
            .max(narrow(count * i64::from(graph.params.port_gap))?);
        proper.nodes[index].node.w = node.w;
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
pub(super) fn component_layout(
    g: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
    options: order::OrderOptions,
) -> Result<Component, LayoutError> {
    attachments::layout(g, input, measurements, options)
}

pub(super) fn bounds<'a>(
    boxes: impl IntoIterator<Item = &'a Rect>,
    routes: &[route::EdgeRoute],
) -> Result<(i32, i32, i32, i32), LayoutError> {
    let mut boxes = boxes.into_iter();
    let first = boxes.next();
    let mut min_x = first.map_or(0, |b| b.x);
    let mut min_y = first.map_or(0, |b| b.y);
    let mut right = min_x;
    let mut bottom = min_y;
    for b in first.into_iter().chain(boxes) {
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
    attachment_metadata::validate(input)?;
    if let Some(scene) = super::isolate::layout(input, edges)? {
        return Ok(scene);
    }
    layout_unisolated(input, edges, &[])
}

pub(super) fn layout_unisolated(
    input: &Input,
    edges: &[EdgeOptions<'_>],
    fixed: &[super::isolate::Fixed<'_>],
) -> Result<(Scene, bool), LayoutError> {
    let route_lines = measure_route_labels(input)?;
    let (mut g, lines) = measured(input, edges)?;
    let titles = lines
        .iter()
        .map(|lines| {
            let mut size = Size {
                w: lines.iter().map(|line| line.width).max().unwrap_or(0),
                h: narrow(
                    i64::try_from(lines.len().max(1)).map_err(|_| LayoutError::Overflow)?
                        * i64::from(constant(input.profile, "line_h")),
                )?,
            };
            if matches!(input.direction, Direction::Lr | Direction::Rl) {
                std::mem::swap(&mut size.w, &mut size.h);
            }
            Ok(size)
        })
        .collect::<Result<Vec<_>, LayoutError>>()?;
    let route_stacks = super::labels::stacks(input, &route_lines)?;
    let measurements = Measurements {
        route_lines,
        titles,
        route_stacks,
        fixed,
    };
    let route_lines = &measurements.route_lines;
    apply_fixed(&mut g, fixed, input)?;
    let sizes = edge_sizes(&g, &measurements.route_stacks)?;
    super::loops::size_nodes(&mut g, &sizes, input)?;
    super::clusters::connect(&mut g, input);
    attachment_metadata::connect(&mut g, input);
    let mut dump = blank_dump(input);
    let mut canvas = Size { w: 0, h: 0 };
    let mut placed_titles = Vec::new();
    let mut budget = false;
    let text = DumpText {
        input,
        original: input,
        nodes: &lines,
        routes: route_lines,
    };
    for part in place_components(&g, input, &measurements)? {
        let (size, exhausted) = write_component(&mut dump, &mut placed_titles, part, &text)?;
        canvas.w = canvas.w.max(size.w);
        canvas.h = canvas.h.max(size.h);
        budget |= exhausted;
    }
    dump.labels
        .sort_by_key(|label| input.labels.iter().position(|l| l.id == label.id));
    let margin = margin(input);
    for (_, rect) in &mut placed_titles {
        rect.x = narrow(i64::from(rect.x) + i64::from(margin))?;
        rect.y = narrow(i64::from(rect.y) + i64::from(margin))?;
    }
    add_margin(&mut dump, &mut canvas, margin)?;
    for (_, rect) in &mut placed_titles {
        orient_rect(rect, input.direction, canvas.h);
    }
    orient(&mut dump, &mut canvas);
    let items = assemble(
        &dump,
        input,
        &placed_titles,
        &lines,
        &measurements.route_lines,
        edges,
    )?;
    Ok((Scene::new(canvas, dump, items), budget))
}

fn apply_fixed(
    graph: &mut Graph,
    fixed: &[super::isolate::Fixed<'_>],
    input: &Input,
) -> Result<(), LayoutError> {
    let pad = constant(input.profile, "cluster_pad");
    for fixed in fixed {
        let node = graph
            .nodes
            .iter_mut()
            .find(|node| node.id == fixed.id)
            .ok_or(LayoutError::Domain)?;
        let (size, _) = fixed_geometry(
            fixed,
            Size {
                w: node.w,
                h: node.h,
            },
            input.direction,
            pad,
        )?;
        node.w = size.w;
        node.h = size.h;
    }
    Ok(())
}

fn fixed_geometry(
    fixed: &super::isolate::Fixed<'_>,
    mut title: Size,
    parent: Direction,
    pad: i32,
) -> Result<(Size, Rect), LayoutError> {
    if matches!(parent, Direction::Lr | Direction::Rl) {
        std::mem::swap(&mut title.w, &mut title.h);
    }
    let mut size = fixed.scene.canvas();
    if matches!(fixed.direction, Direction::Lr | Direction::Rl) {
        std::mem::swap(&mut size.w, &mut size.h);
        std::mem::swap(&mut title.w, &mut title.h);
    }
    size.w = narrow(i64::from(size.w.max(title.w)) + 2 * i64::from(pad))?;
    size.h = narrow(i64::from(size.h) + i64::from(title.h) + 2 * i64::from(pad))?;
    let mut rect = Rect {
        x: (size.w - title.w) / 2,
        y: pad,
        w: title.w,
        h: title.h,
    };
    orient_rect(&mut rect, fixed.direction, size.h);
    if matches!(fixed.direction, Direction::Lr | Direction::Rl) {
        std::mem::swap(&mut size.w, &mut size.h);
    }
    rect = match parent {
        Direction::Tb => rect,
        Direction::Bt => Rect {
            y: size.h - rect.y - rect.h,
            ..rect
        },
        Direction::Lr => Rect {
            x: rect.y,
            y: rect.x,
            w: rect.h,
            h: rect.w,
        },
        Direction::Rl => Rect {
            x: rect.y,
            y: size.w - rect.x - rect.w,
            w: rect.h,
            h: rect.w,
        },
    };
    if matches!(parent, Direction::Lr | Direction::Rl) {
        std::mem::swap(&mut size.w, &mut size.h);
    }
    Ok((size, rect))
}

fn blank_dump(input: &Input) -> Dump {
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
    dump
}

struct PackedComponent {
    members: Vec<usize>,
    graph: Graph,
    layout: Component,
    bounds: (i32, i32, i32, i32),
    origin: Point,
}

fn place_components(
    graph: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
) -> Result<Vec<PackedComponent>, LayoutError> {
    let (mut parts, sizes) = collect_components(graph, input, measurements)?;
    let target = super::pack::target(
        input.profile,
        input.options.max_width,
        parts.iter().flat_map(|part| part.layout.packing_rects()),
        parts.iter().flat_map(|part| {
            part.layout
                .routes
                .iter()
                .map(|route| route.points.as_slice())
        }),
        &sizes,
        graph.params.node_gap,
    )?;
    for (part, origin) in
        parts
            .iter_mut()
            .zip(super::pack::shelves(&sizes, target, graph.params.node_gap)?)
    {
        part.origin = origin;
    }
    Ok(parts)
}

fn collect_components(
    graph: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
) -> Result<(Vec<PackedComponent>, Vec<Size>), LayoutError> {
    let mut parts = Vec::new();
    let mut sizes = Vec::new();
    for members in rank::components(graph)? {
        let mut component = component(graph, &members);
        if !component
            .nodes
            .iter()
            .any(|node| input.groups.iter().any(|group| group.id == node.id))
        {
            let reversed = cycles::break_cycles(&component)?;
            for (edge, reversed) in component.edges.iter_mut().zip(reversed) {
                edge.reversed = reversed;
            }
        }
        let layout = super::portfolio::layout(&component, input, measurements)?;
        let bounds = bounds(layout.packing_rects(), &layout.routes)?;
        sizes.push(Size {
            w: narrow(i64::from(bounds.2) - i64::from(bounds.0))?,
            h: narrow(i64::from(bounds.3) - i64::from(bounds.1))?,
        });
        parts.push(PackedComponent {
            members,
            graph: component,
            layout,
            bounds,
            origin: Point { x: 0, y: 0 },
        });
    }
    Ok((parts, sizes))
}

struct DumpText<'a, 'text> {
    input: &'a Input,
    original: &'a Input,
    nodes: &'a [Vec<measure::StyledLine<'text>>],
    routes: &'a [Vec<measure::StyledLine<'text>>],
}

fn write_component(
    dump: &mut Dump,
    placed_titles: &mut Vec<(usize, Rect)>,
    packed: PackedComponent,
    text: &DumpText<'_, '_>,
) -> Result<(Size, bool), LayoutError> {
    let PackedComponent {
        members,
        graph,
        layout,
        bounds: (mx, my, right, bottom),
        origin,
    } = packed;
    let Component {
        boxes,
        routes,
        labels,
        titles,
        budget,
        ..
    } = layout;
    let input = text.input;
    for (node, rect) in titles {
        let index = members[node];
        let rect = placed_rect(rect, origin, Point { x: mx, y: my })?;
        placed_titles.push((index, rect));
        if let Some(label) = input
            .labels
            .iter()
            .find(|l| l.owner == input.boxes[index].id)
        {
            let original = text
                .original
                .labels
                .iter()
                .find(|l| l.id == label.id)
                .ok_or(LayoutError::Domain)?;
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: original.text.clone(),
                rect,
                lines: text.nodes[index]
                    .iter()
                    .map(|line| line.text.to_owned())
                    .collect(),
            });
        }
    }
    for (index, rect) in labels {
        let label = &input.labels[index];
        dump.labels.push(SceneLabel {
            id: label.id.clone(),
            owner: label.owner.clone(),
            text: text.original.labels[index].text.clone(),
            rect: placed_rect(rect, origin, Point { x: mx, y: my })?,
            lines: text.routes[index]
                .iter()
                .map(|line| line.text.to_owned())
                .collect(),
        });
    }
    for (index, rect) in boxes.into_iter().enumerate() {
        dump.boxes[members[index]].rect = placed_rect(rect, origin, Point { x: mx, y: my })?;
    }
    for (edge, route) in graph.edges.iter().zip(routes) {
        let declaration = usize::try_from(edge.decl).map_err(|_| LayoutError::Domain)?;
        if declaration >= input.routes.len() {
            continue;
        }
        let mut points = route.points;
        for point in &mut points {
            point.x = narrow(i64::from(point.x) + i64::from(origin.x) - i64::from(mx))?;
            point.y = narrow(i64::from(point.y) + i64::from(origin.y) - i64::from(my))?;
        }
        dump.routes[declaration].points = points;
    }
    Ok((
        Size {
            w: narrow(i64::from(origin.x) + i64::from(right) - i64::from(mx))?,
            h: narrow(i64::from(origin.y) + i64::from(bottom) - i64::from(my))?,
        },
        budget,
    ))
}

fn placed_rect(rect: Rect, origin: Point, minimum: Point) -> Result<Rect, LayoutError> {
    Ok(Rect {
        x: narrow(i64::from(rect.x) + i64::from(origin.x) - i64::from(minimum.x))?,
        y: narrow(i64::from(rect.y) + i64::from(origin.y) - i64::from(minimum.y))?,
        ..rect
    })
}

fn add_margin(dump: &mut Dump, canvas: &mut Size, margin: i32) -> Result<(), LayoutError> {
    for rect in dump
        .boxes
        .iter_mut()
        .map(|b| &mut b.rect)
        .chain(dump.labels.iter_mut().map(|l| &mut l.rect))
    {
        rect.x = narrow(i64::from(rect.x) + i64::from(margin))?;
        rect.y = narrow(i64::from(rect.y) + i64::from(margin))?;
    }
    for route in &mut dump.routes {
        for point in &mut route.points {
            point.x = narrow(i64::from(point.x) + i64::from(margin))?;
            point.y = narrow(i64::from(point.y) + i64::from(margin))?;
        }
    }
    canvas.w = narrow(i64::from(canvas.w) + 2 * i64::from(margin))?;
    canvas.h = narrow(i64::from(canvas.h) + 2 * i64::from(margin))?;
    Ok(())
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
        orient_rect(&mut b.rect, d, h);
    }
    for label in &mut dump.labels {
        orient_rect(&mut label.rect, d, h);
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
fn measure_route_labels(input: &Input) -> Result<Vec<Vec<measure::StyledLine<'_>>>, LayoutError> {
    let metric = if input.profile == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(Role::Label)
    };
    let metric = crate::scene::configured_metric(metric, &input.options.config);
    let width = measure::wrap_target(
        metric,
        kind_wrapping_width(input.profile, input.kind),
        if input.profile == Profile::Cell {
            i32::try_from(input.options.max_width).map_err(|_| LayoutError::Overflow)?
        } else {
            0
        },
    );
    input
        .labels
        .iter()
        .map(|label| {
            if input.routes.iter().any(|r| r.id == label.owner) {
                measure::styled_lines(&label.text, width, metric)
            } else {
                Ok(Vec::new())
            }
        })
        .collect()
}

fn edge_sizes(
    graph: &Graph,
    stacks: &[super::labels::Stack],
) -> Result<Vec<(i32, i32)>, LayoutError> {
    graph
        .edges
        .iter()
        .map(|edge| {
            let declaration = usize::try_from(edge.decl).map_err(|_| LayoutError::Domain)?;
            Ok(stacks
                .get(declaration)
                .map_or((0, 0), |stack| (stack.size.w, stack.size.h)))
        })
        .collect()
}

fn orient_rect(rect: &mut Rect, direction: Direction, height: i32) {
    let mut position = point(
        Point {
            x: rect.x,
            y: rect.y,
        },
        direction,
        height,
    );
    match direction {
        Direction::Bt => position.y -= rect.h,
        Direction::Lr => std::mem::swap(&mut rect.w, &mut rect.h),
        Direction::Rl => {
            std::mem::swap(&mut rect.w, &mut rect.h);
            position.x -= rect.w;
        }
        _ => {}
    }
    rect.x = position.x;
    rect.y = position.y;
}

#[cfg(test)]
#[path = "pipeline_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "pipeline/attachment_tests.rs"]
mod attachment_tests;
