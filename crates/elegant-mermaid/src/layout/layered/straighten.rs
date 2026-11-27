use super::{
    LayoutError,
    coords::narrow,
    graph::Proper,
    pipeline::PackedComponent,
    route::{self, Routing},
};
use crate::geom::{Point, Rect, polyline_hits_rect};
use crate::layout::input::Input;
use crate::scene::BoxRole;

pub(crate) struct StraightenContext {
    pub(crate) proper: Proper,
    pub(crate) layers: Vec<Vec<usize>>,
    pub(crate) x: Vec<i32>,
    pub(crate) y: Vec<i32>,
    pub(crate) top: Vec<i32>,
    pub(crate) routing: Routing,
    pub(crate) cluster_tops: Vec<usize>,
    pub(crate) border: Vec<bool>,
}

struct WorkBox {
    id: String,
    rect: Rect,
}

fn is_real_node(context: &StraightenContext, index: usize) -> bool {
    let Some(node) = context.proper.nodes.get(index) else {
        return false;
    };
    if node.dummy || node.label {
        return false;
    }
    !context.border.get(index).copied().unwrap_or(true)
}

fn corridor_clear(
    candidate: &[Point; 2],
    tail_id: &str,
    head_id: &str,
    boxes: &[WorkBox],
) -> Result<bool, LayoutError> {
    for work in boxes {
        if work.id == tail_id || work.id == head_id {
            continue;
        }
        if polyline_hits_rect(candidate, work.rect)? {
            return Ok(false);
        }
    }
    Ok(true)
}

struct Proposal {
    chain: usize,
    local: i32,
    saved_source: i32,
    saved_target: i32,
    fx: i32,
    top: i32,
    bottom: i32,
}

pub(crate) fn straighten_parts(
    parts: &mut [PackedComponent],
    input: &Input,
) -> Result<(), LayoutError> {
    let mut needed = false;
    for part in parts.iter() {
        if part
            .layout
            .straighten
            .as_ref()
            .is_some_and(|context| !context.proper.edges.is_empty())
        {
            needed = true;
            break;
        }
    }
    if !needed {
        return Ok(());
    }
    let mut work_routes: Vec<Vec<Vec<Point>>> = Vec::with_capacity(parts.len());
    let mut work_boxes: Vec<WorkBox> = Vec::new();
    let mut part_obstacles: Vec<Vec<WorkBox>> = (0..parts.len()).map(|_| Vec::new()).collect();
    for (part_index, part) in parts.iter().enumerate() {
        let dx = i64::from(part.origin.x) - i64::from(part.bounds.0);
        let dy = i64::from(part.origin.y) - i64::from(part.bounds.1);
        let mut routes = Vec::with_capacity(part.layout.routes.len());
        for route in &part.layout.routes {
            routes.push(translate_points(&route.points, dx, dy)?);
        }
        work_routes.push(routes);
        for (index, rect) in part.layout.boxes.iter().enumerate() {
            let Some(node) = part.graph.nodes.get(index) else {
                continue;
            };
            let declaration = usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?;
            let entry = input.boxes.get(declaration).ok_or(LayoutError::Domain)?;
            if entry.role != BoxRole::Node {
                if part
                    .layout
                    .straighten
                    .as_ref()
                    .is_some_and(|context| is_real_node(context, index))
                {
                    part_obstacles[part_index].push(WorkBox {
                        id: node.id.clone(),
                        rect: translate_rect(rect, dx, dy)?,
                    });
                }
                continue;
            }
            work_boxes.push(WorkBox {
                id: node.id.clone(),
                rect: translate_rect(rect, dx, dy)?,
            });
        }
    }
    for (part, part_boxes) in part_obstacles.iter().enumerate() {
        straighten_part(part, parts, &mut work_routes, &work_boxes, part_boxes)?;
    }
    Ok(())
}

fn straighten_part(
    part: usize,
    parts: &mut [PackedComponent],
    work_routes: &mut [Vec<Vec<Point>>],
    work_boxes: &[WorkBox],
    part_boxes: &[WorkBox],
) -> Result<(), LayoutError> {
    let steps = parts
        .get(part)
        .and_then(|part| part.layout.straighten.as_ref())
        .map_or(0, |context| context.proper.edges.len());
    let (dx, dy) = parts
        .get(part)
        .map(|part| {
            (
                i64::from(part.origin.x) - i64::from(part.bounds.0),
                i64::from(part.origin.y) - i64::from(part.bounds.1),
            )
        })
        .ok_or(LayoutError::Domain)?;
    for step in 0..steps {
        let Some(proposal) = propose(&*parts, part, step, dx, dy, work_boxes, part_boxes)? else {
            continue;
        };
        if busy(work_routes, part, &proposal) {
            continue;
        }
        let Some(old) = work_routes
            .get(part)
            .and_then(|routes| routes.get(proposal.chain))
        else {
            continue;
        };
        let old = old.clone();
        set_ports(parts, part, step, proposal.local, proposal.local)?;
        let (gap, segment, saved_slot) = straighten_slot(parts, part, step)?;
        let fresh = recompute(&*parts, part);
        restore_slot(parts, part, gap, segment, saved_slot)?;
        let fresh = fresh?;
        let fresh_points = fresh
            .get(proposal.chain)
            .ok_or(LayoutError::Domain)?
            .points
            .clone();
        let new = translate_points(&fresh_points, dx, dy)?;
        if grew(&old, &new, work_routes, part, proposal.chain)? || !route_box_contains(&old, &new) {
            set_ports(
                parts,
                part,
                step,
                proposal.saved_source,
                proposal.saved_target,
            )?;
            continue;
        }
        *work_routes
            .get_mut(part)
            .and_then(|routes| routes.get_mut(proposal.chain))
            .ok_or(LayoutError::Domain)? = new;
        parts
            .get_mut(part)
            .ok_or(LayoutError::Domain)?
            .layout
            .routes
            .get_mut(proposal.chain)
            .ok_or(LayoutError::Domain)?
            .points = fresh_points;
    }
    Ok(())
}

fn propose(
    parts: &[PackedComponent],
    part: usize,
    step: usize,
    dx: i64,
    dy: i64,
    work_boxes: &[WorkBox],
    part_boxes: &[WorkBox],
) -> Result<Option<Proposal>, LayoutError> {
    let context = parts
        .get(part)
        .and_then(|part| part.layout.straighten.as_ref())
        .ok_or(LayoutError::Domain)?;
    let edge = *context.proper.edges.get(step).ok_or(LayoutError::Domain)?;
    if context
        .routing
        .segment
        .get(step)
        .copied()
        .ok_or(LayoutError::Domain)?
        == usize::MAX
    {
        return Ok(None);
    }
    let tail = context
        .proper
        .nodes
        .get(edge.tail)
        .ok_or(LayoutError::Domain)?;
    let head = context
        .proper
        .nodes
        .get(edge.head)
        .ok_or(LayoutError::Domain)?;
    if tail.dummy || tail.label || tail.edge != -1 || head.dummy || head.label || head.edge != -1 {
        return Ok(None);
    }
    if context
        .border
        .get(edge.tail)
        .copied()
        .ok_or(LayoutError::Domain)?
        || context
            .border
            .get(edge.head)
            .copied()
            .ok_or(LayoutError::Domain)?
    {
        return Ok(None);
    }
    if edge.tail == edge.head {
        return Ok(None);
    }
    let source_x = *context
        .routing
        .source_x
        .get(step)
        .ok_or(LayoutError::Domain)?;
    let target_x = *context
        .routing
        .target_x
        .get(step)
        .ok_or(LayoutError::Domain)?;
    if source_x == target_x {
        return Ok(None);
    }
    let tail_left = i64::from(*context.x.get(edge.tail).ok_or(LayoutError::Domain)?)
        - i64::from(tail.node.w) / 2;
    let head_left = i64::from(*context.x.get(edge.head).ok_or(LayoutError::Domain)?)
        - i64::from(head.node.w) / 2;
    let lo = tail_left.max(head_left);
    let hi = (tail_left + i64::from(tail.node.w)).min(head_left + i64::from(head.node.w));
    if lo > hi {
        return Ok(None);
    }
    let cx = straight_port(source_x, target_x, lo, hi);
    let local = narrow(cx)?;
    let top = narrow(
        i64::from(*context.y.get(edge.tail).ok_or(LayoutError::Domain)?)
            + i64::from(tail.node.h)
            + dy,
    )?;
    let bottom = narrow(i64::from(*context.y.get(edge.head).ok_or(LayoutError::Domain)?) + dy)?;
    if top >= bottom {
        return Ok(None);
    }
    let fx = narrow(cx + dx)?;
    let candidate = [Point { x: fx, y: top }, Point { x: fx, y: bottom }];
    if !corridor_clear(&candidate, &tail.node.id, &head.node.id, work_boxes)? {
        return Ok(None);
    }
    if !corridor_clear(&candidate, &tail.node.id, &head.node.id, part_boxes)? {
        return Ok(None);
    }
    Ok(Some(Proposal {
        chain: edge.original,
        local,
        saved_source: source_x,
        saved_target: target_x,
        fx,
        top,
        bottom,
    }))
}

fn busy(work_routes: &[Vec<Vec<Point>>], part: usize, proposal: &Proposal) -> bool {
    for (other_part, routes) in work_routes.iter().enumerate() {
        for (chain, points) in routes.iter().enumerate() {
            if other_part == part && chain == proposal.chain {
                continue;
            }
            for pair in points.windows(2) {
                let (a, b) = (pair[0], pair[1]);
                if a.x != b.x || i64::from(a.x) != i64::from(proposal.fx) {
                    continue;
                }
                let (mut lo, mut hi) = (i64::from(a.y), i64::from(b.y));
                if lo > hi {
                    std::mem::swap(&mut lo, &mut hi);
                }
                if i64::from(proposal.top).max(lo) <= i64::from(proposal.bottom).min(hi) {
                    return true;
                }
            }
        }
    }
    false
}

fn set_ports(
    parts: &mut [PackedComponent],
    part: usize,
    step: usize,
    source: i32,
    target: i32,
) -> Result<(), LayoutError> {
    let context = parts
        .get_mut(part)
        .and_then(|part| part.layout.straighten.as_mut())
        .ok_or(LayoutError::Domain)?;
    *context
        .routing
        .source_x
        .get_mut(step)
        .ok_or(LayoutError::Domain)? = source;
    *context
        .routing
        .target_x
        .get_mut(step)
        .ok_or(LayoutError::Domain)? = target;
    Ok(())
}

/// Temporarily overrides a gap segment slot, returning the location and the
/// previous value so the caller can restore it. A straightened step bypasses
/// lane assignment, mirroring the straight branch of chain construction.
fn straighten_slot(
    parts: &mut [PackedComponent],
    part: usize,
    step: usize,
) -> Result<(usize, usize, i32), LayoutError> {
    let context = parts
        .get_mut(part)
        .and_then(|part| part.layout.straighten.as_mut())
        .ok_or(LayoutError::Domain)?;
    let tail = context
        .proper
        .edges
        .get(step)
        .ok_or(LayoutError::Domain)?
        .tail;
    let rank = *context.proper.rank.get(tail).ok_or(LayoutError::Domain)?;
    let rank = usize::try_from(rank).map_err(|_| LayoutError::Domain)?;
    let segment = *context
        .routing
        .segment
        .get(step)
        .ok_or(LayoutError::Domain)?;
    let slot = context
        .routing
        .gaps
        .get_mut(rank)
        .and_then(|gap| gap.segments.get_mut(segment))
        .ok_or(LayoutError::Domain)?;
    let saved = slot.slot;
    slot.slot = -1;
    Ok((rank, segment, saved))
}

fn restore_slot(
    parts: &mut [PackedComponent],
    part: usize,
    gap: usize,
    segment: usize,
    value: i32,
) -> Result<(), LayoutError> {
    let context = parts
        .get_mut(part)
        .and_then(|part| part.layout.straighten.as_mut())
        .ok_or(LayoutError::Domain)?;
    *context
        .routing
        .gaps
        .get_mut(gap)
        .and_then(|gap| gap.segments.get_mut(segment))
        .map(|segment| &mut segment.slot)
        .ok_or(LayoutError::Domain)? = value;
    Ok(())
}
fn recompute(parts: &[PackedComponent], part: usize) -> Result<Vec<route::EdgeRoute>, LayoutError> {
    let context = parts
        .get(part)
        .and_then(|part| part.layout.straighten.as_ref())
        .ok_or(LayoutError::Domain)?;
    Ok(route::route_points(
        &context.proper,
        &context.layers,
        &context.x,
        &context.y,
        &context.top,
        &context.routing,
        &context.cluster_tops,
    )?
    .0)
}

fn grew(
    old: &[Point],
    new: &[Point],
    work_routes: &[Vec<Vec<Point>>],
    part: usize,
    chain: usize,
) -> Result<bool, LayoutError> {
    let mut before = 0i64;
    let mut after = 0i64;
    for (other_part, routes) in work_routes.iter().enumerate() {
        for (other_chain, points) in routes.iter().enumerate() {
            if other_part == part && other_chain == chain {
                continue;
            }
            before += route_crossings(old, points)?;
            after += route_crossings(new, points)?;
        }
    }
    Ok(after > before)
}

fn route_box_contains(old: &[Point], next: &[Point]) -> bool {
    let Some(first) = old.first() else {
        return next.is_empty();
    };
    let (mut x0, mut y0, mut x1, mut y1) = (first.x, first.y, first.x, first.y);
    for q in &old[1..] {
        x0 = x0.min(q.x);
        y0 = y0.min(q.y);
        x1 = x1.max(q.x);
        y1 = y1.max(q.y);
    }
    next.iter()
        .all(|q| x0 <= q.x && q.x <= x1 && y0 <= q.y && q.y <= y1)
}

fn straight_port(source: i32, target: i32, lo: i64, hi: i64) -> i64 {
    if i64::from(source) >= lo && i64::from(source) <= hi {
        return i64::from(source);
    }
    if i64::from(target) >= lo && i64::from(target) <= hi {
        return i64::from(target);
    }
    lo + (hi - lo) / 2
}

fn route_crossings(a: &[Point], b: &[Point]) -> Result<i64, LayoutError> {
    let mut count = 0i64;
    for i in 1..a.len() {
        for j in 1..b.len() {
            if segments_cross(a[i - 1], a[i], b[j - 1], b[j])? {
                count += 1;
            }
        }
    }
    Ok(count)
}

fn segments_cross(a: Point, b: Point, c: Point, d: Point) -> Result<bool, LayoutError> {
    let x = orientation(a, b, c)?;
    let y = orientation(a, b, d)?;
    let z = orientation(c, d, a)?;
    let w = orientation(c, d, b)?;
    Ok(x * y == -1 && z * w == -1)
}

fn orientation(a: Point, b: Point, c: Point) -> Result<i64, LayoutError> {
    let n = determinant(
        i64::from(b.x) - i64::from(a.x),
        i64::from(b.y) - i64::from(a.y),
        i64::from(c.x) - i64::from(a.x),
        i64::from(c.y) - i64::from(a.y),
    )?;
    if n < 0 {
        return Ok(-1);
    }
    if n > 0 {
        return Ok(1);
    }
    Ok(0)
}

fn determinant(a: i64, b: i64, c: i64, d: i64) -> Result<i64, LayoutError> {
    product(a, d)?
        .checked_sub(product(b, c)?)
        .ok_or(LayoutError::Overflow)
}

fn product(a: i64, b: i64) -> Result<i64, LayoutError> {
    a.checked_mul(b).ok_or(LayoutError::Overflow)
}

fn translate_points(points: &[Point], dx: i64, dy: i64) -> Result<Vec<Point>, LayoutError> {
    points
        .iter()
        .map(|point| {
            Ok(Point {
                x: narrow(i64::from(point.x) + dx)?,
                y: narrow(i64::from(point.y) + dy)?,
            })
        })
        .collect()
}

fn translate_rect(rect: &Rect, dx: i64, dy: i64) -> Result<Rect, LayoutError> {
    Ok(Rect {
        x: narrow(i64::from(rect.x) + dx)?,
        y: narrow(i64::from(rect.y) + dy)?,
        w: rect.w,
        h: rect.h,
    })
}

#[cfg(test)]
#[path = "straighten_tests.rs"]
mod tests;
