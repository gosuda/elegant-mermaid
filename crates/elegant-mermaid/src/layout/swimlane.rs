//! The `swimlane` layout adapter: the layered family with lanes pinned to bands.
//!
//! Each top-level subgraph is one lane cluster pinned to one cross-axis band; the
//! bands are consecutive in declaration order with no gap. Lane thickness is the
//! content thickness plus the title band plus twice the sum of padding and the
//! routing gutter, along the cross axis (x for TB and BT, y for LR and RL).
//! After the canvas grows, route ends resting on a lane frame's old cross side
//! are re-attached to the new side.

use super::input::Input;
use super::layered::pipeline;
use crate::geom::{GeomError as LayoutError, Point, Rect, Size};
use crate::model::swimlane::Model;
use crate::scene::{self, BoxRole, DumpOptions, GroupRole, Item, PathCommand, Profile, Scene};

mod ends;
mod routing;

/// Builds the layered-family input for a swimlane model.
pub fn from_swimlane(model: &Model, profile: Profile, options: DumpOptions) -> Input {
    let mut input = super::flowchart::from_flowchart(&model.flowchart, profile, options);
    input.kind = "swimlane";
    input
}

/// Lays out a swimlane input through the layered pipeline, then pins lane bands.
pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| {
            Ok(pipeline::EdgeOptions {
                marker_start: marker(&route.marker_start),
                marker_end: marker(&route.marker_end),
                stroke: &route.line,
                min_length: i32::try_from(route.min_length).map_err(|_| LayoutError::Overflow)?,
            })
        })
        .collect::<Result<Vec<_>, LayoutError>>()?;
    let (scene, budget) = pipeline::layout_family(input, &edges)?;
    let scene = pin_bands(input, scene)?;
    Ok((scene, budget))
}

fn marker(name: &str) -> Option<crate::scene::MarkerName> {
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == name)
        .and_then(|row| crate::scene::MarkerName::new(row.name))
}

fn constant(profile: Profile, name: &str) -> Result<i32, LayoutError> {
    let prefix = profile.as_str();
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| {
            row.name
                .strip_prefix(prefix)
                .and_then(|rest| rest.strip_prefix('.'))
                == Some(name)
        })
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn narrow(value: i64) -> Result<i32, LayoutError> {
    i32::try_from(value).map_err(|_| LayoutError::Overflow)
}

fn checked_add(value: i64, delta: i64) -> Result<i64, LayoutError> {
    value.checked_add(delta).ok_or(LayoutError::Overflow)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Axis {
    X,
    Y,
}

impl Axis {
    fn of(self, direction: crate::scene::Direction) -> Axis {
        let _ = self;
        match direction {
            crate::scene::Direction::Lr | crate::scene::Direction::Rl => Axis::Y,
            crate::scene::Direction::Tb | crate::scene::Direction::Bt => Axis::X,
        }
    }
    fn value(self, point: Point) -> i32 {
        match self {
            Axis::X => point.x,
            Axis::Y => point.y,
        }
    }
    fn with(self, point: Point, value: i32) -> Point {
        match self {
            Axis::X => Point {
                x: value,
                y: point.y,
            },
            Axis::Y => Point {
                x: point.x,
                y: value,
            },
        }
    }
    fn start(self, rect: Rect) -> i32 {
        match self {
            Axis::X => rect.x,
            Axis::Y => rect.y,
        }
    }
    fn len(self, rect: Rect) -> i32 {
        match self {
            Axis::X => rect.w,
            Axis::Y => rect.h,
        }
    }
    fn set_start(self, rect: &mut Rect, value: i32) {
        match self {
            Axis::X => rect.x = value,
            Axis::Y => rect.y = value,
        }
    }
    fn set_len(self, rect: &mut Rect, value: i32) {
        match self {
            Axis::X => rect.w = value,
            Axis::Y => rect.h = value,
        }
    }
}

fn cross_axis(direction: crate::scene::Direction) -> Axis {
    Axis::X.of(direction)
}

/// One lane band: its members, its content extent, and its content shift.
struct Band {
    id: String,
    members: Vec<String>,
    shift: i64,
    start: i64,
    thickness: i64,
}

/// The per-target cross-axis moves that pin the lane bands.
struct Pin {
    axis: Axis,
    boxes: Vec<(String, i64)>,
    routes: Vec<(String, i64, i64, i32, i32)>,
}

impl Pin {
    fn box_delta(&self, id: &str) -> i64 {
        self.boxes
            .iter()
            .find(|(owner, _)| owner == id)
            .map_or(0, |(_, delta)| *delta)
    }
    fn route(&self, id: &str) -> Option<(i64, i64, i32, i32)> {
        self.routes
            .iter()
            .find(|(owner, ..)| owner == id)
            .map(|&(_, from, to, first, last)| (from, to, first, last))
    }
    fn label_delta(&self, owner: &str) -> i64 {
        match self.route(owner) {
            Some((from, to, ..)) if from == to => from,
            Some(_) => 0,
            None => self.box_delta(owner),
        }
    }
}

/// The cross-axis move for one scene group's items.
enum Move {
    Constant {
        axis: Axis,
        delta: i64,
    },
    Route {
        axis: Axis,
        from: i64,
        to: i64,
        first: i32,
        last: i32,
    },
}

impl Move {
    fn value(&self, value: i32) -> Result<i32, LayoutError> {
        let delta = match *self {
            Move::Constant { delta, .. } => delta,
            Move::Route {
                from,
                to,
                first,
                last,
                ..
            } => {
                if value == first {
                    from
                } else if value == last {
                    to
                } else {
                    0
                }
            }
        };
        narrow(checked_add(i64::from(value), delta)?)
    }
    fn point(&self, point: &mut Point) -> Result<(), LayoutError> {
        let axis = match *self {
            Move::Constant { axis, .. } | Move::Route { axis, .. } => axis,
        };
        let moved = self.value(axis.value(*point))?;
        *point = axis.with(*point, moved);
        Ok(())
    }
    fn rect(&self, rect: &mut Rect) -> Result<(), LayoutError> {
        let axis = match *self {
            Move::Constant { axis, .. } | Move::Route { axis, .. } => axis,
        };
        let moved = self.value(axis.start(*rect))?;
        axis.set_start(rect, moved);
        Ok(())
    }
    fn item(&self, item: &mut Item) -> Result<(), LayoutError> {
        match item {
            Item::Rect(shape) => self.rect(&mut shape.rect),
            Item::RoundRect(shape) => self.rect(&mut shape.rect),
            Item::Text(shape) => self.rect(&mut shape.rect),
            Item::Ellipse(shape) => {
                let mut centre = Point {
                    x: shape.cx,
                    y: shape.cy,
                };
                self.point(&mut centre)?;
                shape.cx = centre.x;
                shape.cy = centre.y;
                Ok(())
            }
            Item::Polygon(shape) => {
                for point in &mut shape.points {
                    self.point(point)?;
                }
                Ok(())
            }
            Item::Polyline(shape) => {
                for point in &mut shape.points {
                    self.point(point)?;
                }
                Ok(())
            }
            Item::Path(shape) => {
                for command in &mut shape.commands {
                    self.command(command)?;
                }
                Ok(())
            }
            Item::MarkerRef(shape) => self.point(&mut shape.at),
            Item::SymbolRef(shape) => self.point(&mut shape.at),
        }
    }
    fn command(&self, command: &mut PathCommand) -> Result<(), LayoutError> {
        match command {
            PathCommand::Move(point) | PathCommand::Line(point) => self.point(point),
            PathCommand::Curve { c1, c2, to } => {
                self.point(c1)?;
                self.point(c2)?;
                self.point(to)
            }
            PathCommand::Arc { centre, .. } => self.point(centre),
            PathCommand::Close => Ok(()),
        }
    }
}

fn lane_of<'a>(input: &'a Input, id: &'a str) -> Option<&'a str> {
    let mut current = id;
    loop {
        let boxed = input.boxes.iter().find(|boxed| boxed.id == current)?;
        if boxed.parent.is_empty() {
            return (boxed.role == BoxRole::Group).then_some(current);
        }
        current = boxed.parent.as_str();
    }
}

fn pin_bands(input: &Input, scene: Scene) -> Result<Scene, LayoutError> {
    let axis = cross_axis(input.direction);
    let title = i64::from(constant(input.profile, "line_h")?);
    let clear = i64::from(constant(input.profile, "cluster_pad")?)
        .checked_add(i64::from(constant(input.profile, "slot")?))
        .ok_or(LayoutError::Overflow)?;
    let lanes: Vec<&str> = input
        .groups
        .iter()
        .filter(|group| group.parent.is_empty())
        .map(|group| group.id.as_str())
        .collect();
    if lanes.is_empty() {
        return Ok(scene);
    }
    let mut start: i64 = lanes
        .iter()
        .filter_map(|lane| {
            scene
                .boxes()
                .iter()
                .find(|boxed| &boxed.id == lane)
                .map(|boxed| i64::from(axis.start(boxed.rect)))
        })
        .min()
        .unwrap_or(0);
    let mut bands = Vec::new();
    for lane in lanes {
        let members: Vec<String> = input
            .boxes
            .iter()
            .filter(|boxed| lane_of(input, &boxed.id) == Some(lane))
            .map(|boxed| boxed.id.clone())
            .collect();
        let mut band = Band {
            id: lane.to_owned(),
            members,
            shift: 0,
            start,
            thickness: 0,
        };
        let content = content_extent(scene.boxes(), scene.routes(), &band, axis, input)?;
        let (lo, hi) = content.unwrap_or((start, start));
        band.thickness = checked_add(checked_add(title, 2 * clear)?, checked_add(hi, -lo)?)?;
        band.shift = checked_add(checked_add(start, title)?, clear)?
            .checked_sub(lo)
            .ok_or(LayoutError::Overflow)?;
        start = checked_add(start, band.thickness)?;
        bands.push(band);
    }
    let loose: Vec<String> = input
        .boxes
        .iter()
        .filter(|boxed| boxed.parent.is_empty() && boxed.role == BoxRole::Node)
        .map(|boxed| boxed.id.clone())
        .collect();
    if !loose.is_empty() {
        let mut band = Band {
            id: String::new(),
            members: loose,
            shift: 0,
            start,
            thickness: 0,
        };
        if let Some((lo, hi)) = content_extent(scene.boxes(), scene.routes(), &band, axis, input)? {
            band.thickness = checked_add(hi, -lo)?;
            band.shift = checked_add(start, clear)?
                .checked_sub(lo)
                .ok_or(LayoutError::Overflow)?;
        }
        bands.push(band);
    }
    let frames = ends::lane_frames(axis, &bands, scene.boxes());
    let pin = build_pin(axis, &bands, &scene);
    let original: Vec<Vec<Point>> = scene.routes().iter().map(|r| r.points.clone()).collect();
    let mut dump = scene.dump_part().clone();
    let mut items = scene.items().to_vec();
    apply_pin(&mut dump, &mut items, &pin, &bands)?;
    routing::Router {
        axis,
        slot: i64::from(constant(input.profile, "slot")?),
        bend: i64::from(constant(input.profile, "rank_gap")?),
    }
    .run(&mut dump, &mut items, (&bands, &original))?;
    let origin = origin_min(&dump, &items, axis).unwrap_or(0);
    if origin < 0 {
        apply_extra(&mut dump, &mut items, axis, -i64::from(origin))?;
    }
    relocate_labels(&mut dump, &mut items, axis, input.profile)?;
    let mut canvas = scene.canvas();
    let extent = geometry_max(&dump, &items, axis)?;
    canvas = match axis {
        Axis::X => Size {
            w: canvas.w.max(narrow(extent)?),
            h: canvas.h,
        },
        Axis::Y => Size {
            w: canvas.w,
            h: canvas.h.max(narrow(extent)?),
        },
    };
    ends::attach_lane_ends(&mut dump, &mut items, axis, &frames)?;
    Ok(Scene::new(canvas, dump, items))
}

fn content_extent(
    boxes: &[scene::SceneBox],
    routes: &[scene::SceneRoute],
    band: &Band,
    axis: Axis,
    input: &Input,
) -> Result<Option<(i64, i64)>, LayoutError> {
    let lane = band.id.as_str();
    let mut extent: Option<(i64, i64)> = None;
    let mut extend = |value: i64| {
        extent = Some(match extent {
            None => (value, value),
            Some((lo, hi)) => (lo.min(value), hi.max(value)),
        });
    };
    for member in &band.members {
        if let Some(boxed) = boxes.iter().find(|boxed| &boxed.id == member) {
            extend(i64::from(axis.start(boxed.rect)));
            extend(i64::from(axis.start(boxed.rect)) + i64::from(axis.len(boxed.rect)));
        }
    }
    for route in routes {
        let inside =
            lane_of(input, &route.from) == Some(lane) && lane_of(input, &route.to) == Some(lane);
        if inside {
            for point in &route.points {
                extend(i64::from(axis.value(*point)));
            }
        }
    }
    Ok(extent)
}

fn build_pin(axis: Axis, bands: &[Band], scene: &Scene) -> Pin {
    let boxes = bands
        .iter()
        .flat_map(|band| {
            std::iter::once((band.id.clone(), band.shift)).chain(
                band.members
                    .iter()
                    .map(|member| (member.clone(), band.shift)),
            )
        })
        .collect();
    let routes = scene
        .routes()
        .iter()
        .filter_map(|route| {
            let from = band_delta(bands, &route.from);
            let to = band_delta(bands, &route.to);
            let first = route.points.first().map(|point| axis.value(*point))?;
            let last = route.points.last().map(|point| axis.value(*point))?;
            Some((route.id.clone(), from, to, first, last))
        })
        .collect();
    Pin {
        axis,
        boxes,
        routes,
    }
}

fn band_delta(bands: &[Band], id: &str) -> i64 {
    bands
        .iter()
        .find(|band| band.id == id || band.members.iter().any(|member| member == id))
        .map_or(0, |band| band.shift)
}

fn apply_pin(
    dump: &mut scene::Dump,
    items: &mut [scene::Group],
    pin: &Pin,
    bands: &[Band],
) -> Result<(), LayoutError> {
    move_dump(dump, pin)?;
    for group in items.iter_mut() {
        move_group(group, pin)?;
    }
    for band in bands {
        replace_frame(dump, items, band, pin.axis)?;
    }
    Ok(())
}

/// Shifts every geometry coordinate on the cross axis by `delta`, keeping the layout
/// origin at zero after a band shift moved content into negative coordinates.
fn apply_extra(
    dump: &mut scene::Dump,
    items: &mut [scene::Group],
    axis: Axis,
    delta: i64,
) -> Result<(), LayoutError> {
    for boxed in &mut dump.boxes {
        shift_rect_by(&mut boxed.rect, axis, delta)?;
    }
    for label in &mut dump.labels {
        shift_rect_by(&mut label.rect, axis, delta)?;
    }
    let move_ = Move::Constant { axis, delta };
    for route in &mut dump.routes {
        for point in &mut route.points {
            move_.point(point)?;
        }
    }
    for group in items.iter_mut() {
        for item in &mut group.items {
            move_.item(item)?;
        }
    }
    Ok(())
}

fn move_dump(dump: &mut scene::Dump, pin: &Pin) -> Result<(), LayoutError> {
    for boxed in &mut dump.boxes {
        shift_rect_by(&mut boxed.rect, pin.axis, pin.box_delta(&boxed.id))?;
    }
    for label in &mut dump.labels {
        shift_rect_by(&mut label.rect, pin.axis, pin.label_delta(&label.owner))?;
    }
    for route in &mut dump.routes {
        let Some((from, to, first, last)) = pin.route(&route.id) else {
            continue;
        };
        let move_ = if from == to {
            Move::Constant {
                axis: pin.axis,
                delta: from,
            }
        } else {
            Move::Route {
                axis: pin.axis,
                from,
                to,
                first,
                last,
            }
        };
        for point in &mut route.points {
            move_.point(point)?;
        }
    }
    Ok(())
}

fn shift_rect_by(rect: &mut Rect, axis: Axis, delta: i64) -> Result<(), LayoutError> {
    let moved = narrow(checked_add(i64::from(axis.start(*rect)), delta)?)?;
    axis.set_start(rect, moved);
    Ok(())
}

fn meets_interior(outer: &Rect, inner: &Rect) -> bool {
    i64::from(outer.x).max(i64::from(inner.x))
        < i64::from(outer.x + outer.w).min(i64::from(inner.x + inner.w))
        && i64::from(outer.y).max(i64::from(inner.y))
            < i64::from(outer.y + outer.h).min(i64::from(inner.y + inner.h))
}

fn strictly_inside(outer: &Rect, inner: &Rect) -> bool {
    i64::from(outer.x) < i64::from(inner.x)
        && i64::from(inner.x + inner.w) < i64::from(outer.x + outer.w)
        && i64::from(outer.y) < i64::from(inner.y)
        && i64::from(inner.y + inner.h) < i64::from(outer.y + outer.h)
}

/// The ancestors of a label's owner: the owner box's ancestors for a box label, and
/// the union of the route endpoints' ancestors for a route label.
fn label_owner_scope(
    label: &scene::SceneLabel,
    routes: &std::collections::BTreeMap<&str, (&str, &str)>,
    ancestors: &impl Fn(&str) -> std::collections::BTreeSet<String>,
) -> std::collections::BTreeSet<String> {
    match routes.get(label.owner.as_str()) {
        Some(&(from, to)) => {
            let mut scope = ancestors(from);
            scope.extend(ancestors(to));
            scope
        }
        None => ancestors(&label.owner),
    }
}

fn label_overlaps_frame(frame: &scene::SceneBox, label: &scene::SceneLabel) -> bool {
    frame.role == scene::BoxRole::Group
        && meets_interior(&frame.rect, &label.rect)
        && !strictly_inside(&frame.rect, &label.rect)
}

fn label_hits_unrelated_node(
    boxed: &scene::SceneBox,
    label: &scene::SceneLabel,
    scope: &std::collections::BTreeSet<String>,
) -> bool {
    boxed.exclusive
        && boxed.id != label.owner
        && !scope.contains(boxed.id.as_str())
        && meets_interior(&boxed.rect, &label.rect)
}

/// True when a band pin left `label` overlapping a foreign frame interior or an
/// unrelated exclusive node.
fn label_needs_relocation(
    label: &scene::SceneLabel,
    dump: &scene::Dump,
    routes: &std::collections::BTreeMap<&str, (&str, &str)>,
    ancestors: &impl Fn(&str) -> std::collections::BTreeSet<String>,
) -> bool {
    let scope = label_owner_scope(label, routes, ancestors);
    dump.boxes.iter().any(|boxed| {
        label_overlaps_frame(boxed, label) || label_hits_unrelated_node(boxed, label, &scope)
    })
}

/// Moves labels that a band pin left overlapping a foreign frame interior or an
/// unrelated exclusive node to the strip beyond the band stack. Lane bands tile the
/// cross axis with no gap, so a cross-lane route label has no legal position inside
/// the stack; beyond the stack it is disjoint from every frame and every node.
fn relocate_labels(
    dump: &mut scene::Dump,
    items: &mut [scene::Group],
    axis: Axis,
    profile: Profile,
) -> Result<(), LayoutError> {
    let gap = i64::from(constant(profile, "slot")?);
    let strip = narrow(checked_add(geometry_max(dump, items, axis)?, gap)?)?;
    let mut moves: Vec<Rect> = Vec::new();
    let offenders: Vec<usize> = {
        let parents: std::collections::BTreeMap<&str, &str> = dump
            .boxes
            .iter()
            .map(|boxed| (boxed.id.as_str(), boxed.parent.as_str()))
            .collect();
        let ancestors = |id: &str| {
            let mut out = std::collections::BTreeSet::new();
            let mut current = parents.get(id).copied();
            while let Some(parent) = current {
                out.insert(parent.to_owned());
                current = parents.get(parent).copied();
            }
            out
        };
        let routes: std::collections::BTreeMap<&str, (&str, &str)> = dump
            .routes
            .iter()
            .map(|route| (route.id.as_str(), (route.from.as_str(), route.to.as_str())))
            .collect();
        (0..dump.labels.len())
            .filter(|index| label_needs_relocation(&dump.labels[*index], dump, &routes, &ancestors))
            .collect()
    };
    for index in offenders {
        let label = &mut dump.labels[index];
        moves.push(label.rect);
        axis.set_start(&mut label.rect, strip);
    }
    if moves.is_empty() {
        return Ok(());
    }
    for group in items.iter_mut() {
        for item in &mut group.items {
            if let Item::Text(text) = item
                && moves.contains(&text.rect)
            {
                axis.set_start(&mut text.rect, strip);
            }
        }
    }
    Ok(())
}

fn move_group(group: &mut scene::Group, pin: &Pin) -> Result<(), LayoutError> {
    let move_ = match group.role {
        GroupRole::Edge => {
            let route = pin.route(&group.owner).unwrap_or((0, 0, 0, 0));
            let (from, to, first, last) = route;
            if from == to {
                Move::Constant {
                    axis: pin.axis,
                    delta: from,
                }
            } else {
                Move::Route {
                    axis: pin.axis,
                    from,
                    to,
                    first,
                    last,
                }
            }
        }
        GroupRole::Node | GroupRole::Group | GroupRole::Decor => Move::Constant {
            axis: pin.axis,
            delta: pin.box_delta(&group.owner),
        },
    };
    for item in &mut group.items {
        move_.item(item)?;
    }
    Ok(())
}

fn replace_frame(
    dump: &mut scene::Dump,
    items: &mut [scene::Group],
    band: &Band,
    axis: Axis,
) -> Result<(), LayoutError> {
    let Some(boxed) = dump.boxes.iter_mut().find(|boxed| boxed.id == band.id) else {
        return Ok(());
    };
    axis.set_start(&mut boxed.rect, narrow(band.start)?);
    axis.set_len(&mut boxed.rect, narrow(band.thickness)?);
    let Some(group) = items.iter_mut().find(|group| group.owner == band.id) else {
        return Ok(());
    };
    for item in &mut group.items {
        if let Item::Rect(shape) = item {
            axis.set_start(&mut shape.rect, narrow(band.start)?);
            axis.set_len(&mut shape.rect, narrow(band.thickness)?);
        }
    }
    Ok(())
}

fn origin_min(dump: &scene::Dump, items: &[scene::Group], axis: Axis) -> Option<i32> {
    let mut min: Option<i32> = None;
    let mut see = |value: i32| min = Some(min.map_or(value, |current| current.min(value)));
    for boxed in &dump.boxes {
        see(axis.start(boxed.rect));
    }
    for route in &dump.routes {
        for point in &route.points {
            see(axis.value(*point));
        }
    }
    for label in &dump.labels {
        see(axis.start(label.rect));
    }
    for group in items {
        for item in &group.items {
            visit_item(item, axis, &mut see);
        }
    }
    min
}

fn geometry_max(
    dump: &scene::Dump,
    items: &[scene::Group],
    axis: Axis,
) -> Result<i64, LayoutError> {
    let mut max: i64 = 0;
    let mut raise = |value: i32| max = max.max(i64::from(value));
    for boxed in &dump.boxes {
        raise(axis.start(boxed.rect) + axis.len(boxed.rect));
    }
    for route in &dump.routes {
        for point in &route.points {
            raise(axis.value(*point));
        }
    }
    for label in &dump.labels {
        raise(axis.start(label.rect) + axis.len(label.rect));
    }
    for group in items {
        for item in &group.items {
            visit_item(item, axis, &mut raise);
        }
    }
    Ok(max)
}

fn visit_item(item: &Item, axis: Axis, see: &mut impl FnMut(i32)) {
    match item {
        Item::Rect(shape) => see_rect(see, axis, &shape.rect),
        Item::RoundRect(shape) => see_rect(see, axis, &shape.rect),
        Item::Text(shape) => see_rect(see, axis, &shape.rect),
        Item::Ellipse(shape) => see_point(
            see,
            axis,
            &Point {
                x: shape.cx,
                y: shape.cy,
            },
        ),
        Item::Polygon(shape) => {
            for p in &shape.points {
                see_point(see, axis, p);
            }
        }
        Item::Polyline(shape) => {
            for p in &shape.points {
                see_point(see, axis, p);
            }
        }
        Item::Path(shape) => {
            for command in &shape.commands {
                visit_command(command, axis, see);
            }
        }
        Item::MarkerRef(shape) => see_point(see, axis, &shape.at),
        Item::SymbolRef(shape) => see_point(see, axis, &shape.at),
    }
}

fn see_point(see: &mut impl FnMut(i32), axis: Axis, point: &Point) {
    see(axis.value(*point));
}

fn see_rect(see: &mut impl FnMut(i32), axis: Axis, rect: &Rect) {
    see(axis.start(*rect));
    see(axis.start(*rect) + axis.len(*rect));
}

fn visit_command(command: &PathCommand, axis: Axis, see: &mut impl FnMut(i32)) {
    match command {
        PathCommand::Move(point) | PathCommand::Line(point) => see_point(see, axis, point),
        PathCommand::Curve { c1, c2, to } => {
            see_point(see, axis, c1);
            see_point(see, axis, c2);
            see_point(see, axis, to);
        }
        PathCommand::Arc { centre, .. } => see_point(see, axis, centre),
        PathCommand::Close => {}
    }
}
