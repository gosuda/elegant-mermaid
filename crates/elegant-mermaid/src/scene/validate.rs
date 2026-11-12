//! The layout validator of `spec/layout-dump.md`: `WellFormed`, the ancestor and scope
//! relations, and the seven hard-constraint clauses in their fixed order.
//!
//! A reader checks [`well_formed`] before it validates. Under a well-formed dump every
//! `crate::geom` operation this module calls succeeds, so [`check`] and [`validate`] return
//! an error only for input that skipped the check.

use std::collections::BTreeSet;
use std::fmt;

use crate::geom::{
    COORD_LIMIT, GeomError, I32_MAX, I32_MIN, Point, Rect, Size, contains, intersects,
    is_orthogonal, polyline_hits_rect,
};

use super::{Dump, SceneBox, SceneLabel, SceneRoute};

/// The clause of `spec/layout-dump.md` that a dump violates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Clause {
    /// Every box rect is contained in the canvas.
    Canvas,
    /// Exclusive boxes with one parent are disjoint.
    ExclusiveSiblings,
    /// A box with a parent lies inside that parent.
    Parent,
    /// Every orthogonal route is orthogonal.
    Orthogonal,
    /// Every route end lies on its box boundary.
    Ports,
    /// No route reaches an exclusive box outside its scope.
    RouteClearance,
    /// No label overlaps an exclusive box outside its owner's ancestors.
    LabelClearance,
}

/// The seven clauses in their fixed order.
pub const CLAUSES: [Clause; 7] = [
    Clause::Canvas,
    Clause::ExclusiveSiblings,
    Clause::Parent,
    Clause::Orthogonal,
    Clause::Ports,
    Clause::RouteClearance,
    Clause::LabelClearance,
];

impl Clause {
    /// The fixed clause id of `spec/layout-dump.md`.
    pub const fn id(self) -> &'static str {
        match self {
            Clause::Canvas => "canvas",
            Clause::ExclusiveSiblings => "exclusive-siblings",
            Clause::Parent => "parent",
            Clause::Orthogonal => "orthogonal",
            Clause::Ports => "ports",
            Clause::RouteClearance => "route-clearance",
            Clause::LabelClearance => "label-clearance",
        }
    }

    /// The fixed clause message of `spec/layout-dump.md`.
    pub const fn message(self) -> &'static str {
        match self {
            Clause::Canvas => "box outside canvas",
            Clause::ExclusiveSiblings => "exclusive sibling boxes overlap",
            Clause::Parent => "box outside its parent",
            Clause::Orthogonal => "orthogonal route has a diagonal segment",
            Clause::Ports => "route end is off its box boundary",
            Clause::RouteClearance => "route crosses an exclusive box",
            Clause::LabelClearance => "label overlaps an exclusive box",
        }
    }

    /// The line that `geomcheck validate` prints, `invalid <clause-id>: <message>`.
    pub fn report(self) -> String {
        format!("invalid {}: {}", self.id(), self.message())
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}

/// A dump that fails `WellFormed`. `geomcheck validate` prints `malformed dump: REASON` and
/// exits 2.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum Malformed {
    /// A box id appears twice.
    #[error("box id {0} appears twice")]
    DuplicateBox(String),
    /// A route id appears twice.
    #[error("route id {0} appears twice")]
    DuplicateRoute(String),
    /// A label id appears twice.
    #[error("label id {0} appears twice")]
    DuplicateLabel(String),
    /// A route names a box that the dump does not hold.
    #[error("route {route} names unknown box {id}")]
    UnknownRouteEnd {
        /// The route id.
        route: String,
        /// The box id the route names.
        id: String,
    },
    /// A label names an owner that the dump holds neither as a box nor as a route.
    #[error("label {label} has unknown owner {owner}")]
    UnknownOwner {
        /// The label id.
        label: String,
        /// The owner id the label names.
        owner: String,
    },
    /// A box names a parent that the dump does not hold.
    #[error("box {bbox} has unknown parent {parent}")]
    UnknownParent {
        /// The box id.
        bbox: String,
        /// The parent id the box names.
        parent: String,
    },
    /// A parent chain returns to its own box.
    #[error("box {0} is its own ancestor")]
    ParentCycle(String),
    /// A rectangle is invalid: a negative width or height, or a rect edge outside `int32`.
    #[error("{0} has an invalid rectangle")]
    InvalidRect(String),
    /// A coordinate, a point, or a rectangle edge lies beyond the coordinate limit.
    #[error("{0} has a coordinate beyond the limit")]
    Coordinate(String),
}

/// The ancestor and identity relations of one dump, computed once for the clauses.
struct Index<'a> {
    boxes: &'a [SceneBox],
    routes: &'a [SceneRoute],
}

impl<'a> Index<'a> {
    fn new(dump: &'a Dump) -> Index<'a> {
        Index {
            boxes: &dump.boxes,
            routes: &dump.routes,
        }
    }

    fn bbox(&self, id: &str) -> Option<&'a SceneBox> {
        self.boxes.iter().find(|b| b.id == id)
    }

    fn route(&self, id: &str) -> Option<&'a SceneRoute> {
        self.routes.iter().find(|r| r.id == id)
    }

    /// The proper ancestors of a box, found by following `parent`. The walk takes at most
    /// one step per box, so a parent chain that returns to its own box still terminates.
    fn ancestors(&self, id: &str) -> Vec<&'a str> {
        std::iter::successors(self.bbox(id).map(|b| b.parent.as_str()), |cursor| {
            self.bbox(cursor).map(|b| b.parent.as_str())
        })
        .filter(|parent| !parent.is_empty())
        .take(self.boxes.len())
        .collect()
    }

    /// The scope of a route: both endpoints and their ancestors.
    fn scope(&self, route: &'a SceneRoute) -> BTreeSet<&'a str> {
        let mut ids: BTreeSet<&'a str> = self.ancestors(&route.from).into_iter().collect();
        ids.extend(self.ancestors(&route.to));
        ids.insert(&route.from);
        ids.insert(&route.to);
        ids
    }

    /// The ancestors of a label's owner, which the dump holds as a route or as a box.
    fn owner_ancestors(&self, owner: &str) -> BTreeSet<&'a str> {
        match self.route(owner) {
            Some(route) => {
                let mut ids: BTreeSet<&'a str> = self.ancestors(&route.from).into_iter().collect();
                ids.extend(self.ancestors(&route.to));
                ids
            }
            None => self.ancestors(owner).into_iter().collect(),
        }
    }
}

/// `on_boundary(p, r)`: `p` lies in the closed `r` and on one of its four sides.
fn on_boundary(p: Point, r: Rect) -> bool {
    let x0 = i64::from(r.x);
    let y0 = i64::from(r.y);
    let x1 = x0 + i64::from(r.w);
    let y1 = y0 + i64::from(r.h);
    let x = i64::from(p.x);
    let y = i64::from(p.y);
    x >= x0 && x <= x1 && y >= y0 && y <= y1 && (x == x0 || x == x1 || y == y0 || y == y1)
}

/// `p` lies within `+/-COORD_LIMIT` on both axes.
fn point_within_limit(p: Point) -> bool {
    i64::from(p.x).abs() <= COORD_LIMIT && i64::from(p.y).abs() <= COORD_LIMIT
}

/// A rectangle whose width and height are at least 0 and whose edges fit in `int32`.
fn rect_is_valid(r: Rect) -> bool {
    let x = i64::from(r.x);
    let y = i64::from(r.y);
    let w = i64::from(r.w);
    let h = i64::from(r.h);
    w >= 0 && h >= 0 && x + w >= I32_MIN && x + w <= I32_MAX && y + h >= I32_MIN && y + h <= I32_MAX
}

/// The rectangle's four coordinates lie within `+/-COORD_LIMIT`.
fn rect_within_limit(r: Rect) -> bool {
    let x = i64::from(r.x);
    let y = i64::from(r.y);
    [x, y, x + i64::from(r.w), y + i64::from(r.h)]
        .iter()
        .all(|value| value.abs() <= COORD_LIMIT)
}

/// Checks `WellFormed` of `spec/layout-dump.md`. Every reason names the member that fails,
/// so `geomcheck validate` can print `malformed dump: REASON`.
pub fn well_formed(canvas: Size, dump: &Dump) -> Result<(), Malformed> {
    check_canvas(canvas)?;
    check_unique(dump)?;
    check_relations(dump)?;
    check_boxes(&dump.boxes)?;
    dump.labels
        .iter()
        .try_for_each(|label| check_rect("label", &label.id, label.rect))?;
    dump.routes
        .iter()
        .try_for_each(|route| check_points(&route.id, &route.points))
}

fn check_unique(dump: &Dump) -> Result<(), Malformed> {
    let mut boxes: BTreeSet<&str> = BTreeSet::new();
    for b in &dump.boxes {
        if !boxes.insert(b.id.as_str()) {
            return Err(Malformed::DuplicateBox(b.id.clone()));
        }
    }
    let mut routes: BTreeSet<&str> = BTreeSet::new();
    for r in &dump.routes {
        if !routes.insert(r.id.as_str()) {
            return Err(Malformed::DuplicateRoute(r.id.clone()));
        }
    }
    let mut labels: BTreeSet<&str> = BTreeSet::new();
    for l in &dump.labels {
        if !labels.insert(l.id.as_str()) {
            return Err(Malformed::DuplicateLabel(l.id.clone()));
        }
    }
    Ok(())
}

fn check_relations(dump: &Dump) -> Result<(), Malformed> {
    let index = Index::new(dump);
    for route in &dump.routes {
        for id in [&route.from, &route.to] {
            if index.bbox(id).is_none() {
                return Err(Malformed::UnknownRouteEnd {
                    route: route.id.clone(),
                    id: id.clone(),
                });
            }
        }
    }
    for label in &dump.labels {
        if index.bbox(&label.owner).is_none() && index.route(&label.owner).is_none() {
            return Err(Malformed::UnknownOwner {
                label: label.id.clone(),
                owner: label.owner.clone(),
            });
        }
    }
    for b in &dump.boxes {
        if b.parent.is_empty() {
            continue;
        }
        if index.bbox(&b.parent).is_none() {
            return Err(Malformed::UnknownParent {
                bbox: b.id.clone(),
                parent: b.parent.clone(),
            });
        }
        if index.ancestors(&b.id).contains(&b.id.as_str()) {
            return Err(Malformed::ParentCycle(b.id.clone()));
        }
    }
    Ok(())
}

fn check_canvas(canvas: Size) -> Result<(), Malformed> {
    check_rect(
        "canvas",
        "",
        Rect {
            x: 0,
            y: 0,
            w: canvas.w,
            h: canvas.h,
        },
    )
}

fn check_boxes(boxes: &[SceneBox]) -> Result<(), Malformed> {
    boxes
        .iter()
        .try_for_each(|b| check_rect("box", &b.id, b.rect))
}

fn check_rect(kind: &str, id: &str, r: Rect) -> Result<(), Malformed> {
    let named = format!("{kind} {id}");
    if !rect_is_valid(r) {
        return Err(Malformed::InvalidRect(named));
    }
    if !rect_within_limit(r) {
        return Err(Malformed::Coordinate(named));
    }
    Ok(())
}

fn check_points(id: &str, points: &[Point]) -> Result<(), Malformed> {
    match points.iter().find(|p| !point_within_limit(**p)) {
        None => Ok(()),
        Some(_) => Err(Malformed::Coordinate(format!("route {id}"))),
    }
}

/// Clause `canvas`: every box rect is contained in `(0, 0, canvas.w, canvas.h)`.
fn canvas_holds(canvas: Rect, dump: &Dump) -> Result<bool, GeomError> {
    for b in &dump.boxes {
        if !contains(canvas, b.rect)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Clause `exclusive-siblings`: exclusive boxes with one parent are disjoint.
fn exclusive_siblings_hold(dump: &Dump) -> Result<bool, GeomError> {
    for (position, b) in dump.boxes.iter().enumerate().filter(|(_, b)| b.exclusive) {
        for c in dump.boxes.iter().skip(position + 1) {
            if c.exclusive && c.parent == b.parent && intersects(b.rect, c.rect)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// Clause `parent`: a box with a parent lies inside that parent.
fn parent_holds(index: &Index<'_>) -> Result<bool, GeomError> {
    let children = index.boxes.iter().filter(|b| !b.parent.is_empty());
    for b in children {
        let Some(parent) = index.bbox(&b.parent) else {
            continue;
        };
        if !contains(parent.rect, b.rect)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Clause `orthogonal`: every orthogonal route is orthogonal.
fn orthogonal_holds(dump: &Dump) -> bool {
    dump.routes
        .iter()
        .all(|r| !r.orthogonal || is_orthogonal(&r.points))
}

/// Clause `ports`: every route has a point, and its ends lie on the boundaries of its
/// boxes.
fn ports_hold(index: &Index<'_>) -> bool {
    index.routes.iter().all(|route| {
        let (Some(first), Some(last)) = (route.points.first(), route.points.last()) else {
            return false;
        };
        let (Some(from), Some(to)) = (index.bbox(&route.from), index.bbox(&route.to)) else {
            return false;
        };
        on_boundary(*first, from.rect) && on_boundary(*last, to.rect)
    })
}

/// Clause `route-clearance`: no route reaches an exclusive box outside its scope.
fn route_clearance_holds(index: &Index<'_>) -> Result<bool, GeomError> {
    for route in index.routes {
        let scope = index.scope(route);
        let boxes = index
            .boxes
            .iter()
            .filter(|b| b.exclusive && !scope.contains(b.id.as_str()));
        for b in boxes {
            if polyline_hits_rect(&route.points, b.rect)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// Clause `label-clearance`: no label overlaps an exclusive box outside its owner's
/// ancestors.
fn label_clearance_holds(index: &Index<'_>, labels: &[SceneLabel]) -> Result<bool, GeomError> {
    for label in labels {
        let allowed = index.owner_ancestors(&label.owner);
        let boxes = index
            .boxes
            .iter()
            .filter(|b| b.exclusive && !allowed.contains(b.id.as_str()));
        for b in boxes {
            if intersects(label.rect, b.rect)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// The first clause that fails, in the fixed clause order of `spec/layout-dump.md`, or
/// `None` when every clause holds.
pub fn validate(canvas: Size, dump: &Dump) -> Result<Option<Clause>, GeomError> {
    well_formed(canvas, dump).map_err(|_| GeomError::Domain)?;
    let index = Index::new(dump);
    let canvas = Rect {
        x: 0,
        y: 0,
        w: canvas.w,
        h: canvas.h,
    };
    if !canvas_holds(canvas, dump)? {
        return Ok(Some(Clause::Canvas));
    }
    if !exclusive_siblings_hold(dump)? {
        return Ok(Some(Clause::ExclusiveSiblings));
    }
    if !parent_holds(&index)? {
        return Ok(Some(Clause::Parent));
    }
    if !orthogonal_holds(dump) {
        return Ok(Some(Clause::Orthogonal));
    }
    if !ports_hold(&index) {
        return Ok(Some(Clause::Ports));
    }
    if !route_clearance_holds(&index)? {
        return Ok(Some(Clause::RouteClearance));
    }
    if !label_clearance_holds(&index, &dump.labels)? {
        return Ok(Some(Clause::LabelClearance));
    }
    Ok(None)
}

/// True exactly when no clause fails.
pub fn check(canvas: Size, dump: &Dump) -> Result<bool, GeomError> {
    Ok(validate(canvas, dump)?.is_none())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geom::Size;
    use crate::scene::{BoxRole, Dump, DumpOptions, SceneBox, SceneLabel, SceneRoute};

    fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect { x, y, w, h }
    }

    fn point(x: i32, y: i32) -> Point {
        Point { x, y }
    }

    fn bbox(id: &str, r: Rect) -> SceneBox {
        SceneBox {
            id: id.to_owned(),
            role: BoxRole::Node,
            rect: r,
            parent: String::new(),
            exclusive: true,
        }
    }

    fn route(id: &str, from: &str, to: &str, points: Vec<Point>) -> SceneRoute {
        SceneRoute {
            id: id.to_owned(),
            from: from.to_owned(),
            to: to.to_owned(),
            orthogonal: true,
            points,
        }
    }

    fn label(id: &str, owner: &str, r: Rect) -> SceneLabel {
        SceneLabel {
            id: id.to_owned(),
            owner: owner.to_owned(),
            text: String::from("x"),
            rect: r,
            lines: vec![String::from("x")],
        }
    }

    fn canvas() -> Size {
        Size { w: 100, h: 100 }
    }

    /// Two disjoint nodes, one route between them, and one label in the gap.
    fn valid_dump() -> Dump {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        dump.boxes.push(bbox("A", rect(0, 0, 20, 20)));
        dump.boxes.push(bbox("B", rect(0, 60, 20, 20)));
        dump.routes
            .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
        dump.labels
            .push(label("e0.label", "e0", rect(0, 30, 8, 10)));
        dump
    }

    fn failure(dump: &Dump) -> Option<Clause> {
        validate(canvas(), dump).unwrap_or(None)
    }

    fn malformed(dump: &Dump) -> Option<Malformed> {
        well_formed(canvas(), dump).err()
    }

    #[test]
    fn a_valid_dump_passes_every_clause() {
        let dump = valid_dump();
        assert_eq!(failure(&dump), None);
        assert!(check(canvas(), &dump).unwrap_or(false));
        assert_eq!(well_formed(canvas(), &dump), Ok(()));
    }

    #[test]
    fn clause_ids_and_messages_are_fixed_and_in_order() {
        let ids: Vec<&str> = CLAUSES.iter().map(|c| c.id()).collect();
        assert_eq!(
            ids,
            [
                "canvas",
                "exclusive-siblings",
                "parent",
                "orthogonal",
                "ports",
                "route-clearance",
                "label-clearance"
            ]
        );
        let messages: Vec<&str> = CLAUSES.iter().map(|c| c.message()).collect();
        assert_eq!(
            messages,
            [
                "box outside canvas",
                "exclusive sibling boxes overlap",
                "box outside its parent",
                "orthogonal route has a diagonal segment",
                "route end is off its box boundary",
                "route crosses an exclusive box",
                "label overlaps an exclusive box"
            ]
        );
        assert_eq!(
            Clause::Canvas.report(),
            "invalid canvas: box outside canvas"
        );
        assert_eq!(
            Clause::Ports.report(),
            "invalid ports: route end is off its box boundary"
        );
        assert_eq!(format!("{}", Clause::LabelClearance), "label-clearance");
    }

    #[test]
    fn clause_canvas_rejects_a_box_outside_the_canvas() {
        let mut dump = valid_dump();
        if let Some(b) = dump.boxes.get_mut(1) {
            b.rect = rect(0, 90, 20, 20);
        }
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![point(10, 20), point(10, 90)];
        }
        assert_eq!(failure(&dump), Some(Clause::Canvas));
    }

    #[test]
    fn clause_exclusive_siblings_rejects_overlapping_siblings() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("C", rect(10, 10, 20, 20)));
        assert_eq!(failure(&dump), Some(Clause::ExclusiveSiblings));
    }

    #[test]
    fn clause_exclusive_siblings_ignores_touching_boxes() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("C", rect(20, 0, 20, 20)));
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_exclusive_siblings_ignores_a_non_exclusive_box() {
        let mut dump = valid_dump();
        let mut shared = bbox("C", rect(10, 10, 20, 20));
        shared.exclusive = false;
        dump.boxes.push(shared);
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_exclusive_siblings_keeps_boxes_of_other_parents() {
        let mut dump = valid_dump();
        let mut frame = bbox("G", rect(0, 0, 40, 40));
        frame.role = BoxRole::Group;
        frame.exclusive = false;
        dump.boxes.push(frame);
        let mut other = bbox("C", rect(10, 10, 20, 20));
        other.parent = String::from("G");
        dump.boxes.push(other);
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_parent_rejects_a_box_outside_its_parent() {
        let mut dump = valid_dump();
        let mut frame = bbox("G", rect(0, 0, 40, 40));
        frame.role = BoxRole::Group;
        frame.exclusive = false;
        dump.boxes.push(frame);
        let mut child = bbox("C", rect(0, 0, 20, 20));
        child.parent = String::from("G");
        dump.boxes.push(child);
        assert_eq!(failure(&dump), None);
        if let Some(b) = dump.boxes.get_mut(2) {
            b.rect = rect(30, 30, 20, 20);
        }
        assert_eq!(failure(&dump), Some(Clause::Parent));
    }

    #[test]
    fn clause_orthogonal_rejects_a_diagonal_segment() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![point(10, 20), point(12, 60)];
        }
        assert_eq!(failure(&dump), Some(Clause::Orthogonal));
    }

    #[test]
    fn clause_orthogonal_passes_a_diagonal_route_that_is_not_marked() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.orthogonal = false;
            r.points = vec![point(10, 20), point(12, 60)];
        }
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_ports_rejects_a_route_end_off_the_boundary() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![point(10, 20), point(10, 55)];
        }
        assert_eq!(failure(&dump), Some(Clause::Ports));
    }

    #[test]
    fn clause_ports_rejects_an_endpoint_inside_the_box() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![point(10, 20), point(10, 50)];
        }
        assert_eq!(failure(&dump), Some(Clause::Ports));
    }

    #[test]
    fn clause_ports_rejects_a_route_without_points() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points = Vec::new();
        }
        assert_eq!(failure(&dump), Some(Clause::Ports));
    }

    #[test]
    fn clause_ports_accepts_a_corner_end() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.orthogonal = false;
            r.points = vec![point(0, 20), point(0, 60)];
        }
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_route_clearance_rejects_a_route_through_a_box() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("C", rect(0, 30, 20, 20)));
        assert_eq!(failure(&dump), Some(Clause::RouteClearance));
    }

    #[test]
    fn clause_route_clearance_ignores_a_box_in_the_scope() {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        let mut frame = bbox("G", rect(0, 0, 40, 100));
        frame.role = BoxRole::Group;
        dump.boxes.push(frame);
        let mut a = bbox("A", rect(0, 0, 20, 20));
        a.parent = String::from("G");
        dump.boxes.push(a);
        let mut b = bbox("B", rect(0, 60, 20, 20));
        b.parent = String::from("G");
        dump.boxes.push(b);
        dump.routes
            .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_route_clearance_ignores_a_zero_area_box() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("C", rect(0, 35, 0, 0)));
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_label_clearance_rejects_a_label_over_a_box() {
        let mut dump = valid_dump();
        if let Some(l) = dump.labels.first_mut() {
            l.rect = rect(10, 10, 8, 5);
        }
        assert_eq!(failure(&dump), Some(Clause::LabelClearance));
    }

    #[test]
    fn clause_label_clearance_ignores_a_group_in_the_owner_ancestors() {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        let mut frame = bbox("G", rect(0, 0, 40, 40));
        frame.role = BoxRole::Group;
        dump.boxes.push(frame);
        let mut a = bbox("A", rect(0, 0, 20, 20));
        a.parent = String::from("G");
        dump.boxes.push(a);
        dump.labels
            .push(label("G.title", "A", rect(25, 25, 10, 10)));
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_label_clearance_ignores_a_box_owner_ancestor() {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        let mut frame = bbox("G", rect(0, 0, 40, 40));
        frame.role = BoxRole::Group;
        dump.boxes.push(frame);
        let mut a = bbox("A", rect(0, 0, 20, 20));
        a.parent = String::from("G");
        dump.boxes.push(a);
        dump.labels
            .push(label("A.title", "A", rect(25, 25, 10, 10)));
        assert_eq!(failure(&dump), None);
    }

    #[test]
    fn clause_order_reports_the_earlier_clause_when_two_fail() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("C", rect(10, 10, 20, 20)));
        if let Some(l) = dump.labels.first_mut() {
            l.rect = rect(10, 10, 8, 5);
        }
        assert_eq!(failure(&dump), Some(Clause::ExclusiveSiblings));
        if let Some(b) = dump.boxes.get_mut(1) {
            b.rect = rect(0, 90, 20, 20);
        }
        assert_eq!(failure(&dump), Some(Clause::Canvas));
    }

    #[test]
    fn clause_order_reports_ports_before_route_clearance() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points = vec![point(10, 25), point(10, 55)];
        }
        assert_eq!(failure(&dump), Some(Clause::Ports));
    }

    #[test]
    fn malformed_rejects_a_duplicate_box_id() {
        let mut dump = valid_dump();
        dump.boxes.push(bbox("A", rect(40, 40, 10, 10)));
        assert_eq!(
            malformed(&dump),
            Some(Malformed::DuplicateBox(String::from("A")))
        );
    }

    #[test]
    fn malformed_rejects_a_duplicate_route_and_label_id() {
        let mut routes = valid_dump();
        routes
            .routes
            .push(route("e0", "A", "B", vec![point(10, 20), point(10, 60)]));
        assert_eq!(
            malformed(&routes),
            Some(Malformed::DuplicateRoute(String::from("e0")))
        );
        let mut labels = valid_dump();
        labels
            .labels
            .push(label("e0.label", "e0", rect(0, 40, 4, 4)));
        assert_eq!(
            malformed(&labels),
            Some(Malformed::DuplicateLabel(String::from("e0.label")))
        );
    }

    #[test]
    fn malformed_rejects_an_unknown_parent() {
        let mut dump = valid_dump();
        if let Some(b) = dump.boxes.first_mut() {
            b.parent = String::from("Z");
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::UnknownParent {
                bbox: String::from("A"),
                parent: String::from("Z"),
            })
        );
    }

    #[test]
    fn malformed_rejects_a_parent_cycle() {
        let mut dump = valid_dump();
        if let Some(a) = dump.boxes.first_mut() {
            a.parent = String::from("B");
        }
        if let Some(b) = dump.boxes.get_mut(1) {
            b.parent = String::from("A");
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::ParentCycle(String::from("A")))
        );
    }

    #[test]
    fn malformed_rejects_a_box_that_is_its_own_parent() {
        let mut dump = valid_dump();
        if let Some(a) = dump.boxes.first_mut() {
            a.parent = String::from("A");
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::ParentCycle(String::from("A")))
        );
    }

    #[test]
    fn malformed_rejects_an_unknown_route_end() {
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.to = String::from("Z");
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::UnknownRouteEnd {
                route: String::from("e0"),
                id: String::from("Z"),
            })
        );
    }

    #[test]
    fn malformed_rejects_an_unknown_owner() {
        let mut dump = valid_dump();
        if let Some(l) = dump.labels.first_mut() {
            l.owner = String::from("Z");
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::UnknownOwner {
                label: String::from("e0.label"),
                owner: String::from("Z"),
            })
        );
    }

    #[test]
    fn malformed_rejects_a_coordinate_beyond_the_limit() {
        let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
        let mut dump = valid_dump();
        if let Some(b) = dump.boxes.first_mut() {
            b.rect = rect(0, 0, limit + 1, 10);
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::Coordinate(String::from("box A")))
        );
    }

    #[test]
    fn malformed_rejects_a_route_point_beyond_the_limit() {
        let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
        let mut dump = valid_dump();
        if let Some(r) = dump.routes.first_mut() {
            r.points.push(point(limit + 1, 0));
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::Coordinate(String::from("route e0")))
        );
    }

    #[test]
    fn malformed_rejects_a_negative_width() {
        let mut dump = valid_dump();
        if let Some(b) = dump.boxes.first_mut() {
            b.rect = rect(0, 0, -1, 10);
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::InvalidRect(String::from("box A")))
        );
    }

    #[test]
    fn malformed_rejects_a_label_beyond_the_limit() {
        let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
        let mut dump = valid_dump();
        if let Some(l) = dump.labels.first_mut() {
            l.rect = rect(limit, 0, 4, 4);
        }
        assert_eq!(
            malformed(&dump),
            Some(Malformed::Coordinate(String::from("label e0.label")))
        );
    }

    #[test]
    fn malformed_reasons_carry_the_printed_prefix() {
        let mut bad = valid_dump();
        bad.boxes.push(bbox("A", rect(40, 40, 10, 10)));
        let reason = malformed(&bad).map(|m| format!("malformed dump: {m}"));
        assert_eq!(
            reason,
            Some(String::from("malformed dump: box id A appears twice"))
        );
    }

    #[test]
    fn ancestors_stop_on_a_parent_chain_that_returns() {
        let mut dump = valid_dump();
        if let Some(a) = dump.boxes.first_mut() {
            a.parent = String::from("B");
        }
        if let Some(b) = dump.boxes.get_mut(1) {
            b.parent = String::from("A");
        }
        let index = Index::new(&dump);
        let chain = index.ancestors("A");
        assert_eq!(chain.len(), dump.boxes.len());
    }

    #[test]
    fn scope_and_owner_ancestors_follow_the_relations() {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        let mut outer = bbox("O", rect(0, 0, 100, 100));
        outer.role = BoxRole::Group;
        outer.exclusive = false;
        dump.boxes.push(outer);
        let mut inner = bbox("I", rect(0, 0, 50, 50));
        inner.role = BoxRole::Group;
        inner.parent = String::from("O");
        inner.exclusive = false;
        dump.boxes.push(inner);
        let mut a = bbox("A", rect(0, 0, 20, 20));
        a.parent = String::from("I");
        dump.boxes.push(a);
        let mut b = bbox("B", rect(60, 60, 20, 20));
        b.parent = String::from("O");
        dump.boxes.push(b);
        dump.routes
            .push(route("e0", "A", "B", vec![point(10, 20), point(70, 60)]));
        let index = Index::new(&dump);
        let scope: Vec<&str> = index.scope(&dump.routes[0]).into_iter().collect();
        assert_eq!(scope, ["A", "B", "I", "O"]);
        let owner: Vec<&str> = index.owner_ancestors("e0").into_iter().collect();
        assert_eq!(owner, ["I", "O"]);
        let boxed: Vec<&str> = index.owner_ancestors("B").into_iter().collect();
        assert_eq!(boxed, ["O"]);
    }

    #[test]
    fn on_boundary_accepts_the_four_sides_and_rejects_the_interior() {
        let r = rect(0, 0, 10, 10);
        for p in [
            point(0, 0),
            point(10, 10),
            point(0, 5),
            point(10, 5),
            point(5, 0),
            point(5, 10),
        ] {
            assert!(on_boundary(p, r), "{p:?}");
        }
        for p in [point(5, 5), point(11, 0), point(-1, 0)] {
            assert!(!on_boundary(p, r), "{p:?}");
        }
    }

    #[test]
    fn a_canvas_beyond_the_limit_is_malformed() {
        let dump = valid_dump();
        let limit = i32::try_from(COORD_LIMIT).unwrap_or(i32::MAX);
        let oversized = Size {
            w: limit + 1,
            h: 10,
        };
        assert_eq!(
            well_formed(oversized, &dump),
            Err(Malformed::Coordinate(String::from("canvas ")))
        );
    }
}
