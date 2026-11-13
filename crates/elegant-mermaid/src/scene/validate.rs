//! The layout validator of `spec/layout-dump.md`: `WellFormed`, the ancestor and scope
//! relations, and the eight hard-constraint clauses in their fixed order.
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

use super::{BoxRole, Dump, SceneBox, SceneLabel, SceneRoute};

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
    /// No group frame overlaps a foreign box, and no label straddles or touches a frame border.
    FrameClearance,
}

/// The eight clauses in their fixed order.
pub const CLAUSES: [Clause; 8] = [
    Clause::Canvas,
    Clause::ExclusiveSiblings,
    Clause::Parent,
    Clause::Orthogonal,
    Clause::Ports,
    Clause::RouteClearance,
    Clause::LabelClearance,
    Clause::FrameClearance,
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
            Clause::FrameClearance => "frame-clearance",
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
            Clause::FrameClearance => "group frame overlaps a foreign box or label",
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

/// `inner` lies strictly inside `outer`, so it touches none of the four border cells.
fn strictly_inside(outer: Rect, inner: Rect) -> bool {
    let (ox, oy) = (i64::from(outer.x), i64::from(outer.y));
    let (ix, iy) = (i64::from(inner.x), i64::from(inner.y));
    ox < ix
        && ix + i64::from(inner.w) < ox + i64::from(outer.w)
        && oy < iy
        && iy + i64::from(inner.h) < oy + i64::from(outer.h)
}

/// Clause `frame-clearance`: a group frame is disjoint from every box that is neither its
/// member nor its ancestor, and from every label that it does not strictly contain.
fn frame_clearance_holds(index: &Index<'_>, labels: &[SceneLabel]) -> Result<bool, GeomError> {
    let ancestry: Vec<Vec<&str>> = index.boxes.iter().map(|b| index.ancestors(&b.id)).collect();
    for (at, g) in index
        .boxes
        .iter()
        .enumerate()
        .filter(|(_, b)| b.role == BoxRole::Group)
    {
        if !frame_boxes_clear(index, &ancestry, at)? || !frame_labels_clear(g, labels)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn frame_boxes_clear(
    index: &Index<'_>,
    ancestry: &[Vec<&str>],
    at: usize,
) -> Result<bool, GeomError> {
    let g = &index.boxes[at];
    let foreign = index.boxes.iter().enumerate().filter(|(other, b)| {
        *other != at
            && !ancestry[*other].contains(&g.id.as_str())
            && !ancestry[at].contains(&b.id.as_str())
    });
    for (_, b) in foreign {
        if intersects(g.rect, b.rect)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn frame_labels_clear(g: &SceneBox, labels: &[SceneLabel]) -> Result<bool, GeomError> {
    for label in labels {
        if intersects(g.rect, label.rect)? && !strictly_inside(g.rect, label.rect) {
            return Ok(false);
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
    if !frame_clearance_holds(&index, &dump.labels)? {
        return Ok(Some(Clause::FrameClearance));
    }
    Ok(None)
}

/// True exactly when no clause fails.
pub fn check(canvas: Size, dump: &Dump) -> Result<bool, GeomError> {
    Ok(validate(canvas, dump)?.is_none())
}

#[cfg(test)]
#[path = "validate/constraint_tests.rs"]
mod tests;
