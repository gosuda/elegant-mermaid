//! The scene of the Wardley plan: routes, dump boxes and labels, texts, and groups.

use crate::geom::{GeomError, Point};
use crate::measure::Role;
use crate::scene::{
    Group, GroupRole, Item, Line, MarkerAxis, SceneBox, SceneLabel, Shape, ShapeStyle, TextItem,
    TextRole, TextStyle,
};

use super::wardley::{
    BOX_ID, Kind, MARKER_POINT, PLOT_ID, STROKE_DASHED, accelerator_id, annotation_id,
    deaccelerator_id, ghost_id, node_id, pipeline_id,
};
use super::wardley_items::{marker, open_path, point_of};
use super::wardley_plan::{Plan, Pt};
use super::{LayoutError, to_i32};

const STROKE_DOTTED: &str = "dotted";

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

fn stroke_line(stroke: &str) -> Line {
    match stroke {
        STROKE_DASHED => Line::Dashed,
        STROKE_DOTTED => Line::Dotted,
        _ => Line::Solid,
    }
}

fn axis_of(dx: i64, dy: i64) -> MarkerAxis {
    match (dx.abs() >= dy.abs(), dx >= 0, dy >= 0) {
        (true, true, _) => MarkerAxis::PlusX,
        (true, false, _) => MarkerAxis::MinusX,
        (false, _, true) => MarkerAxis::PlusY,
        (false, _, false) => MarkerAxis::MinusY,
    }
}

fn step_back(to: Pt, axis: MarkerAxis) -> Pt {
    match axis {
        MarkerAxis::PlusX => Pt { x: to.x - 1, ..to },
        MarkerAxis::MinusX => Pt { x: to.x + 1, ..to },
        MarkerAxis::PlusY => Pt { y: to.y - 1, ..to },
        MarkerAxis::MinusY => Pt { y: to.y + 1, ..to },
    }
}

fn as_pt(p: Point) -> Pt {
    Pt {
        x: i64::from(p.x),
        y: i64::from(p.y),
    }
}

impl Plan<'_> {
    pub(super) fn build_routes(&mut self) -> Result<(), LayoutError> {
        let w = self.w;
        let mut routes = w.skeleton_routes();
        let mut ends: Vec<(Pt, Pt)> = Vec::with_capacity(routes.len());
        for k in 0..w.pipelines.len() {
            ends.extend(
                w.pipeline_links(k)
                    .into_iter()
                    .map(|(a, b)| (self.pos[a], self.pos[b])),
            );
        }
        ends.extend(w.links.iter().map(|l| (self.pos[l.from], self.pos[l.to])));
        for (k, t) in w.trends.iter().enumerate() {
            ends.push((self.pos[t.node], self.ghosts[k]));
        }
        for (route, (a, b)) in routes.iter_mut().zip(ends) {
            route.points = vec![point_of(a.x, a.y)?, point_of(b.x, b.y)?];
        }
        self.routes = routes;
        Ok(())
    }

    pub(super) fn place_boxes(&mut self) -> Result<(), LayoutError> {
        let zero = |q: &Pt| super::Area::new(q.x, q.y, 0, 0);
        let mut areas = vec![self.plot];
        areas.extend(self.frames.iter().copied());
        areas.extend(self.pos.iter().map(zero));
        areas.extend(self.ghosts.iter().map(zero));
        areas.extend(self.accels.iter().copied());
        areas.extend(self.decels.iter().copied());
        areas.extend(self.points.iter().map(zero));
        if self.w.shows_box() {
            areas.push(self.box_area);
        }
        self.box_rects = areas
            .into_iter()
            .map(super::Area::to_rect)
            .collect::<Result<_, _>>()?;
        Ok(())
    }

    pub(super) fn grow(&mut self) {
        for (r, shown) in self.rects.iter().zip(&self.shown) {
            if *shown {
                self.width = self.width.max(i64::from(r.x) + i64::from(r.w));
                self.height = self.height.max(i64::from(r.y) + i64::from(r.h));
            }
        }
        if self.w.shows_box() {
            let b = self.box_area;
            self.width = self.width.max(b.x + b.w);
            self.height = self.height.max(b.y + b.h);
        }
    }

    pub(super) fn dump_boxes(&self) -> Vec<SceneBox> {
        let mut boxes = self.w.skeleton_boxes();
        for (b, rect) in boxes.iter_mut().zip(&self.box_rects) {
            b.rect = *rect;
        }
        boxes
    }

    pub(super) fn dump_labels(&self) -> Vec<SceneLabel> {
        self.specs
            .iter()
            .enumerate()
            .map(|(i, s)| SceneLabel {
                id: s.id.clone(),
                owner: s.owner.clone(),
                text: s.text.clone(),
                rect: self.rects[i],
                lines: self.lines[i].clone(),
            })
            .collect()
    }

    fn text_items(&self, owner: &str) -> Vec<Item> {
        self.specs
            .iter()
            .enumerate()
            .filter(|(i, s)| s.owner == owner && self.shown[*i])
            .map(|(i, _)| self.text_item(i))
            .collect()
    }

    fn text_item(&self, i: usize) -> Item {
        let spec = &self.specs[i];
        let (role, size) = self.style_of(spec);
        let style = if matches!(spec.kind, Kind::AxisX | Kind::AxisY | Kind::Stage) {
            TextStyle::TextMuted
        } else {
            TextStyle::Text
        };
        Item::Text(TextItem {
            rect: self.rects[i],
            role: text_role(role),
            size,
            align: self.aligns[i],
            style,
            series: 0,
            lines: self.texts[i].lines.iter().map(|l| l.runs.clone()).collect(),
        })
    }

    pub(super) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let mut groups = Groups::default();
        self.underlay(&mut groups)?;
        self.overlay(&mut groups)?;
        Ok(groups.list)
    }

    fn underlay(&self, groups: &mut Groups) -> Result<(), LayoutError> {
        groups.add(GroupRole::Decor, "", self.decor_items()?);
        for (i, route) in self.routes.iter().enumerate() {
            groups.add(GroupRole::Edge, &route.id, self.route_items(i)?);
        }
        Ok(())
    }

    fn overlay(&self, groups: &mut Groups) -> Result<(), LayoutError> {
        groups.add(GroupRole::Node, PLOT_ID, self.text_items(PLOT_ID));
        for k in 0..self.w.pipelines.len() {
            groups.add(GroupRole::Node, &pipeline_id(k), self.frame_items(k)?);
        }
        for k in 0..self.w.nodes.len() {
            let id = node_id(k);
            let mut items = self.node_items(k)?;
            items.extend(self.text_items(&id));
            groups.add(GroupRole::Node, &id, items);
        }
        self.extra_groups(groups)
    }

    fn extra_groups(&self, groups: &mut Groups) -> Result<(), LayoutError> {
        for k in 0..self.ghosts.len() {
            groups.add(GroupRole::Node, &ghost_id(k), self.ghost_items(k)?);
        }
        for (k, area) in self.accels.iter().enumerate() {
            let id = accelerator_id(k);
            let mut items = self.accelerator_items(*area)?;
            items.extend(self.text_items(&id));
            groups.add(GroupRole::Node, &id, items);
        }
        for (k, area) in self.decels.iter().enumerate() {
            let id = deaccelerator_id(k);
            let mut items = self.deaccelerator_items(*area)?;
            items.extend(self.text_items(&id));
            groups.add(GroupRole::Node, &id, items);
        }
        for k in 0..self.points.len() {
            let id = annotation_id(k);
            let mut items = self.annotation_items(k)?;
            items.extend(self.text_items(&id));
            groups.add(GroupRole::Node, &id, items);
        }
        if self.w.shows_box() {
            let mut items = self.box_items()?;
            items.extend(self.text_items(BOX_ID));
            groups.add(GroupRole::Node, BOX_ID, items);
        }
        Ok(())
    }

    fn reach_of(&self, id: &str) -> i64 {
        let node = id
            .strip_prefix('n')
            .and_then(|rest| rest.parse::<usize>().ok())
            .and_then(|k| self.w.nodes.get(k));
        node.map_or(self.c.node_radius, |n| self.reach(n))
    }

    fn route_items(&self, i: usize) -> Result<Vec<Item>, LayoutError> {
        let route = &self.routes[i];
        let (Some(first), Some(last)) = (route.points.first(), route.points.last()) else {
            return Err(GeomError::Domain);
        };
        let (a, b) = (as_pt(*first), as_pt(*last));
        let shape = Shape::plain(ShapeStyle::Edge).with_line(stroke_line(&route.stroke));
        let mut items = vec![open_path(shape, &[a, b])?];
        if route.marker_start == MARKER_POINT {
            let (at, axis) = self.arrowhead(b, a, self.reach_of(&route.from));
            items.push(marker(at, axis)?);
        }
        if route.marker_end == MARKER_POINT {
            let (at, axis) = self.arrowhead(a, b, self.reach_of(&route.to));
            items.push(marker(at, axis)?);
        }
        items.extend(self.text_items(&route.id));
        Ok(items)
    }

    fn arrowhead(&self, from: Pt, to: Pt, reach: i64) -> (Pt, MarkerAxis) {
        let (dx, dy) = (to.x - from.x, to.y - from.y);
        let axis = axis_of(dx, dy);
        if dx == 0 && dy == 0 {
            return (to, axis);
        }
        if self.cell {
            return (step_back(to, axis), axis);
        }
        let Ok(length) = crate::geom::isqrt(dx * dx + dy * dy) else {
            return (to, axis);
        };
        let pulled = Pt {
            x: to.x - crate::measure::round_half_up(dx * reach, length),
            y: to.y - crate::measure::round_half_up(dy * reach, length),
        };
        (pulled, axis)
    }

    pub(super) fn canvas(&self) -> Result<crate::geom::Size, LayoutError> {
        Ok(crate::geom::Size {
            w: to_i32(self.width)?,
            h: to_i32(self.height)?,
        })
    }
}

#[derive(Default)]
struct Groups {
    list: Vec<Group>,
}

impl Groups {
    fn add(&mut self, role: GroupRole, owner: &str, items: Vec<Item>) {
        if !items.is_empty() {
            self.list.push(Group::new(role, owner).with_items(items));
        }
    }
}
