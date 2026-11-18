//! The dump part and the display list of the cynefin plan.

use crate::geom::{GeomError, Point};
use crate::measure::Role;
use crate::scene::{
    Align, EllipseItem, Group, GroupRole, Item, MarkerName, MarkerRefItem, PolylineItem, Profile,
    RectItem, RoundRectItem, Shape, ShapeStyle,
};

use super::LayoutError;
use super::cynefin::CynefinPlan;
use super::cynefin_route::axis_of;
use super::cynefin_shape::{cliff_path, new_fold};
use super::cynefin_spec::{
    FRAME_ID, Frame, TITLE_ID, cynefin_skeleton, domain_label_id, item_label_id, route_label_id,
};
use super::cynefin_stack::DomainPlan;
use super::cynefin_text::{TextSpec, point_of};
use super::to_i32;

const QUADRANTS: [&str; 4] = ["complex", "complicated", "clear", "chaotic"];
const MARKER: &str = "point";

impl CynefinPlan<'_> {
    pub(crate) fn place_labels(&mut self) {
        if self.title_shown {
            self.set_label(TITLE_ID, self.title_at, Align::Middle, self.title.clone());
        }
        for i in 0..self.domains.len() {
            let d = self.domains[i].clone();
            self.set_label(
                &domain_label_id(&d.name),
                d.name_at,
                Align::Middle,
                d.title.clone(),
            );
            for (k, item) in d.items.iter().enumerate() {
                self.set_label(
                    &item_label_id(&d.name, k),
                    d.texts[k],
                    Align::Middle,
                    item.clone(),
                );
            }
        }
    }

    pub(crate) fn dump_frame(&self) -> Result<Frame, LayoutError> {
        let mut frame = cynefin_skeleton(self.chart);
        for b in &mut frame.boxes {
            let area = if b.id == FRAME_ID {
                self.frame_area()
            } else {
                self.domains[self.domain_index(&b.id)].bounds
            };
            b.rect = area.to_rect()?;
        }
        for (route, path) in frame.routes.iter_mut().zip(&self.paths) {
            for p in path {
                route.points.push(point_of(p.x, p.y)?);
            }
        }
        for label in &mut frame.labels {
            if let Some(placed) = self.labels.get(&label.id) {
                label.rect = placed.at.to_rect()?;
                label.lines.clone_from(&placed.text.plain);
            }
        }
        Ok(frame)
    }

    fn text_item(&self, id: &str, role: Role) -> Result<Item, LayoutError> {
        let placed = self.labels.get(id).ok_or(crate::geom::GeomError::Domain)?;
        TextSpec::of_role(self.profile, role).item(&placed.text, placed.at, placed.align)
    }

    pub(crate) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let mut groups = vec![Group::new(GroupRole::Decor, "").with_items(self.decor()?)];
        for (i, route) in self.routes.iter().enumerate() {
            groups.push(
                Group::new(GroupRole::Edge, route.id.as_str()).with_items(self.edge_items(i)?),
            );
        }
        let mut frame = Vec::new();
        if self.title_shown {
            frame.push(self.text_item(TITLE_ID, Role::Title)?);
        }
        groups.push(Group::new(GroupRole::Node, FRAME_ID).with_items(frame));
        for d in &self.domains {
            groups.push(
                Group::new(GroupRole::Node, d.name.as_str()).with_items(self.domain_items(d)?),
            );
        }
        Ok(groups)
    }

    fn domain_items(&self, d: &DomainPlan) -> Result<Vec<Item>, LayoutError> {
        let mut items = Vec::new();
        if self.profile == Profile::Vector {
            for badge in &d.badges {
                items.push(Item::RoundRect(RoundRectItem {
                    shape: Shape::plain(ShapeStyle::Node),
                    rect: badge.to_rect()?,
                    r: to_i32(self.c.corner)?,
                }));
            }
        }
        items.push(self.text_item(&domain_label_id(&d.name), Role::Label)?);
        for k in 0..d.items.len() {
            items.push(self.text_item(&item_label_id(&d.name, k), Role::Body)?);
        }
        Ok(items)
    }

    fn edge_items(&self, index: usize) -> Result<Vec<Item>, LayoutError> {
        let path = &self.paths[index];
        let points = path
            .iter()
            .map(|p| point_of(p.x, p.y))
            .collect::<Result<Vec<Point>, LayoutError>>()?;
        let marker = match (path.windows(2).last(), points.last()) {
            (Some(pair), Some(&at)) => Some(Item::MarkerRef(MarkerRefItem {
                marker: MarkerName::new(MARKER).ok_or(GeomError::Domain)?,
                at,
                axis: axis_of(pair[0], pair[1]),
            })),
            _ => None,
        };
        let mut items = vec![Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Edge),
            points,
            corner: to_i32(self.c.corner)?,
        })];
        items.extend(marker);
        if !self.routes[index].label.is_empty() {
            items.push(self.text_item(&route_label_id(index), Role::Body)?);
        }
        Ok(items)
    }

    fn decor(&self) -> Result<Vec<Item>, LayoutError> {
        let mut items = Vec::new();
        for name in QUADRANTS {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Band),
                rect: self.quadrant(name).to_rect()?,
            }));
        }
        let fold = new_fold(
            self.c.seed,
            self.cx,
            self.c.height,
            self.c.amplitude,
            self.c.waves,
        );
        items.push(if self.profile == Profile::Cell {
            fold.line_path()?
        } else {
            fold.path()?
        });
        items.extend(self.dividers()?);
        items.push(cliff_path(self.c.width, self.c.height, self.cx, self.cy)?);
        items.push(self.ellipse_item()?);
        Ok(items)
    }

    fn dividers(&self) -> Result<Vec<Item>, LayoutError> {
        let (rx, _) = self.ellipse();
        let mut items = Vec::new();
        for (from, to) in [
            (0, self.cx - rx),
            (self.cx + rx, self.c.width - self.c.edge),
        ] {
            if from >= to {
                continue;
            }
            items.push(Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Rule),
                points: vec![point_of(from, self.cy)?, point_of(to, self.cy)?],
                corner: 0,
            }));
        }
        Ok(items)
    }

    fn ellipse_item(&self) -> Result<Item, LayoutError> {
        let (rx, ry) = self.ellipse();
        Ok(Item::Ellipse(EllipseItem {
            shape: Shape::plain(ShapeStyle::Group),
            cx: to_i32(self.cx)?,
            cy: to_i32(self.cy)?,
            rx: to_i32(rx)?,
            ry: to_i32(ry)?,
        }))
    }
}
