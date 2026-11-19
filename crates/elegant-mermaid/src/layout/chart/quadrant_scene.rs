//! The display list of the quadrant plan: tile bands, frame, dividers, markers, and texts.

use crate::geom::{GeomError, Point};
use crate::measure::Role;
use crate::scene::{
    EllipseItem, Group, GroupRole, Item, PolylineItem, RectItem, Shape, ShapeStyle, TextItem,
    TextRole, TextStyle, Width,
};

use super::quadrant::QuadPlan;
use super::quadrant_spec::{BoxKind, BoxSpec, LabelKind, PLOT_ID, point_box_id};
use super::{LayoutError, to_i32};

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

fn point_at(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

fn divider(from: (i64, i64), to: (i64, i64)) -> Result<Item, LayoutError> {
    Ok(Item::Polyline(PolylineItem {
        shape: Shape::plain(ShapeStyle::Rule),
        points: vec![point_at(from.0, from.1)?, point_at(to.0, to.1)?],
        corner: 0,
    }))
}

impl QuadPlan<'_> {
    fn text_item(&self, i: usize) -> Result<Item, LayoutError> {
        let placed = self.placed.as_ref().ok_or(GeomError::Domain)?;
        let spec = &self.specs[i];
        let (role, size) = self.style_of(spec);
        let style = match spec.kind {
            LabelKind::XLeft | LabelKind::XRight | LabelKind::YBottom | LabelKind::YTop => {
                TextStyle::TextMuted
            }
            _ => TextStyle::Text,
        };
        let lines = self.texts[i]
            .lines
            .iter()
            .map(|line| line.runs.clone())
            .collect();
        Ok(Item::Text(TextItem {
            rect: placed.label_rects[i],
            role: text_role(role),
            size,
            align: placed.aligns[i],
            style,
            series: 0,
            lines,
        }))
    }

    fn text_items(&self, owner: &str) -> Result<Vec<Item>, LayoutError> {
        self.specs
            .iter()
            .enumerate()
            .filter(|(_, spec)| spec.owner == owner)
            .map(|(i, _)| self.text_item(i))
            .collect()
    }

    fn plot_items(&self) -> Result<Vec<Item>, LayoutError> {
        let (pl, e) = (self.plot, self.c.edge);
        let (column, row) = (self.tiles[0].x, self.tiles[2].y);
        let mut items = vec![
            Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Rule).with_width(Width::Emphasis),
                rect: pl.to_rect()?,
            }),
            divider((column, pl.y), (column, pl.y + pl.h - e))?,
            divider((pl.x, row), (pl.x + pl.w - e, row))?,
        ];
        items.extend(self.text_items(PLOT_ID)?);
        Ok(items)
    }

    fn point_items(&self, k: usize) -> Result<Vec<Item>, LayoutError> {
        let (c, r) = (self.centres[k], self.radii[k]);
        let mut items = Vec::new();
        if r.x > 0 && r.y > 0 {
            items.push(Item::Ellipse(EllipseItem {
                shape: Shape::plain(ShapeStyle::Series),
                cx: to_i32(c.x)?,
                cy: to_i32(c.y)?,
                rx: to_i32(r.x)?,
                ry: to_i32(r.y)?,
            }));
        }
        items.extend(self.text_items(&point_box_id(k))?);
        Ok(items)
    }

    fn box_items(&self, b: &BoxSpec) -> Result<Vec<Item>, LayoutError> {
        match b.kind {
            BoxKind::Plot => self.plot_items(),
            BoxKind::Tile => self.text_items(&b.id),
            BoxKind::Point => self.point_items(b.index),
        }
    }

    pub(super) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let bands = self
            .tiles
            .iter()
            .map(|tile| {
                Ok(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Band),
                    rect: tile.to_rect()?,
                }))
            })
            .collect::<Result<Vec<_>, LayoutError>>()?;
        let mut groups = vec![Group::new(GroupRole::Decor, "").with_items(bands)];
        for b in &self.boxes {
            let items = self.box_items(b)?;
            groups.push(Group::new(GroupRole::Node, b.id.as_str()).with_items(items));
        }
        Ok(groups)
    }
}
