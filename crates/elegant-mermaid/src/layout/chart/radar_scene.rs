//! The display list of the radar plan: graticule rings, axis lines, curve paths, legend
//! markers, and texts.

use crate::geom::{GeomError, Point};
use crate::measure::Role;
use crate::model::chart::Graticule;
use crate::scene::{
    EllipseItem, Group, GroupRole, Item, PathCommand, PathItem, PolygonItem, PolylineItem,
    RectItem, Shape, ShapeStyle, TextItem, TextRole, TextStyle,
};

use super::radar::{LabelKind, PLOT_ID, Pt, RadarPlan, curve_id, role_of};
use super::{LayoutError, to_i32};

const SERIES_COUNT: usize = 12;

fn series_of(index: usize) -> u8 {
    u8::try_from(index % SERIES_COUNT).unwrap_or(0)
}

fn rule_shape() -> Shape {
    Shape::plain(ShapeStyle::Rule)
}

fn tint_shape(curve: usize) -> Shape {
    Shape::plain(ShapeStyle::SeriesTint).with_series(series_of(curve))
}

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

impl RadarPlan<'_> {
    fn at(&self, p: Pt) -> Result<Point, LayoutError> {
        Ok(Point {
            x: to_i32(p.x + self.dx)?,
            y: to_i32(p.y + self.dy)?,
        })
    }

    fn at_all(&self, points: &[Pt]) -> Result<Vec<Point>, LayoutError> {
        points.iter().map(|&p| self.at(p)).collect()
    }

    fn ring(&self, radius: i64) -> Result<Option<Item>, LayoutError> {
        if self.r.graticule == Graticule::Circle {
            let centre = self.at(Pt::default())?;
            let r = to_i32(radius)?;
            return Ok(Some(Item::Ellipse(EllipseItem {
                shape: rule_shape(),
                cx: centre.x,
                cy: centre.y,
                rx: r,
                ry: r,
            })));
        }
        let points = self.at_all(&self.vertices(radius))?;
        Ok(match points.len() {
            0 | 1 => None,
            2 => Some(Item::Polyline(PolylineItem {
                shape: rule_shape(),
                points,
                corner: 0,
            })),
            _ => Some(Item::Polygon(PolygonItem {
                shape: rule_shape(),
                points,
            })),
        })
    }

    fn underlay(&self) -> Result<Vec<Item>, LayoutError> {
        let mut items = Vec::new();
        for &radius in self.rings.iter().filter(|&&radius| radius != 0) {
            items.extend(self.ring(radius)?);
        }
        if self.radius == 0 {
            return Ok(items);
        }
        let centre = self.at(Pt::default())?;
        for tip in self.at_all(&self.vertices(self.radius))? {
            items.push(Item::Polyline(PolylineItem {
                shape: rule_shape(),
                points: vec![centre, tip],
                corner: 0,
            }));
        }
        Ok(items)
    }

    fn curve_path(&self, k: usize) -> Result<Item, LayoutError> {
        let points = &self.curves[k];
        let first = points.first().copied().unwrap_or_default();
        let mut commands = vec![PathCommand::Move(self.at(first)?)];
        if self.r.graticule == Graticule::Circle {
            for b in self.smooth(points) {
                commands.push(PathCommand::Curve {
                    c1: self.at(b.c1)?,
                    c2: self.at(b.c2)?,
                    to: self.at(b.to)?,
                });
            }
        } else {
            for &p in points.iter().skip(1) {
                commands.push(PathCommand::Line(self.at(p)?));
            }
        }
        commands.push(PathCommand::Close);
        Ok(Item::Path(PathItem {
            shape: tint_shape(self.drawn[k]),
            commands,
        }))
    }

    fn text_item(&self, index: usize) -> Item {
        let (role, size) = role_of(&self.labels[index]);
        let lines = self.texts[index]
            .lines
            .iter()
            .map(|line| line.runs.clone())
            .collect();
        Item::Text(TextItem {
            rect: self.label_rects[index],
            role: text_role(role),
            size,
            align: self.aligns[index],
            style: TextStyle::Text,
            series: 0,
            lines,
        })
    }

    fn text_items(&self, kind: LabelKind) -> Vec<Item> {
        self.labels
            .iter()
            .enumerate()
            .filter(|(index, label)| label.kind == kind && self.shown[*index])
            .map(|(index, _)| self.text_item(index))
            .collect()
    }

    fn overlay(&self) -> Result<Vec<Item>, LayoutError> {
        let mut items = self.text_items(LabelKind::Title);
        for (index, marker) in self.markers.iter().enumerate() {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Series).with_series(series_of(index)),
                rect: self.shift(*marker).to_rect()?,
            }));
        }
        items.extend(self.text_items(LabelKind::Legend));
        Ok(items)
    }

    pub(super) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        if !self.placed {
            return Err(GeomError::Domain);
        }
        let mut groups = Vec::new();
        let under = self.underlay()?;
        if !under.is_empty() {
            groups.push(Group::new(GroupRole::Decor, "").with_items(under));
        }
        groups.push(
            Group::new(GroupRole::Node, PLOT_ID).with_items(self.text_items(LabelKind::Axis)),
        );
        for (k, &index) in self.drawn.iter().enumerate() {
            groups.push(
                Group::new(GroupRole::Node, curve_id(index)).with_items(vec![self.curve_path(k)?]),
            );
        }
        let over = self.overlay()?;
        if !over.is_empty() {
            groups.push(Group::new(GroupRole::Decor, "").with_items(over));
        }
        Ok(groups)
    }
}
