//! The display list of the pie plan: slice paths, legend swatches, percent plates, and
//! texts.

use crate::geom::{GeomError, Point, floor_mod};
use crate::measure::Role;
use crate::scene::{
    Group, GroupRole, Item, PathCommand, PathItem, RectItem, Shape, ShapeStyle, TextItem, TextRole,
    TextStyle,
};

use super::pie::{
    FULL_TURN, HALF_TURN, LabelKind, PLOT_ID, PiePlan, QUARTER_TURN, Slice, arc_vertex, role_of,
    slice_id,
};
use super::{LayoutError, to_i32};

const SERIES_COUNT: usize = 12;

fn bar_shape(section: usize) -> Shape {
    let series = u8::try_from(section % SERIES_COUNT).unwrap_or(0);
    Shape::plain(ShapeStyle::Series).with_series(series)
}

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

fn point_of(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

struct PathBuilder {
    commands: Vec<PathCommand>,
}

impl PathBuilder {
    fn move_to(&mut self, x: i64, y: i64) -> Result<(), LayoutError> {
        self.commands.push(PathCommand::Move(point_of(x, y)?));
        Ok(())
    }

    fn line_to(&mut self, x: i64, y: i64) -> Result<(), LayoutError> {
        self.commands.push(PathCommand::Line(point_of(x, y)?));
        Ok(())
    }

    fn arc(&mut self, cx: i64, cy: i64, r: i64, a0: i64, sweep: i64) -> Result<(), LayoutError> {
        self.commands.push(PathCommand::Arc {
            centre: point_of(cx, cy)?,
            r: to_i32(r)?,
            start: to_i32(floor_mod(a0, FULL_TURN))?,
            sweep: to_i32(sweep)?,
        });
        Ok(())
    }

    fn circle(&mut self, cx: i64, cy: i64, r: i64, a0: i64, half: i64) -> Result<(), LayoutError> {
        let (x, y) = arc_vertex(cx, cy, r, a0);
        self.move_to(x, y)?;
        self.arc(cx, cy, r, a0, half)?;
        self.arc(cx, cy, r, a0 + half, half)?;
        self.commands.push(PathCommand::Close);
        Ok(())
    }

    fn slice(&mut self, g: &super::pie::Geom, a0: i64, sweep: i64) -> Result<(), LayoutError> {
        let (cx, cy, r, inner) = (g.cx, g.cy, g.radius, g.inner);
        if sweep == FULL_TURN {
            self.circle(cx, cy, r, a0, HALF_TURN)?;
            if inner > 0 {
                self.circle(cx, cy, inner, a0, -HALF_TURN)?;
            }
            return Ok(());
        }
        let (x, y) = arc_vertex(cx, cy, r, a0);
        if inner == 0 {
            self.move_to(cx, cy)?;
            self.line_to(x, y)?;
        } else {
            self.move_to(x, y)?;
        }
        self.arc(cx, cy, r, a0, sweep)?;
        if inner > 0 {
            let (x, y) = arc_vertex(cx, cy, inner, a0 + sweep);
            self.line_to(x, y)?;
            self.arc(cx, cy, inner, a0 + sweep, -sweep)?;
        }
        self.commands.push(PathCommand::Close);
        Ok(())
    }
}

impl PiePlan<'_> {
    fn slice_path(&self, slice: &Slice) -> Result<Item, LayoutError> {
        let a0 = floor_mod(slice.start - QUARTER_TURN, FULL_TURN);
        let mut b = PathBuilder {
            commands: Vec::new(),
        };
        b.slice(&self.g, a0, slice.sweep)?;
        Ok(Item::Path(PathItem {
            shape: bar_shape(slice.section),
            commands: b.commands,
        }))
    }

    fn text_item(&self, index: usize) -> Result<TextItem, LayoutError> {
        let (role, size) = role_of(&self.labels[index]);
        let lines = self.texts[index]
            .lines
            .iter()
            .map(|line| line.runs.clone())
            .collect();
        Ok(TextItem {
            rect: self.rects[index].to_rect()?,
            role: text_role(role),
            size,
            align: self.align_of(index),
            style: TextStyle::Text,
            series: 0,
            lines,
        })
    }

    pub(super) fn groups(&self) -> Result<Vec<Group>, GeomError> {
        if !self.placed {
            return Err(GeomError::Domain);
        }
        let mut plot = Group::new(GroupRole::Node, PLOT_ID);
        for (i, sw) in self.swatches.iter().enumerate() {
            plot.items.push(Item::Rect(RectItem {
                shape: bar_shape(i),
                rect: sw.to_rect()?,
            }));
        }
        let mut slices: Vec<Group> = Vec::with_capacity(self.slices.len());
        for slice in &self.slices {
            slices.push(
                Group::new(GroupRole::Node, slice_id(slice.section))
                    .with_items(vec![self.slice_path(slice)?]),
            );
        }
        for (i, label) in self.labels.iter().enumerate() {
            let text = self.text_item(i)?;
            if label.kind != LabelKind::Percent {
                plot.items.push(Item::Text(text));
                continue;
            }
            slices[label.index].items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Plate),
                rect: text.rect,
            }));
            slices[label.index].items.push(Item::Text(text));
        }
        let mut groups = vec![plot];
        groups.extend(slices);
        Ok(groups)
    }
}
