//! The display list of the xychart plan: axes, bars, line paths, legend markers, and texts.

use crate::geom::{GeomError, Point, floor_div};
use crate::measure::Role;
use crate::model::chart::{Plot, PlotKind, Point as ChartPoint};
use crate::scene::{
    Group, GroupRole, Item, Line, PathCommand, PathItem, PolylineItem, RectItem, Shape, ShapeStyle,
    TextItem, TextRole, TextStyle, Width,
};

use super::xy::{Placed, XyPlan};
use super::xy_axis::{Axis, Position};
use super::xy_spec::{BoxKind, BoxSpec, LabelKind};
use super::{Area, LayoutError, to_i32};

const SERIES_COUNT: usize = 12;
const LINE_STYLES: [Line; 3] = [Line::Solid, Line::Dashed, Line::Dotted];

#[derive(Debug, Clone, Copy)]
struct Segment {
    from: (i64, i64),
    to: (i64, i64),
}

fn point_of(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

fn series_of(plot: usize) -> u8 {
    u8::try_from(plot % SERIES_COUNT).unwrap_or(0)
}

fn bar_shape(plot: usize) -> Shape {
    Shape::plain(ShapeStyle::Series).with_series(series_of(plot))
}

fn line_shape(plot: usize) -> Shape {
    Shape::plain(ShapeStyle::SeriesLine)
        .with_series(series_of(plot))
        .with_width(Width::Emphasis)
        .with_line(LINE_STYLES[plot % LINE_STYLES.len()])
}

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

fn line_runs(plot: &Plot) -> Vec<Vec<&ChartPoint>> {
    let mut runs: Vec<Vec<&ChartPoint>> = Vec::new();
    let mut open = false;
    for point in &plot.points {
        if !point.present {
            open = false;
        } else if let (true, Some(run)) = (open, runs.last_mut()) {
            run.push(point);
        } else {
            runs.push(vec![point]);
            open = true;
        }
    }
    runs
}

impl XyPlan<'_> {
    fn placed(&self) -> Result<&Placed, LayoutError> {
        self.placed.as_ref().ok_or(GeomError::Domain)
    }

    fn axis_base(a: &Axis) -> i64 {
        let (area, line) = (a.area, a.space.line);
        match a.position {
            Position::Bottom => area.y + floor_div(line, 2),
            Position::Left => area.x + area.w - line + floor_div(line, 2),
            Position::Top => area.y + area.h - line + floor_div(line, 2),
        }
    }

    fn axis_line(&self, a: &Axis) -> Segment {
        let (base, end) = (Self::axis_base(a), a.r1 - self.c.edge);
        match a.position {
            Position::Left => Segment {
                from: (base, a.r0),
                to: (base, end),
            },
            Position::Bottom | Position::Top => Segment {
                from: (a.r0, base),
                to: (end, base),
            },
        }
    }

    fn tick_segment(&self, a: &Axis, at: i64) -> Segment {
        let (area, sp, base) = (a.area, a.space, Self::axis_base(a));
        match a.position {
            Position::Bottom => Segment {
                from: (at, base),
                to: (at, area.y + sp.line + sp.tick - self.c.edge),
            },
            Position::Left => Segment {
                from: (base, at),
                to: (area.x + area.w - sp.line - sp.tick, at),
            },
            Position::Top => Segment {
                from: (at, base),
                to: (at, area.y + area.h - sp.line - sp.tick),
            },
        }
    }

    fn axis_segments(&self, a: &Axis) -> Vec<Segment> {
        let mut out = vec![self.axis_line(a)];
        out.extend((0..a.count()).map(|k| self.tick_segment(a, a.tick_position(k, self.c.edge))));
        out
    }

    fn axis_items(&self, a: &Axis) -> Result<Vec<Item>, LayoutError> {
        let mut out = Vec::new();
        for (i, s) in self.axis_segments(a).iter().enumerate() {
            let unused = if i == 0 {
                a.space.line == 0
            } else {
                a.space.tick == 0
            };
            if unused || s.from == s.to {
                continue;
            }
            out.push(Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Rule),
                points: vec![point_of(s.from.0, s.from.1)?, point_of(s.to.0, s.to.1)?],
                corner: 0,
            }));
        }
        Ok(out)
    }

    pub(crate) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let mut groups = Vec::new();
        let mut axes = self.axis_items(&self.x)?;
        axes.extend(self.axis_items(&self.y)?);
        if !axes.is_empty() {
            groups.push(Group::new(GroupRole::Decor, "").with_items(axes));
        }
        for (i, b) in self.boxes.iter().enumerate() {
            let mut items = self.box_items(i, b)?;
            items.extend(self.text_items(&b.id)?);
            groups.push(Group::new(GroupRole::Node, b.id.as_str()).with_items(items));
        }
        Ok(groups)
    }

    fn box_items(&self, i: usize, b: &BoxSpec) -> Result<Vec<Item>, LayoutError> {
        match b.kind {
            BoxKind::Plot => self.legend_markers(),
            BoxKind::Line => Ok(vec![self.line_path(b.plot)?]),
            BoxKind::Bar => Ok(vec![Item::Rect(RectItem {
                shape: bar_shape(b.plot),
                rect: self.placed()?.box_rects[i],
            })]),
        }
    }

    fn line_path(&self, index: usize) -> Result<Item, LayoutError> {
        let mut commands = Vec::new();
        for run in line_runs(&self.xy.plots[index]) {
            for (j, point) in run.iter().enumerate() {
                let (x, y) = self.point_xy(point);
                let at = point_of(x, y)?;
                if j == 0 {
                    commands.push(PathCommand::Move(at));
                }
                if j > 0 || run.len() == 1 {
                    commands.push(PathCommand::Line(at));
                }
            }
        }
        Ok(Item::Path(PathItem {
            shape: line_shape(index),
            commands,
        }))
    }

    fn legend_markers(&self) -> Result<Vec<Item>, LayoutError> {
        if !self.legend_on {
            return Ok(Vec::new());
        }
        let c = self.c;
        let mut items = Vec::new();
        for (i, plot) in self.xy.plots.iter().enumerate() {
            let step = self.legend_lh + c.item_gap;
            let row = self.legend.y + c.legend_pad + i64::try_from(i).unwrap_or(i64::MAX) * step;
            let x = self.legend.x + c.legend_pad;
            let y = row + floor_div(self.legend_lh - c.legend_marker, 2);
            if plot.kind == PlotKind::Bar {
                items.push(Item::Rect(RectItem {
                    shape: bar_shape(i),
                    rect: Area::new(x, y, c.legend_marker, c.legend_marker).to_rect()?,
                }));
                continue;
            }
            let middle = y + floor_div(c.legend_marker, 2);
            items.push(Item::Path(PathItem {
                shape: line_shape(i),
                commands: vec![
                    PathCommand::Move(point_of(x, middle)?),
                    PathCommand::Line(point_of(x + c.legend_marker - c.edge, middle)?),
                ],
            }));
        }
        Ok(items)
    }

    fn text_items(&self, owner: &str) -> Result<Vec<Item>, LayoutError> {
        let placed = self.placed()?;
        Ok(self
            .specs
            .iter()
            .enumerate()
            .filter(|(i, s)| s.owner == owner && placed.shown[*i])
            .map(|(i, _)| self.text_item(placed, i))
            .collect())
    }

    fn text_item(&self, placed: &Placed, i: usize) -> Item {
        let spec = &self.specs[i];
        let (role, size) = self.style_of(spec);
        let style = if matches!(spec.kind, LabelKind::XTick | LabelKind::YTick) {
            TextStyle::TextMuted
        } else {
            TextStyle::Text
        };
        let lines = self.texts[i]
            .lines
            .iter()
            .map(|line| line.runs.clone())
            .collect();
        Item::Text(TextItem {
            rect: placed.label_rects[i],
            role: text_role(role),
            size,
            align: placed.aligns[i],
            style,
            series: 0,
            lines,
        })
    }
}
