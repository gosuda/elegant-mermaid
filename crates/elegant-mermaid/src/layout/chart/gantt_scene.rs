//! The display list of the gantt plan: excluded-day bands, axes, grid lines, bars,
//! milestones, vertical markers, and texts.

use crate::civil;
use crate::geom::{GeomError, Point, Rect, floor_div};
use crate::measure::Role;
use crate::model::chart::GanttTask;
use crate::scene::{
    Group, GroupRole, Item, PolygonItem, PolylineItem, RectItem, Shape, ShapeStyle, SymbolName,
    SymbolRefItem, TextItem, TextRole, TextStyle,
};

use super::gantt::{BoxKind, GanttBox, GanttPlan, LabelKind, Placed};
use super::{Area, LayoutError, to_i32};

const SERIES_COUNT: usize = 12;

fn point_of(x: i64, y: i64) -> Result<Point, LayoutError> {
    Ok(Point {
        x: to_i32(x)?,
        y: to_i32(y)?,
    })
}

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        _ => TextRole::Label,
    }
}

fn plain_item(style: ShapeStyle, rect: Rect) -> Item {
    Item::Rect(RectItem {
        shape: Shape::plain(style),
        rect,
    })
}

fn bar_shape(t: &GanttTask) -> Shape {
    let style = if t.crit {
        ShapeStyle::Error
    } else if t.done {
        ShapeStyle::Success
    } else if t.active {
        ShapeStyle::Note
    } else {
        return match t.section {
            Some(section) => Shape::plain(ShapeStyle::Series)
                .with_series(u8::try_from(section % SERIES_COUNT).unwrap_or(0)),
            None => Shape::plain(ShapeStyle::Node),
        };
    };
    Shape::plain(style)
}

fn milestone_diamond(r: Rect) -> Item {
    let (cx, cy) = (r.x + r.w / 2, r.y + r.h / 2);
    let points = vec![
        Point { x: cx, y: r.y },
        Point {
            x: r.x + r.w,
            y: cy,
        },
        Point {
            x: cx,
            y: r.y + r.h,
        },
        Point { x: r.x, y: cy },
    ];
    Item::Polygon(PolygonItem {
        shape: Shape::plain(ShapeStyle::Ink),
        points,
    })
}

fn milestone_symbol(r: Rect) -> Result<Item, LayoutError> {
    Ok(Item::SymbolRef(SymbolRefItem {
        symbol: SymbolName::new("diamond").ok_or(GeomError::Domain)?,
        at: Point { x: r.x, y: r.y },
        style: ShapeStyle::Ink,
    }))
}

impl GanttPlan<'_> {
    fn placed(&self) -> Result<&Placed, LayoutError> {
        self.placed.as_ref().ok_or(GeomError::Domain)
    }

    fn task_item(&self, t: &GanttTask, r: Rect) -> Result<Item, LayoutError> {
        if t.vert {
            return Ok(plain_item(ShapeStyle::Ink, r));
        }
        if t.milestone && self.cell {
            return milestone_symbol(r);
        }
        if t.milestone {
            return Ok(milestone_diamond(r));
        }
        Ok(Item::Rect(RectItem {
            shape: bar_shape(t),
            rect: r,
        }))
    }

    pub(crate) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let mut groups = Vec::new();
        let under = self.under_items()?;
        if !under.is_empty() {
            groups.push(Group::new(GroupRole::Decor, "").with_items(under));
        }
        for (i, b) in self.boxes.iter().enumerate() {
            let mut items = self.box_items(i, b)?;
            items.extend(self.text_items(&b.id)?);
            groups.push(Group::new(GroupRole::Node, b.id.as_str()).with_items(items));
        }
        Ok(groups)
    }

    fn under_items(&self) -> Result<Vec<Item>, LayoutError> {
        let mut items = self.excluded_columns()?;
        items.extend(self.axis_lines(self.axis_y(), 1)?);
        if self.g.top_axis {
            items.extend(self.axis_lines(self.top_axis_y(), -1)?);
        }
        Ok(items)
    }

    fn line(x0: i64, y0: i64, x1: i64, y1: i64) -> Result<Item, LayoutError> {
        Ok(Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: vec![point_of(x0, y0)?, point_of(x1, y1)?],
            corner: 0,
        }))
    }

    fn axis_lines(&self, y: i64, sign: i64) -> Result<Vec<Item>, LayoutError> {
        let c = self.c;
        let mut items = vec![Self::line(c.gutter, y, c.width - c.side_pad, y)?];
        for &t in &self.ticks {
            let x = self.time_x(t)?;
            if c.tick_len > 0 {
                items.push(Self::line(x, y, x, y + sign * c.tick_len)?);
            }
            if self.cell || sign < 0 || self.rows == 0 {
                continue;
            }
            items.push(Self::line(x, c.top_pad, x, y)?);
        }
        Ok(items)
    }

    fn excluded_columns(&self) -> Result<Vec<Item>, LayoutError> {
        let span = self.d1 - self.d0;
        let too_long = span > self.c.exclude_years * 366 * civil::SECONDS_PER_DAY;
        if span <= 0 || too_long || self.rows == 0 {
            return Ok(Vec::new());
        }
        let g = self.g;
        let calendar = civil::Calendar::new(&g.excludes, &g.includes, &g.weekend);
        let first = floor_div(self.d0, civil::SECONDS_PER_DAY);
        let last = floor_div(self.d1 - 1, civil::SECONDS_PER_DAY);
        let mut items = Vec::new();
        let mut day = first;
        while day <= last {
            if !calendar.excluded(day) {
                day += 1;
                continue;
            }
            let mut run = day;
            while run < last && calendar.excluded(run + 1) {
                run += 1;
            }
            items.push(self.excluded_run(day, run)?);
            day = run + 1;
        }
        Ok(items)
    }

    fn excluded_run(&self, first: i64, last: i64) -> Result<Item, LayoutError> {
        let x0 = self.time_x((first * civil::SECONDS_PER_DAY).max(self.d0))?;
        let x1 = self.time_x(((last + 1) * civil::SECONDS_PER_DAY).min(self.d1))?;
        let area = Area::new(
            x0.min(x1),
            self.c.top_pad,
            (x1 - x0).abs(),
            self.rows * self.pitch,
        );
        Ok(plain_item(ShapeStyle::Band, area.to_rect()?))
    }

    fn box_items(&self, i: usize, b: &GanttBox) -> Result<Vec<Item>, LayoutError> {
        let rect = self.placed()?.box_rects[i];
        match b.kind {
            BoxKind::Plot => Ok(Vec::new()),
            BoxKind::Section => Ok(vec![plain_item(ShapeStyle::Band, rect)]),
            BoxKind::Task | BoxKind::Vert => {
                let task = self.g.tasks.get(b.index).ok_or(GeomError::Domain)?;
                Ok(vec![self.task_item(task, rect)?])
            }
        }
    }

    fn text_items(&self, owner: &str) -> Result<Vec<Item>, LayoutError> {
        let placed = self.placed()?;
        let mut items = Vec::new();
        for (i, label) in self.labels.iter().enumerate() {
            if label.owner != owner || !placed.shown[i] {
                continue;
            }
            if placed.chips[i] {
                items.push(plain_item(ShapeStyle::Plate, placed.label_rects[i]));
            }
            items.push(self.text_item(placed, i));
        }
        Ok(items)
    }

    fn text_item(&self, placed: &Placed, i: usize) -> Item {
        let label = &self.labels[i];
        let (role, size) = self.style_of(label);
        let style = if matches!(label.kind, LabelKind::Tick | LabelKind::TopTick) {
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
