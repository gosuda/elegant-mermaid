//! Placement of the xychart plan: label rectangles, bar rectangles, and line bounds.

use crate::geom::{Rect, floor_div};
use crate::model::chart::{Plot, Point};
use crate::scene::Align;

use super::scale::clamp;
use super::xy::{Placed, TextBox, XyPlan};
use super::xy_axis::{Axis, Position};
use super::xy_spec::{BoxKind, LabelKind, LabelSpec};
use super::{Area, LayoutError, ZERO_RECT};

const PERMILLE: i64 = 1000;

struct Slot {
    area: Area,
    align: Align,
    visible: bool,
}

impl Slot {
    fn shown(area: Area, align: Align) -> Slot {
        Slot {
            area,
            align,
            visible: true,
        }
    }

    fn hidden() -> Slot {
        Slot {
            area: Area::default(),
            align: Align::Middle,
            visible: false,
        }
    }

    fn when(visible: bool, area: Area, align: Align) -> Slot {
        Slot {
            area,
            align,
            visible,
        }
    }
}

impl XyPlan<'_> {
    pub(crate) fn fit(&self, r: Area) -> Area {
        Area {
            x: clamp(r.x, 0, (self.width - r.w).max(0)),
            y: clamp(r.y, 0, (self.height - r.h).max(0)),
            ..r
        }
    }

    pub(crate) fn place(&mut self) -> Result<(), LayoutError> {
        let n = self.specs.len();
        let mut label_rects = vec![ZERO_RECT; n];
        let mut label_lines: Vec<Vec<String>> = vec![Vec::new(); n];
        let mut aligns = vec![Align::Start; n];
        let mut shown = vec![false; n];
        for i in 0..n {
            let slot = self.label_slot(i);
            if !slot.visible {
                continue;
            }
            let fitted = self.fit(slot.area);
            if self.overlaps_tick(i, fitted, &label_rects, &shown) {
                continue;
            }
            label_rects[i] = fitted.to_rect()?;
            aligns[i] = slot.align;
            shown[i] = true;
            label_lines[i] = self.texts[i].lines.iter().map(|l| l.text.clone()).collect();
        }
        let box_rects = self.place_boxes()?;
        self.placed = Some(Placed {
            box_rects,
            label_rects,
            label_lines,
            shown,
            aligns,
        });
        Ok(())
    }

    fn overlaps_tick(&self, i: usize, r: Area, rects: &[Rect], shown: &[bool]) -> bool {
        let kind = self.specs[i].kind;
        if !self.cell || !matches!(kind, LabelKind::XTick | LabelKind::YTick) {
            return false;
        }
        let edge = self.c.edge;
        (0..i)
            .filter(|j| self.specs[*j].kind == kind && shown[*j])
            .any(|j| {
                let b = rects[j];
                r.x < i64::from(b.x) + i64::from(b.w) + edge
                    && i64::from(b.x) < r.x + r.w + edge
                    && r.y < i64::from(b.y) + i64::from(b.h)
                    && i64::from(b.y) < r.y + r.h
            })
    }

    fn inside_plot(&self, r: Area) -> Area {
        let p = self.plot;
        Area {
            x: clamp(r.x, p.x, (p.x + p.w - r.w).max(p.x)),
            y: clamp(r.y, p.y, (p.y + p.h - r.h).max(p.y)),
            ..r
        }
    }

    fn label_slot(&self, i: usize) -> Slot {
        let spec = &self.specs[i];
        let t = &self.texts[i];
        match spec.kind {
            LabelKind::Title => Slot::when(self.title_shown, self.title_rect(t), Align::Middle),
            LabelKind::XTitle => self.axis_title_slot(i, &self.x),
            LabelKind::YTitle => self.axis_title_slot(i, &self.y),
            LabelKind::XTick => self.tick_slot(&self.x, spec.index, t),
            LabelKind::YTick => self.tick_slot(&self.y, spec.index, t),
            LabelKind::Legend => self.legend_slot(spec.plot, t),
            LabelKind::Point => self.point_label_slot(spec, t),
        }
    }

    fn title_rect(&self, t: &TextBox) -> Area {
        let half = floor_div(t.w, 2);
        let centre = clamp(
            floor_div(2 * self.plot.x + self.plot.w, 2),
            half,
            self.width - half,
        );
        Area::new(centre - half, self.c.title_pad, t.w, t.h)
    }

    fn axis_title_slot(&self, i: usize, a: &Axis) -> Slot {
        let t = &self.texts[i];
        let c = self.c;
        if a.position == Position::Left {
            let area = Area::new(c.pad_x, self.title_h + c.axis_title_pad, t.w, t.h);
            return Slot::when(
                self.side_shown && self.side_title == Some(i),
                area,
                Align::Start,
            );
        }
        if a.space.title == 0 {
            return Slot::hidden();
        }
        if a.position == Position::Bottom {
            let centre = floor_div(a.r0 + a.r1, 2);
            let y = a.area.y + a.area.h - c.axis_title_pad - t.h;
            return Slot::shown(
                Area::new(centre - floor_div(t.w, 2), y, t.w, t.h),
                Align::Middle,
            );
        }
        let centre = a.area.x + floor_div(a.area.w, 2);
        Slot::shown(
            Area::new(
                centre - floor_div(t.w, 2),
                a.area.y + c.axis_title_pad,
                t.w,
                t.h,
            ),
            Align::Middle,
        )
    }

    fn tick_slot(&self, a: &Axis, k: usize, t: &TextBox) -> Slot {
        if !a.space.show_label {
            return Slot::hidden();
        }
        let c = self.c;
        let pos = a.tick_position(k, c.edge);
        let (line, tick) = (a.space.line, a.space.tick);
        match a.position {
            Position::Bottom => Slot::shown(
                Area::new(
                    pos - floor_div(t.w, 2),
                    a.area.y + c.pad_y + tick + line,
                    t.w,
                    t.h,
                ),
                Align::Middle,
            ),
            Position::Left => Slot::shown(
                Area::new(
                    a.area.x + a.area.w - c.pad_x - tick - line - t.w,
                    pos - floor_div(t.h, 2),
                    t.w,
                    t.h,
                ),
                Align::End,
            ),
            Position::Top => Slot::shown(
                Area::new(
                    pos - floor_div(t.w, 2),
                    a.area.y + a.space.title + c.pad_y,
                    t.w,
                    t.h,
                ),
                Align::Middle,
            ),
        }
    }

    fn legend_slot(&self, plot: usize, t: &TextBox) -> Slot {
        let c = self.c;
        let row = self.legend.y
            + c.legend_pad
            + i64::try_from(plot).unwrap_or(i64::MAX) * (self.legend_lh + c.item_gap);
        let x = self.legend.x + c.legend_pad + c.legend_marker + c.marker_gap;
        Slot::when(self.legend_on, Area::new(x, row, t.w, t.h), Align::Start)
    }

    pub(crate) fn point_xy(&self, point: &Point) -> (i64, i64) {
        let category = self.x.point_position(point, self.c.edge);
        let value = self.y.value_position(point.value, self.c.edge);
        if self.horizontal() {
            (value, category)
        } else {
            (category, value)
        }
    }

    fn point_label_slot(&self, spec: &LabelSpec, t: &TextBox) -> Slot {
        let (px, py) = self.point_xy(&self.xy.plots[spec.plot].points[spec.index]);
        if self.horizontal() {
            let area = Area::new(px + self.c.point_offset, py - floor_div(t.h, 2), t.w, t.h);
            return Slot::shown(self.inside_plot(area), Align::Start);
        }
        let area = Area::new(
            px - floor_div(t.w, 2),
            py - self.c.point_offset - floor_div(t.h, 2),
            t.w,
            t.h,
        );
        Slot::shown(self.inside_plot(area), Align::Middle)
    }

    fn bar_area(&self, point: &Point) -> Area {
        let c = self.c;
        let category = self.x.point_position(point, c.edge);
        let value = self.y.value_position(point.value, c.edge);
        let mut width = floor_div(
            (2 * self.x.outer).min(self.x.tick_distance()) * (PERMILLE - c.bar_pad),
            PERMILLE,
        );
        if self.cell {
            width = width.max(1);
        }
        let start = category - floor_div(width, 2);
        if self.horizontal() {
            return Area::new(self.plot.x, start, value - self.plot.x + c.edge, width);
        }
        Area::new(start, value, width, self.plot.y + self.plot.h - value)
    }

    fn line_bounds(&self, plot: &Plot) -> Area {
        let points: Vec<(i64, i64)> = plot
            .points
            .iter()
            .filter(|point| point.present)
            .map(|point| self.point_xy(point))
            .collect();
        let Some(&(x0, y0)) = points.first() else {
            return Area::new(self.plot.x, self.plot.y, 0, 0);
        };
        let (lo_x, lo_y, hi_x, hi_y) = points
            .iter()
            .fold((x0, y0, x0, y0), |(lx, ly, hx, hy), &(x, y)| {
                (lx.min(x), ly.min(y), hx.max(x), hy.max(y))
            });
        let edge = self.c.edge;
        Area::new(lo_x, lo_y, hi_x - lo_x + edge, hi_y - lo_y + edge)
    }

    fn place_boxes(&self) -> Result<Vec<Rect>, LayoutError> {
        self.boxes
            .iter()
            .map(|b| {
                let area = match b.kind {
                    BoxKind::Plot => self.plot,
                    BoxKind::Line => self.line_bounds(&self.xy.plots[b.plot]),
                    BoxKind::Bar => self.bar_area(&self.xy.plots[b.plot].points[b.point]),
                };
                area.to_rect()
            })
            .collect()
    }
}
