//! Radar geometry: polar points, curve smoothing, label boxes, legend rows, and the
//! translation of the whole plot into non-negative canvas coordinates.

use crate::geom::{Rect, Size, cos_q15, floor_div, floor_mod, sin_q15};
use crate::model::chart::Graticule;
use crate::scene::Align;

use super::radar::{LabelKind, Pt, RadarPlan};
use super::scale::clamp;
use super::xy::TextBox;
use super::{Area, LayoutError, to_i32};

const Q15_ONE: i64 = 32768;
const QUARTER_TURN: i64 = 16384;
const FULL_TURN: i64 = 65536;
const PERMILLE: i64 = 1000;

fn count(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

pub(super) fn polar(radius: i64, theta: i32) -> Pt {
    Pt {
        x: floor_div(radius * i64::from(cos_q15(theta)), Q15_ONE),
        y: floor_div(radius * i64::from(sin_q15(theta)), Q15_ONE),
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Bezier {
    pub c1: Pt,
    pub c2: Pt,
    pub to: Pt,
}

#[derive(Debug, Clone, Copy, Default)]
struct Extent {
    min_x: i64,
    min_y: i64,
    max_x: i64,
    max_y: i64,
}

impl Extent {
    fn add_point(&mut self, p: Pt) {
        self.min_x = self.min_x.min(p.x);
        self.min_y = self.min_y.min(p.y);
        self.max_x = self.max_x.max(p.x);
        self.max_y = self.max_y.max(p.y);
    }

    fn add_area(&mut self, a: Area) {
        self.add_point(Pt { x: a.x, y: a.y });
        self.add_point(Pt {
            x: a.x + a.w,
            y: a.y + a.h,
        });
    }
}

fn bounds_of(points: &[Pt]) -> Area {
    let first = points.first().copied().unwrap_or_default();
    let (mut lo, mut hi) = (first, first);
    for p in points {
        lo = Pt {
            x: lo.x.min(p.x),
            y: lo.y.min(p.y),
        };
        hi = Pt {
            x: hi.x.max(p.x),
            y: hi.y.max(p.y),
        };
    }
    Area::new(lo.x, lo.y, hi.x - lo.x, hi.y - lo.y)
}

impl RadarPlan<'_> {
    pub(super) fn theta(&self, axis: usize) -> i32 {
        let n = count(self.r.axes.len());
        let turns = floor_mod(
            floor_div(count(axis) * FULL_TURN, n) - QUARTER_TURN,
            FULL_TURN,
        );
        i32::try_from(turns).unwrap_or(0)
    }

    pub(super) fn value_radius(&self, value: i64) -> i64 {
        let clip = clamp(value, self.lo, self.hi);
        floor_div(self.radius * (clip - self.lo), self.hi - self.lo)
    }

    pub(super) fn vertices(&self, radius: i64) -> Vec<Pt> {
        (0..self.r.axes.len())
            .map(|axis| polar(radius, self.theta(axis)))
            .collect()
    }

    fn curve_points(&self, index: usize) -> Vec<Pt> {
        self.r.curves[index]
            .values
            .iter()
            .enumerate()
            .map(|(axis, &value)| polar(self.value_radius(value), self.theta(axis)))
            .collect()
    }

    pub(super) fn smooth(&self, points: &[Pt]) -> Vec<Bezier> {
        let n = points.len();
        let t = self.c.tension;
        (0..n)
            .map(|i| {
                let p0 = points[(i + n - 1) % n];
                let (p1, p2, p3) = (points[i], points[(i + 1) % n], points[(i + 2) % n]);
                Bezier {
                    c1: Pt {
                        x: p1.x + floor_div((p2.x - p0.x) * t, PERMILLE),
                        y: p1.y + floor_div((p2.y - p0.y) * t, PERMILLE),
                    },
                    c2: Pt {
                        x: p2.x - floor_div((p3.x - p1.x) * t, PERMILLE),
                        y: p2.y - floor_div((p3.y - p1.y) * t, PERMILLE),
                    },
                    to: p2,
                }
            })
            .collect()
    }

    fn align_of(&self, theta: i32) -> Align {
        let cos = i64::from(cos_q15(theta));
        if cos >= self.c.anchor {
            Align::Start
        } else if cos <= -self.c.anchor {
            Align::End
        } else {
            Align::Middle
        }
    }

    fn axis_area(&self, index: usize, text: &TextBox) -> (Area, Align) {
        let theta = self.theta(index);
        let cos = i64::from(cos_q15(theta));
        let sin = i64::from(sin_q15(theta));
        let at_x = floor_div((self.radius + self.c.gap_x) * cos, Q15_ONE);
        let at_y = floor_div((self.radius + self.c.gap_y) * sin, Q15_ONE);
        let align = self.align_of(theta);
        let x = match align {
            Align::Start => at_x,
            Align::End => at_x - text.w,
            Align::Middle => at_x - floor_div(text.w, 2),
        };
        let y = if sin >= self.c.anchor {
            at_y
        } else if sin <= -self.c.anchor {
            at_y - text.h
        } else {
            at_y - floor_div(text.h, 2)
        };
        (Area::new(x, y, text.w, text.h), align)
    }

    pub(super) fn legend_on(&self) -> bool {
        self.r.show_legend && !self.r.curves.is_empty()
    }

    fn legend_origin(&self) -> Pt {
        let c = self.c;
        let half_w = floor_div(c.width, 2);
        let half_h = floor_div(c.height, 2);
        Pt {
            x: floor_div((half_w + c.margin_right) * 3, 4),
            y: floor_div(-(half_h + c.margin_top) * 3, 4),
        }
    }

    fn legend_row(&self, index: usize) -> Pt {
        let origin = self.legend_origin();
        Pt {
            x: origin.x,
            y: origin.y + count(index) * self.c.legend_row,
        }
    }

    fn place_label(&self, index: usize) -> (Area, Align, bool) {
        let label = &self.labels[index];
        let text = &self.texts[index];
        let visible = text.w > 0;
        match label.kind {
            LabelKind::Title => (
                Area::new(-floor_div(text.w, 2), self.frame.y - text.h, text.w, text.h),
                Align::Middle,
                visible,
            ),
            LabelKind::Axis => {
                let (area, align) = self.axis_area(label.index, text);
                (area, align, visible)
            }
            LabelKind::Legend => {
                let row = self.legend_row(label.index);
                (
                    Area::new(
                        row.x + self.c.marker + self.c.marker_gap,
                        row.y,
                        text.w,
                        text.h,
                    ),
                    Align::Start,
                    visible && self.legend_on(),
                )
            }
        }
    }

    pub(super) fn place(&mut self) -> Result<(), LayoutError> {
        let c = self.c;
        let half_w = floor_div(c.width, 2);
        let half_h = floor_div(c.height, 2);
        self.frame = Area::new(
            -(half_w + c.margin),
            -(half_h + c.margin_top),
            2 * half_w + c.margin + c.margin_right,
            2 * half_h + c.margin_top + c.margin,
        );
        self.plot = Area::new(-self.extent, -self.extent, 2 * self.extent, 2 * self.extent);
        let mut extent = Extent::default();
        extent.add_area(self.frame);
        extent.add_area(self.plot);
        let placements: Vec<(Area, Align, bool)> = (0..self.labels.len())
            .map(|index| self.place_label(index))
            .collect();
        for &(area, _, shown) in &placements {
            if shown {
                extent.add_area(area);
            }
        }
        self.rects = placements.iter().map(|p| p.0).collect();
        self.aligns = placements.iter().map(|p| p.1).collect();
        self.shown = placements.iter().map(|p| p.2).collect();
        self.curves = self.drawn.iter().map(|&i| self.curve_points(i)).collect();
        for points in &self.curves {
            for &p in points {
                extent.add_point(p);
            }
            if self.r.graticule == Graticule::Circle {
                for b in self.smooth(points) {
                    extent.add_point(b.c1);
                    extent.add_point(b.c2);
                }
            }
        }
        self.markers = if self.legend_on() {
            (0..self.r.curves.len())
                .map(|index| {
                    let row = self.legend_row(index);
                    Area::new(row.x, row.y, c.marker, c.marker)
                })
                .collect()
        } else {
            Vec::new()
        };
        for &marker in &self.markers {
            extent.add_area(marker);
        }
        self.dx = -extent.min_x;
        self.dy = -extent.min_y;
        self.finish(extent)
    }

    pub(super) fn shift(&self, a: Area) -> Area {
        Area::new(a.x + self.dx, a.y + self.dy, a.w, a.h)
    }

    fn finish(&mut self, extent: Extent) -> Result<(), LayoutError> {
        self.canvas = Size {
            w: to_i32(extent.max_x - extent.min_x)?,
            h: to_i32(extent.max_y - extent.min_y)?,
        };
        let mut boxes = vec![self.plot];
        boxes.extend(self.curves.iter().map(|points| bounds_of(points)));
        self.box_rects = boxes
            .into_iter()
            .map(|area| self.shift(area).to_rect())
            .collect::<Result<Vec<Rect>, _>>()?;
        let mut label_rects = Vec::with_capacity(self.labels.len());
        for (area, &shown) in self.rects.iter().zip(&self.shown) {
            label_rects.push(if shown {
                self.shift(*area).to_rect()?
            } else {
                super::ZERO_RECT
            });
        }
        self.label_rects = label_rects;
        self.placed = true;
        Ok(())
    }
}
