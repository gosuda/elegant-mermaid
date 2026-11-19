//! Space allocation of the xychart plan: title, axes, legend, and the plot rectangle.

use crate::geom::floor_div;
use crate::model::chart::PlotKind;

use super::Area;
use super::xy::{AxisId, XyPlan};
use super::xy_axis::{Axis, BandSpace};
use super::xy_spec::LabelKind;

const PERCENT: i64 = 100;
const PERMILLE: i64 = 1000;

struct LegendSize {
    w: i64,
    h: i64,
    beside: bool,
}

impl XyPlan<'_> {
    pub(crate) fn has_bars(&self) -> bool {
        self.xy.plots.iter().any(|plot| plot.kind == PlotKind::Bar)
    }

    pub(crate) fn title_block(&self, index: usize, pad: i64) -> i64 {
        self.texts[index].h + 2 * pad
    }

    fn title_space(&mut self, avail_h: i64) -> i64 {
        let Some(i) = self.find(LabelKind::Title) else {
            return 0;
        };
        let need = self.title_block(i, self.c.title_pad);
        self.title_shown = need <= avail_h;
        if self.title_shown { need } else { 0 }
    }

    fn side_title_space(&mut self, avail_h: i64) -> i64 {
        let kind = if self.horizontal() {
            LabelKind::XTitle
        } else {
            LabelKind::YTitle
        };
        let Some(i) = self.find(kind) else {
            return 0;
        };
        let need = self.title_block(i, self.c.axis_title_pad);
        self.side_title = Some(i);
        self.side_shown = need <= avail_h;
        if self.side_shown { need } else { 0 }
    }

    fn horizontal_space(&self, a: &mut Axis, avail_w: i64, avail_h: i64) -> BandSpace {
        let c = self.c;
        let mut space = BandSpace {
            w: avail_w,
            ..BandSpace::default()
        };
        let mut h = avail_h;
        if h > c.axis_line {
            h -= c.axis_line;
            space.line = c.axis_line;
        }
        if a.show_labels {
            (a.label_w, a.label_h) = self.tick_extent(a.tick_kind);
            a.outer = floor_div(a.label_w, 2).min(floor_div(c.outer_max * avail_w, PERMILLE));
            let need = a.label_h + 2 * c.pad_y;
            if need <= h {
                h -= need;
                space.show_label = true;
            }
        }
        if h >= c.tick_len {
            h -= c.tick_len;
            space.tick = c.tick_len;
        }
        if let Some(i) = self.find(a.title_kind) {
            let need = self.title_block(i, c.axis_title_pad);
            if need <= h {
                h -= need;
                space.title = need;
            }
        }
        space.h = avail_h - h;
        space
    }

    fn vertical_space(&self, a: &mut Axis, avail_w: i64, avail_h: i64) -> BandSpace {
        let c = self.c;
        let mut space = BandSpace {
            h: avail_h,
            ..BandSpace::default()
        };
        let mut w = avail_w;
        if w > c.axis_line {
            w -= c.axis_line;
            space.line = c.axis_line;
        }
        if a.show_labels {
            (a.label_w, a.label_h) = self.tick_extent(a.tick_kind);
            a.outer = floor_div(a.label_h, 2).min(floor_div(c.outer_max * avail_h, PERMILLE));
            let need = a.label_w + 2 * c.pad_x;
            if need <= w {
                w -= need;
                space.show_label = true;
            }
        }
        if w >= c.tick_len {
            w -= c.tick_len;
            space.tick = c.tick_len;
        }
        space.w = avail_w - w;
        space
    }

    fn legend_size(&mut self, avail_w: i64, avail_h: i64) -> LegendSize {
        let mut widest = 0;
        let mut line_height = 0;
        let mut rows = 0;
        for (spec, text) in self.specs.iter().zip(&self.texts) {
            if spec.kind != LabelKind::Legend {
                continue;
            }
            widest = widest.max(text.w);
            line_height = line_height.max(text.h);
            rows += 1;
        }
        self.legend_lh = line_height;
        self.legend_rows = rows;
        if rows == 0 {
            return LegendSize {
                w: 0,
                h: 0,
                beside: false,
            };
        }
        let c = self.c;
        let w = 2 * c.legend_pad + c.legend_marker + c.marker_gap + widest;
        let h = 2 * c.legend_pad + rows * line_height + (rows - 1) * c.item_gap;
        LegendSize {
            w,
            h,
            beside: w <= avail_w && h <= avail_h,
        }
    }

    fn legend_beside(&self, w: i64, h: i64) -> Area {
        let pl = self.plot;
        Area::new(pl.x + pl.w, pl.y + floor_div(pl.h - h, 2).max(0), w, h)
    }

    fn legend_overlay(&self, w: i64, h: i64) -> Area {
        let pl = self.plot;
        self.fit(Area::new(pl.x + pl.w - w, pl.y, w, h))
    }

    pub(crate) fn arrange(&mut self) {
        let c = self.c;
        self.width = c.width;
        self.height = c.height;
        let mut chart_w = floor_div(self.width * c.reserved, PERCENT);
        let mut chart_h = floor_div(self.height * c.reserved, PERCENT);
        let (mut avail_w, mut avail_h) = (self.width - chart_w, self.height - chart_h);
        self.title_h = self.title_space(avail_h);
        avail_h -= self.title_h;
        let side_h = self.side_title_space(avail_h);
        avail_h -= side_h;
        let top = self.title_h + side_h;
        let (plot_x, plot_y) = if self.horizontal() {
            let x = self.with_axis(AxisId::X, |p, a| p.vertical_space(a, avail_w, avail_h));
            self.x.space = x;
            avail_w -= x.w;
            let y = self.with_axis(AxisId::Y, |p, a| p.horizontal_space(a, avail_w, avail_h));
            self.y.space = y;
            avail_h -= y.h;
            (x.w, top + y.h)
        } else {
            let x = self.with_axis(AxisId::X, |p, a| p.horizontal_space(a, avail_w, avail_h));
            self.x.space = x;
            avail_h -= x.h;
            let y = self.with_axis(AxisId::Y, |p, a| p.vertical_space(a, avail_w, avail_h));
            self.y.space = y;
            avail_w -= y.w;
            (y.w, top)
        };
        let legend = self.legend_size(avail_w, chart_h);
        self.legend_on = self.legend_rows > 0;
        if legend.beside {
            avail_w -= legend.w;
        }
        chart_w = (chart_w + avail_w.max(0)).max(c.edge);
        chart_h = (chart_h + avail_h.max(0)).max(c.edge);
        self.plot = Area::new(
            plot_x.min(self.width - chart_w).max(0),
            plot_y.min(self.height - chart_h).max(0),
            chart_w,
            chart_h,
        );
        self.legend = if legend.beside {
            self.legend_beside(legend.w, legend.h)
        } else {
            self.legend_overlay(legend.w, legend.h)
        };
        self.set_areas(top);
    }

    fn set_areas(&mut self, top: i64) {
        let pl = self.plot;
        if self.horizontal() {
            self.x.area = Area::new(0, pl.y, self.x.space.w, pl.h);
            self.y.area = Area::new(pl.x, top, pl.w, self.y.space.h);
            (self.x.r0, self.x.r1) = (pl.y, pl.y + pl.h);
            (self.y.r0, self.y.r1) = (pl.x, pl.x + pl.w);
        } else {
            self.x.area = Area::new(pl.x, pl.y + pl.h, pl.w, self.x.space.h);
            self.y.area = Area::new(0, pl.y, self.y.space.w, pl.h);
            (self.x.r0, self.x.r1) = (pl.x, pl.x + pl.w);
            (self.y.r0, self.y.r1) = (pl.y, pl.y + pl.h);
        }
        if self.has_bars() {
            self.x.raise_outer_for_bars(self.c.bar_ratio);
        }
    }
}
