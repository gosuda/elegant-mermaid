//! Bands, plot rectangle, tiles, and point centres of the quadrant plan.

use crate::geom::floor_div;
use crate::measure::Role;

use super::quadrant::{MIN_PLOT, QuadPlan, SCALE, Spot, units_x, units_y};
use super::quadrant_spec::{LabelKind, NO_POINT_RADIUS, QuadrantPoint};
use super::xy::TextBox;
use super::{Area, LayoutError};

fn px(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(i32::MAX)
}

impl QuadPlan<'_> {
    fn measure_kinds(
        &mut self,
        target: i64,
        kinds: &[LabelKind],
    ) -> Result<(i64, i64, bool), LayoutError> {
        let (mut widest, mut tallest, mut found) = (0, 0, false);
        for kind in kinds {
            let Some(i) = self.find(*kind) else {
                continue;
            };
            let text = self.measure_at(i, target)?;
            widest = widest.max(text.w);
            tallest = tallest.max(text.h);
            found = true;
            self.texts[i] = text;
        }
        Ok((widest, tallest, found))
    }

    fn arrange_title(&mut self) -> Result<i64, LayoutError> {
        let target = self.c.width - 2 * self.c.pad_x;
        let (_, tallest, found) = self.measure_kinds(target, &[LabelKind::Title])?;
        if !found {
            return Ok(0);
        }
        let lh = self.line_height(Role::Title, px(self.c.title_font_px));
        let pad = units_y(self.profile, self.c.title_pad_px);
        Ok((self.c.title_band + tallest - lh).max(pad + tallest))
    }

    fn arrange_left(&mut self) -> Result<i64, LayoutError> {
        let pad = units_x(self.profile, self.c.y_pad_px);
        let target = (floor_div(self.c.width, 2) - 2 * pad - 2 * self.c.pad_x).max(1);
        let (widest, _, found) =
            self.measure_kinds(target, &[LabelKind::YBottom, LabelKind::YTop])?;
        if !found {
            return Ok(0);
        }
        Ok(self.c.y_band.max(widest + 2 * pad))
    }

    fn arrange_bottom(&mut self, plot_w: i64) -> Result<i64, LayoutError> {
        let both = self.find(LabelKind::XLeft).is_some() && self.find(LabelKind::XRight).is_some();
        let target = if both { floor_div(plot_w, 2) } else { plot_w };
        let (_, tallest, found) =
            self.measure_kinds(target.max(1), &[LabelKind::XLeft, LabelKind::XRight])?;
        if !found {
            return Ok(0);
        }
        let lh = self.line_height(Role::Label, px(self.c.x_font_px));
        let pad = units_y(self.profile, self.c.x_pad_px);
        Ok((self.c.x_band + tallest - lh).max(pad + tallest))
    }

    pub(super) fn arrange(&mut self) -> Result<(), LayoutError> {
        let c = self.c;
        self.texts = vec![TextBox::default(); self.specs.len()];
        let title_band = self.arrange_title()?;
        let left_band = self.arrange_left()?;
        let plot_w = (c.width - 2 * c.pad_x - left_band).max(MIN_PLOT);
        let bottom_band = self.arrange_bottom(plot_w)?;
        let plot_h = (c.height - 2 * c.pad_y - title_band - bottom_band).max(MIN_PLOT);
        self.width = 2 * c.pad_x + left_band + plot_w;
        self.height = 2 * c.pad_y + title_band + plot_h + bottom_band;
        self.plot = Area::new(c.pad_x + left_band, c.pad_y + title_band, plot_w, plot_h);
        self.arrange_tiles();
        self.arrange_points();
        Ok(())
    }

    fn arrange_tiles(&mut self) {
        let (pl, e) = (self.plot, self.c.edge);
        let (left_w, top_h) = (floor_div(pl.w, 2), floor_div(pl.h, 2));
        let cols = [(pl.x, pl.x + left_w), (pl.x + left_w, pl.x + pl.w)];
        let rows = [(pl.y, pl.y + top_h), (pl.y + top_h, pl.y + pl.h)];
        for (i, (col, row)) in [(1, 0), (0, 0), (0, 1), (1, 1)].into_iter().enumerate() {
            let ((left, right_edge), (top, bottom_edge)) = (cols[col], rows[row]);
            self.tiles[i] = Area::new(left, top, right_edge - left, bottom_edge - top);
            let right = if col == 1 { right_edge - e } else { right_edge };
            let bottom = if row == 1 {
                bottom_edge - e
            } else {
                bottom_edge
            };
            self.inner[i] = Area::new(
                left + e,
                top + e,
                (right - left - e).max(0),
                (bottom - top - e).max(0),
            );
        }
    }

    fn radius_of(&self, point: &QuadrantPoint) -> Spot {
        if point.radius == NO_POINT_RADIUS {
            return Spot {
                x: self.c.radius_x,
                y: self.c.radius_y,
            };
        }
        Spot {
            x: units_x(self.profile, point.radius),
            y: units_y(self.profile, point.radius),
        }
    }

    fn arrange_points(&mut self) {
        let (pl, e) = (self.plot, self.c.edge);
        let (span_w, span_h) = ((pl.w - 3 * e).max(0), (pl.h - 3 * e).max(0));
        for point in &self.q.points {
            let centre = Spot {
                x: pl.x + e + floor_div(point.x * span_w, SCALE),
                y: pl.y + e + span_h - floor_div(point.y * span_h, SCALE),
            };
            let radius = self.radius_of(point);
            self.centres.push(centre);
            self.radii.push(radius);
            self.point_boxes.push(self.marker_box(centre, radius));
        }
    }

    fn marker_box(&self, c: Spot, r: Spot) -> Area {
        if !self.cell {
            return Area::new(c.x - r.x, c.y - r.y, 2 * r.x, 2 * r.y).within(self.plot);
        }
        if r.x <= 1 && r.y <= 1 {
            return Area::new(c.x, c.y, 1, 1);
        }
        Area::new(c.x - r.x, c.y - r.y, 2 * r.x + 1, 2 * r.y + 1).within(self.plot)
    }
}
