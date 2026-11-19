//! Label placement of the quadrant plan.
//!
//! Axis labels and the title have fixed positions. In the cell profile a tile label or a
//! point label takes the first free candidate, so no label meets a border, a divider, a
//! marker, or another label; the vector profile keeps one position per label.

use crate::geom::floor_div;
use crate::scene::Align;

use super::quadrant::{QuadPlan, Spot, units_x, units_y};
use super::quadrant_spec::{LabelKind, Placed};
use super::scale::clamp;
use super::xy::TextBox;
use super::{Area, LayoutError, ZERO_RECT};

#[derive(Debug, Clone, Copy)]
struct Candidate {
    r: Area,
    align: Align,
}

const GROUPS: [&[LabelKind]; 3] = [
    &[
        LabelKind::Title,
        LabelKind::XLeft,
        LabelKind::XRight,
        LabelKind::YBottom,
        LabelKind::YTop,
    ],
    &[LabelKind::Tile],
    &[LabelKind::Point],
];

fn spread(limit: i64) -> Vec<i64> {
    let mut out = vec![0];
    for d in 1..=limit {
        out.push(d);
        out.push(-d);
    }
    out
}

impl Area {
    pub(super) fn overlaps(&self, o: &Area) -> bool {
        self.w > 0
            && self.h > 0
            && o.w > 0
            && o.h > 0
            && self.x < o.x + o.w
            && o.x < self.x + self.w
            && self.y < o.y + o.h
            && o.y < self.y + self.h
    }

    pub(super) fn inside(&self, outer: &Area) -> bool {
        self.x >= outer.x
            && self.y >= outer.y
            && self.x + self.w <= outer.x + outer.w
            && self.y + self.h <= outer.y + outer.h
    }

    pub(super) fn within(self, outer: Area) -> Area {
        let (x0, y0) = (self.x.max(outer.x), self.y.max(outer.y));
        let x1 = (self.x + self.w).min(outer.x + outer.w);
        let y1 = (self.y + self.h).min(outer.y + outer.h);
        Area::new(x0, y0, (x1 - x0).max(0), (y1 - y0).max(0))
    }
}

impl QuadPlan<'_> {
    fn fit(&self, r: Area) -> Area {
        Area::new(
            clamp(r.x, 0, (self.width - r.w).max(0)),
            clamp(r.y, 0, (self.height - r.h).max(0)),
            r.w,
            r.h,
        )
    }

    fn inside_plot(&self, r: Area) -> Area {
        let pl = self.plot;
        Area::new(
            clamp(r.x, pl.x, (pl.x + pl.w - r.w).max(pl.x)),
            clamp(r.y, pl.y, (pl.y + pl.h - r.h).max(pl.y)),
            r.w,
            r.h,
        )
    }

    fn interior(&self) -> Area {
        let (pl, e) = (self.plot, self.c.edge);
        Area::new(
            pl.x + e,
            pl.y + e,
            (pl.w - 2 * e).max(0),
            (pl.h - 2 * e).max(0),
        )
    }

    fn obstacles(&self) -> Vec<Area> {
        if !self.cell {
            return Vec::new();
        }
        let pl = self.plot;
        let mut out = vec![
            Area::new(self.tiles[0].x, pl.y, 1, pl.h),
            Area::new(pl.x, self.tiles[2].y, pl.w, 1),
        ];
        out.extend(self.point_boxes.iter().copied());
        out
    }

    fn free(&self, r: &Area) -> bool {
        r.inside(&self.interior()) && !self.taken.iter().any(|t| r.overlaps(t))
    }

    fn search(&self, cands: &[Candidate]) -> (Candidate, bool) {
        if self.cell
            && let Some(found) = cands.iter().find(|c| self.free(&c.r))
        {
            return (*found, true);
        }
        (cands[0], !self.cell)
    }

    pub(super) fn place(&mut self) -> Result<(), LayoutError> {
        let n = self.specs.len();
        let mut placed = Placed {
            box_rects: Vec::new(),
            label_rects: vec![ZERO_RECT; n],
            label_lines: vec![Vec::new(); n],
            aligns: vec![Align::Start; n],
        };
        self.taken = self.obstacles();
        let kinds: Vec<LabelKind> = self.specs.iter().map(|spec| spec.kind).collect();
        for group in GROUPS {
            for (i, kind) in kinds.iter().enumerate() {
                if group.contains(kind) {
                    self.place_label(i, &mut placed)?;
                }
            }
        }
        placed.box_rects = self
            .boxes
            .iter()
            .map(|b| self.box_rect(b).to_rect())
            .collect::<Result<_, _>>()?;
        self.placed = Some(placed);
        Ok(())
    }

    fn place_label(&mut self, i: usize, placed: &mut Placed) -> Result<(), LayoutError> {
        let c = self.candidate_for(i)?;
        placed.label_rects[i] = c.r.to_rect()?;
        placed.aligns[i] = c.align;
        placed.label_lines[i] = self.texts[i]
            .lines
            .iter()
            .map(|line| line.text.clone())
            .collect();
        self.taken.push(c.r);
        Ok(())
    }

    fn candidate_for(&mut self, i: usize) -> Result<Candidate, LayoutError> {
        match self.specs[i].kind {
            LabelKind::Title => Ok(self.title_candidate(i)),
            LabelKind::XLeft | LabelKind::XRight => Ok(self.bottom_candidate(i)),
            LabelKind::YBottom | LabelKind::YTop => Ok(self.left_candidate(i)),
            LabelKind::Tile => self.tile_candidate(i),
            LabelKind::Point => self.point_candidate(i),
        }
    }

    fn title_candidate(&self, i: usize) -> Candidate {
        let t = &self.texts[i];
        let y = units_y(self.profile, self.c.title_pad_px);
        Candidate {
            r: self.fit(Area::new(floor_div(self.width - t.w, 2), y, t.w, t.h)),
            align: Align::Middle,
        }
    }

    fn bottom_candidate(&self, i: usize) -> Candidate {
        let (t, pl) = (&self.texts[i], self.plot);
        let y = pl.y + pl.h + units_y(self.profile, self.c.x_pad_px);
        let both = self.find(LabelKind::XLeft).is_some() && self.find(LabelKind::XRight).is_some();
        if !both {
            return Candidate {
                r: self.fit(Area::new(pl.x, y, t.w, t.h)),
                align: Align::Start,
            };
        }
        let left_w = floor_div(pl.w, 2);
        let centre = if self.specs[i].kind == LabelKind::XRight {
            pl.x + left_w + floor_div(pl.w - left_w, 2)
        } else {
            pl.x + floor_div(left_w, 2)
        };
        Candidate {
            r: self.fit(Area::new(centre - floor_div(t.w, 2), y, t.w, t.h)),
            align: Align::Middle,
        }
    }

    fn left_candidate(&self, i: usize) -> Candidate {
        let (t, pl) = (&self.texts[i], self.plot);
        let x = pl.x - units_x(self.profile, self.c.y_pad_px) - t.w;
        let both = self.find(LabelKind::YBottom).is_some() && self.find(LabelKind::YTop).is_some();
        let bottom = self.specs[i].kind == LabelKind::YBottom;
        let y = match (both, bottom) {
            (true, true) => pl.y + pl.h - floor_div(pl.h, 4) - floor_div(t.h, 2),
            (true, false) => pl.y + floor_div(pl.h, 4) - floor_div(t.h, 2),
            (false, true) => pl.y + pl.h - t.h,
            (false, false) => pl.y,
        };
        Candidate {
            r: self.fit(Area::new(x, y, t.w, t.h)),
            align: Align::End,
        }
    }

    fn tile_candidate(&mut self, i: usize) -> Result<Candidate, LayoutError> {
        let inner = self.inner[self.specs[i].index];
        let t = self.measure_at(i, (inner.w - 2 * self.c.pad_x).max(1))?;
        let x = inner.x + floor_div(inner.w - t.w, 2).max(0);
        let y = if self.q.points.is_empty() {
            inner.y + floor_div(inner.h - t.h, 2).max(0)
        } else {
            inner.y + self.c.top_pad
        };
        let cands: Vec<Candidate> = spread(inner.h)
            .into_iter()
            .map(|dy| Candidate {
                r: Area::new(x, y + dy, t.w, t.h),
                align: Align::Middle,
            })
            .collect();
        self.texts[i] = t;
        Ok(self.search(&cands).0)
    }

    fn column(&self, centre: Spot) -> Area {
        if centre.x >= self.tiles[0].x {
            self.inner[0]
        } else {
            self.inner[1]
        }
    }

    fn point_candidates(&self, centre: Spot, r: Spot, t: &TextBox) -> Vec<Candidate> {
        let right = centre.x + r.x + self.c.text_pad;
        let top = centre.y - floor_div(t.h, 2);
        if !self.cell {
            return vec![Candidate {
                r: self.inside_plot(Area::new(right, top, t.w, t.h)),
                align: Align::Start,
            }];
        }
        let left = centre.x - (r.x + self.c.text_pad - 1) - t.w;
        let column = self.column(centre);
        let fitted = clamp(
            centre.x - floor_div(t.w, 2),
            column.x,
            (column.x + column.w - t.w).max(column.x),
        );
        let offsets = spread(self.plot.h);
        let mut out = Vec::new();
        for dy in &offsets {
            out.push(Candidate {
                r: Area::new(right, top + dy, t.w, t.h),
                align: Align::Start,
            });
            out.push(Candidate {
                r: Area::new(left, top + dy, t.w, t.h),
                align: Align::End,
            });
        }
        out.extend(offsets.iter().map(|dy| Candidate {
            r: Area::new(fitted, top + dy, t.w, t.h),
            align: Align::Middle,
        }));
        out
    }

    fn point_wrap(&self, centre: Spot) -> i64 {
        self.column(centre).w.max(2)
    }

    fn try_point(
        &mut self,
        i: usize,
        centre: Spot,
        r: Spot,
        target: i64,
    ) -> Result<(Candidate, bool), LayoutError> {
        let t = self.measure_at(i, target)?;
        let found = self.search(&self.point_candidates(centre, r, &t));
        self.texts[i] = t;
        Ok(found)
    }

    fn point_candidate(&mut self, i: usize) -> Result<Candidate, LayoutError> {
        let index = self.specs[i].index;
        let (centre, r) = (self.centres[index], self.radii[index]);
        let (first, found) = self.try_point(i, centre, r, 0)?;
        if found {
            return Ok(first);
        }
        Ok(self.try_point(i, centre, r, self.point_wrap(centre))?.0)
    }
}
