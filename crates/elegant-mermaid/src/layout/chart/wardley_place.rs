//! Label placement of the Wardley plan. A label never moves to avoid a collision.

use crate::geom::floor_div;
use crate::measure::Role;
use crate::scene::Align;

use super::wardley::{Kind, Spec, WardleyNode};
use super::wardley_plan::{Plan, Pt};
use super::xy::TextBox;
use super::{Area, LayoutError, ZERO_RECT};

struct Placed {
    area: Area,
    align: Align,
}

fn shown_at(area: Area, align: Align) -> Option<Placed> {
    Some(Placed { area, align })
}

fn at_box(x: i64, y: i64, t: &TextBox) -> Area {
    Area::new(x, y, t.w, t.h)
}

fn centred_at(at: Pt, t: &TextBox) -> Option<Placed> {
    shown_at(
        at_box(at.x - floor_div(t.w, 2), at.y - floor_div(t.h, 2), t),
        Align::Middle,
    )
}

impl Plan<'_> {
    pub(super) fn place_labels(&mut self) -> Result<(), LayoutError> {
        let n = self.specs.len();
        self.rects = vec![ZERO_RECT; n];
        self.lines = vec![Vec::new(); n];
        self.aligns = vec![Align::Start; n];
        self.shown = vec![false; n];
        self.layout_box();
        for i in 0..n {
            let spec = &self.specs[i];
            if spec.text.is_empty() {
                continue;
            }
            let Some(placed) = self.label_area(i, spec) else {
                continue;
            };
            self.keep(i, self.fit_canvas(placed.area), placed.align)?;
        }
        Ok(())
    }

    fn keep(&mut self, i: usize, area: Area, align: Align) -> Result<(), LayoutError> {
        self.rects[i] = area.to_rect()?;
        self.aligns[i] = align;
        self.shown[i] = true;
        self.lines[i] = self.texts[i].lines.iter().map(|l| l.text.clone()).collect();
        Ok(())
    }

    fn label_area(&self, i: usize, spec: &Spec) -> Option<Placed> {
        let t = &self.texts[i];
        match spec.kind {
            Kind::Title | Kind::AxisX | Kind::AxisY | Kind::Stage => self.chrome_label(spec, t),
            Kind::Node | Kind::Link | Kind::Note => self.map_label(spec, t),
            Kind::Number | Kind::Annotation => self.annotation_label(spec, t),
            Kind::Accelerator | Kind::Deaccelerator => self.force_label(spec, t),
        }
    }

    fn chrome_label(&self, spec: &Spec, t: &TextBox) -> Option<Placed> {
        let plot = self.plot;
        let centred = plot.x + floor_div(plot.w - t.w, 2);
        match spec.kind {
            Kind::Title => shown_at(
                at_box(centred, floor_div(plot.y - t.h, 2), t),
                Align::Middle,
            ),
            Kind::AxisX => shown_at(at_box(centred, self.axis_y(), t), Align::Middle),
            Kind::AxisY => shown_at(
                at_box(plot.x, plot.y - t.h - self.c.axis_gap, t),
                Align::Start,
            ),
            _ => self.stage_label(spec.index, t),
        }
    }

    fn map_label(&self, spec: &Spec, t: &TextBox) -> Option<Placed> {
        match spec.kind {
            Kind::Node => self.node_label(spec.index, t),
            Kind::Link => self.link_label(spec.index, t),
            _ => {
                let at = self.notes[spec.index];
                shown_at(at_box(at.x, at.y - t.h, t), Align::Start)
            }
        }
    }

    fn annotation_label(&self, spec: &Spec, t: &TextBox) -> Option<Placed> {
        if spec.kind == Kind::Number {
            return centred_at(self.points[spec.index], t);
        }
        self.annotation_text(spec.index, t)
    }

    fn stage_height(&self) -> i64 {
        let size = i32::try_from(self.c.axis_size / 64).unwrap_or(0);
        self.line_height(Role::Label, size)
    }

    fn axis_y(&self) -> i64 {
        self.plot.y + self.plot.h + 2 * self.c.stage_gap + self.stage_height()
    }

    fn stage_label(&self, k: usize, t: &TextBox) -> Option<Placed> {
        let (start, end) = self.stage_span(k);
        shown_at(
            at_box(
                floor_div(start + end - t.w, 2),
                self.plot.y + self.plot.h + self.c.stage_gap,
                t,
            ),
            Align::Middle,
        )
    }

    fn offset(&self, n: &WardleyNode) -> Pt {
        if self.cell {
            return Pt {
                x: floor_div(n.offset_x, 8),
                y: floor_div(n.offset_y, 16),
            };
        }
        Pt {
            x: n.offset_x * 64,
            y: n.offset_y * 64,
        }
    }

    fn node_label(&self, k: usize, t: &TextBox) -> Option<Placed> {
        let n = &self.w.nodes[k];
        let at = self.pos[k];
        if n.has_offset {
            let off = self.offset(n);
            return centred_at(
                Pt {
                    x: at.x + off.x,
                    y: at.y + off.y,
                },
                t,
            );
        }
        if n.anchor {
            return centred_at(at, t);
        }
        shown_at(
            at_box(at.x + self.reach(n) + self.c.label_gap, at.y - t.h, t),
            Align::Start,
        )
    }

    fn link_label(&self, k: usize, t: &TextBox) -> Option<Placed> {
        let l = &self.w.links[k];
        let (a, b) = (self.pos[l.from], self.pos[l.to]);
        let mid = Pt {
            x: floor_div(a.x + b.x, 2),
            y: floor_div(a.y + b.y, 2),
        };
        let (dx, dy) = (b.x - a.x, b.y - a.y);
        let gap = self.c.link_label_gap;
        if dy == 0 {
            return shown_at(
                at_box(mid.x - floor_div(t.w, 2), mid.y - gap - t.h, t),
                Align::Middle,
            );
        }
        if dx == 0 {
            return shown_at(
                at_box(mid.x + gap, mid.y - floor_div(t.h, 2), t),
                Align::Start,
            );
        }
        if (dx < 0) == (dy < 0) {
            return shown_at(at_box(mid.x + gap, mid.y - gap - t.h, t), Align::Start);
        }
        shown_at(
            at_box(mid.x - gap - t.w, mid.y - gap - t.h, t),
            Align::Start,
        )
    }

    fn annotation_text(&self, k: usize, t: &TextBox) -> Option<Placed> {
        if !self.w.shows_box() {
            let at = self.points[k];
            return shown_at(
                at_box(
                    at.x + self.c.annotation_radius + self.c.label_gap,
                    at.y - floor_div(t.h, 2),
                    t,
                ),
                Align::Start,
            );
        }
        let above: i64 = self
            .boxed
            .iter()
            .take_while(|&&shown| shown != k)
            .map(|&shown| self.text_of_annotation(shown).h)
            .sum();
        shown_at(
            at_box(
                self.box_area.x + self.c.box_pad,
                self.box_area.y + self.c.box_pad + above,
                t,
            ),
            Align::Start,
        )
    }

    fn text_of_annotation(&self, k: usize) -> TextBox {
        self.specs
            .iter()
            .zip(&self.texts)
            .find(|(s, _)| s.kind == Kind::Annotation && s.index == k)
            .map(|(_, t)| t.clone())
            .unwrap_or_default()
    }

    fn force_label(&self, spec: &Spec, t: &TextBox) -> Option<Placed> {
        let areas = if spec.kind == Kind::Deaccelerator {
            &self.decels
        } else {
            &self.accels
        };
        let f = areas[spec.index];
        shown_at(
            at_box(
                f.x + floor_div(f.w - t.w, 2),
                f.y + f.h + self.c.link_label_gap,
                t,
            ),
            Align::Middle,
        )
    }

    fn layout_box(&mut self) {
        let Some(point) = self.w.box_point.filter(|_| self.w.shows_box()) else {
            return;
        };
        let (mut w, mut h) = (0, 0);
        for &k in &self.boxed {
            let t = self.text_of_annotation(k);
            w = w.max(t.w);
            h += t.h;
        }
        let at = self.project(point.x, point.y);
        let pad = self.c.box_pad;
        self.box_area = self.fit_plot(Area::new(at.x, at.y, w + 2 * pad, h + 2 * pad));
    }
}
