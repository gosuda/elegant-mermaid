//! Placement of the gantt boxes and labels: bars, milestones, vertical markers, and the
//! outside-or-inside rule of task labels.

use std::collections::BTreeMap;

use crate::geom::{GeomError, Rect, floor_div};
use crate::measure::Role;
use crate::model::chart::GanttTask;
use crate::scene::Align;

use super::gantt::{
    BoxKind, GanttBox, GanttLabel, GanttPlan, LabelKind, Placed, TICK_FONT, box_id,
};
use super::scale::clamp;
use super::xy::TextBox;
use super::{Area, LayoutError, ZERO_RECT};

impl GanttPlan<'_> {
    fn fit(&self, r: Area) -> Area {
        Area {
            x: clamp(r.x, 0, (self.width - r.w).max(0)),
            y: clamp(r.y, 0, (self.height - r.h).max(0)),
            ..r
        }
    }

    pub(super) fn place(&mut self) -> Result<(), LayoutError> {
        let box_rects = self.place_boxes()?;
        let placed = self.place_labels(box_rects)?;
        self.placed = Some(placed);
        Ok(())
    }

    fn task_area(&self, t: &GanttTask, top: i64) -> Result<Area, LayoutError> {
        let start = self.time_x(t.start)?;
        if t.vert {
            return Ok(Area::new(
                start - floor_div(self.c.vert_w, 2),
                self.c.top_pad,
                self.c.vert_w,
                self.rows * self.pitch,
            ));
        }
        if t.milestone {
            let end = self.time_x(t.end)?;
            return Ok(Area::new(
                start + floor_div(end - start, 2) - floor_div(self.c.bar_h, 2),
                top,
                self.c.bar_h,
                self.c.bar_h,
            ));
        }
        let end = self.time_x(t.render_end)?;
        Ok(Area::new(
            start,
            top,
            (end - start).max(0) + self.c.edge,
            self.c.bar_h,
        ))
    }

    fn box_area(&self, b: &GanttBox) -> Result<Area, LayoutError> {
        let top = b.row.map_or(self.c.top_pad, |row| self.row_top(row));
        match b.kind {
            BoxKind::Plot => Ok(self.plot),
            BoxKind::Section => Ok(Area::new(0, top, self.width, self.pitch)),
            BoxKind::Task | BoxKind::Vert => {
                let task = self.g.tasks.get(b.index).ok_or(GeomError::Domain)?;
                let area = self.task_area(task, top)?;
                Ok(Area {
                    x: clamp(area.x, 0, (self.width - area.w).max(0)),
                    ..area
                })
            }
        }
    }

    fn place_boxes(&self) -> Result<Vec<Rect>, LayoutError> {
        self.boxes
            .iter()
            .map(|b| self.box_area(b)?.to_rect())
            .collect()
    }

    fn place_labels(&self, box_rects: Vec<Rect>) -> Result<Placed, LayoutError> {
        let n = self.labels.len();
        let mut placed = Placed {
            box_rects,
            label_rects: vec![ZERO_RECT; n],
            label_lines: vec![Vec::new(); n],
            shown: vec![false; n],
            aligns: vec![Align::Middle; n],
            chips: vec![false; n],
        };
        let box_of: BTreeMap<&str, usize> = self
            .boxes
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id.as_str(), i))
            .collect();
        for (i, label) in self.labels.iter().enumerate() {
            let (area, align) = self.label_area(i, label, &box_of, &placed.box_rects)?;
            let area = self.fit(area);
            if self.overlaps_shown(i, area, &placed) {
                continue;
            }
            placed.label_rects[i] = area.to_rect()?;
            placed.aligns[i] = align;
            placed.shown[i] = true;
            placed.chips[i] = self.needs_chip(label, align);
            placed.label_lines[i] = self.texts[i]
                .lines
                .iter()
                .map(|line| line.text.clone())
                .collect();
        }
        Ok(placed)
    }

    fn overlaps_shown(&self, i: usize, r: Area, placed: &Placed) -> bool {
        if !self.cell {
            return false;
        }
        let edge = self.c.edge;
        (0..i).filter(|&j| placed.shown[j]).any(|j| {
            let b = placed.label_rects[j];
            let (bx, by) = (i64::from(b.x), i64::from(b.y));
            let (bw, bh) = (i64::from(b.w), i64::from(b.h));
            r.x < bx + bw + edge && bx < r.x + r.w + edge && r.y < by + bh && by < r.y + r.h
        })
    }

    fn label_area(
        &self,
        i: usize,
        l: &GanttLabel,
        box_of: &BTreeMap<&str, usize>,
        box_rects: &[Rect],
    ) -> Result<(Area, Align), LayoutError> {
        let t = &self.texts[i];
        let lookup = |kind: BoxKind| {
            box_of
                .get(box_id(kind, l.index).as_str())
                .copied()
                .ok_or(GeomError::Domain)
        };
        match l.kind {
            LabelKind::Title => {
                let half = floor_div(t.w, 2);
                let centre = clamp(floor_div(self.width, 2), half, self.width - half);
                Ok((
                    Area::new(centre - half, self.c.title_pad, t.w, t.h),
                    Align::Middle,
                ))
            }
            LabelKind::Section => {
                let row = self.boxes[lookup(BoxKind::Section)?].row.unwrap_or(0);
                let y = self.row_top(row) + floor_div(self.c.bar_h - t.h, 2);
                Ok((Area::new(self.c.section_pad, y, t.w, t.h), Align::Start))
            }
            LabelKind::Task => {
                let rect = *box_rects
                    .get(lookup(BoxKind::Task)?)
                    .ok_or(GeomError::Domain)?;
                self.task_label_area(l, t, rect)
            }
            LabelKind::Tick | LabelKind::TopTick => {
                let tick = *self.ticks.get(l.index).ok_or(GeomError::Domain)?;
                let x = self.time_x(tick)?;
                let y = if l.kind == LabelKind::TopTick {
                    self.top_axis_y() - self.c.tick_len - self.c.tick_gap - t.h
                } else {
                    self.axis_y() + self.c.tick_len + self.c.edge + self.c.tick_gap
                };
                Ok((Area::new(x - floor_div(t.w, 2), y, t.w, t.h), Align::Middle))
            }
        }
    }

    fn task_label_area(
        &self,
        l: &GanttLabel,
        t: &TextBox,
        rect: Rect,
    ) -> Result<(Area, Align), LayoutError> {
        let task = self.g.tasks.get(l.index).ok_or(GeomError::Domain)?;
        let (bx, by, bw) = (i64::from(rect.x), i64::from(rect.y), i64::from(rect.w));
        let (x0, x1) = (bx, bx + bw);
        let centred = x0 + floor_div(bw - t.w, 2);
        if task.vert {
            let below = self.axis_y()
                + self.c.tick_len
                + self.c.edge
                + self.c.tick_gap
                + self.line_height(Role::Label, TICK_FONT)
                + self.c.tick_gap;
            return Ok((Area::new(centred, below, t.w, t.h), Align::Middle));
        }
        let y = by + floor_div(self.c.bar_h - t.h, 2);
        let inside = Area::new(centred, y, t.w, t.h);
        if !self.cell && !task.milestone && t.w <= bw {
            return Ok((inside, Align::Middle));
        }
        let left = Area::new(x0 - self.c.label_gap - t.w, y, t.w, t.h);
        let right = Area::new(x1 + self.c.label_gap, y, t.w, t.h);
        let prefer_left = 2 * (x1 + t.w) + self.c.gutter > 2 * self.width;
        let choice = if prefer_left && left.x >= 0 {
            (left, Align::End)
        } else if right.x + right.w <= self.width {
            (right, Align::Start)
        } else if left.x >= 0 {
            (left, Align::End)
        } else if self.cell {
            (Area::new(x0, by + self.c.bar_h, t.w, t.h), Align::Start)
        } else {
            (inside, Align::Middle)
        };
        Ok(choice)
    }

    fn needs_chip(&self, l: &GanttLabel, align: Align) -> bool {
        if l.kind != LabelKind::Task || align != Align::Middle {
            return false;
        }
        self.g.tasks.get(l.index).is_some_and(|t| {
            !t.vert && !t.milestone && !t.crit && !t.done && !t.active && t.section.is_some()
        })
    }
}
