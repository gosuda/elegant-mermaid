//! Transition routes between domain boxes and the placement of their labels.

use std::cmp::Reverse;

use crate::geom::floor_div;
use crate::scene::{Align, MarkerAxis};

use super::Area;
use super::cynefin::CynefinPlan;
use super::cynefin_spec::route_label_id;
use super::cynefin_stack::{CurvePoint, DomainPlan};
use super::cynefin_text::{TextBox, bottom, right};

fn dedupe(points: Vec<CurvePoint>) -> Vec<CurvePoint> {
    let mut out: Vec<CurvePoint> = Vec::with_capacity(points.len());
    for point in points {
        if out.last() != Some(&point) {
            out.push(point);
        }
    }
    out
}

fn at(x: i64, y: i64) -> CurvePoint {
    CurvePoint { x, y }
}

fn overlaps(a: Area, b: Area) -> bool {
    a.x < right(b) && b.x < right(a) && a.y < bottom(b) && b.y < bottom(a)
}

fn crosses(path: &[CurvePoint], o: Area) -> bool {
    path.windows(2).any(|pair| {
        let (a, b) = (pair[0], pair[1]);
        a.x.min(b.x) <= right(o)
            && a.x.max(b.x) >= o.x
            && a.y.min(b.y) <= bottom(o)
            && a.y.max(b.y) >= o.y
    })
}

fn hits_label(path: &[CurvePoint], at: Area, reach: i64) -> bool {
    path.windows(2).any(|pair| {
        let (a, b) = (pair[0], pair[1]);
        a.x.min(b.x) < right(at)
            && a.x.max(b.x) + reach > at.x
            && a.y.min(b.y) < bottom(at)
            && a.y.max(b.y) + reach > at.y
    })
}

#[derive(Debug, Clone, Copy)]
struct Link {
    horizontal: bool,
    x0: i64,
    y0: i64,
    x1: i64,
    y1: i64,
}

impl Link {
    fn ends(self) -> (i64, i64) {
        if self.horizontal {
            (self.x0, self.x1)
        } else {
            (self.y0, self.y1)
        }
    }

    fn path(self, mid: i64) -> Vec<CurvePoint> {
        dedupe(if self.horizontal {
            vec![
                at(self.x0, self.y0),
                at(mid, self.y0),
                at(mid, self.y1),
                at(self.x1, self.y1),
            ]
        } else {
            vec![
                at(self.x0, self.y0),
                at(self.x0, mid),
                at(self.x1, mid),
                at(self.x1, self.y1),
            ]
        })
    }

    fn lanes(self, others: &[Area], gap: i64) -> Vec<i64> {
        let (from, to) = self.ends();
        let natural = floor_div(from + to, 2);
        let (lo, hi) = (from.min(to), from.max(to));
        let mut mids = vec![natural];
        for o in others {
            let (before, after) = if self.horizontal {
                (o.x - gap, right(*o) + gap)
            } else {
                (o.y - gap, bottom(*o) + gap)
            };
            for mid in [before, after] {
                if (lo..=hi).contains(&mid) && !mids.contains(&mid) {
                    mids.push(mid);
                }
            }
        }
        mids[1..].sort_by_key(|mid| ((mid - natural).abs(), *mid));
        mids
    }
}

fn horizontal_link(a: &DomainPlan, b: &DomainPlan) -> Option<Link> {
    let (ab, bb) = (a.bounds, b.bounds);
    if right(ab) <= bb.x {
        Some(Link {
            horizontal: true,
            x0: right(ab),
            y0: a.anchor_y,
            x1: bb.x,
            y1: b.anchor_y,
        })
    } else if right(bb) <= ab.x {
        Some(Link {
            horizontal: true,
            x0: ab.x,
            y0: a.anchor_y,
            x1: right(bb),
            y1: b.anchor_y,
        })
    } else {
        None
    }
}

fn vertical_link(a: &DomainPlan, b: &DomainPlan) -> Option<Link> {
    let (ab, bb) = (a.bounds, b.bounds);
    if bottom(ab) <= bb.y {
        Some(Link {
            horizontal: false,
            x0: a.cx,
            y0: bottom(ab),
            x1: b.cx,
            y1: bb.y,
        })
    } else if bottom(bb) <= ab.y {
        Some(Link {
            horizontal: false,
            x0: a.cx,
            y0: ab.y,
            x1: b.cx,
            y1: bottom(bb),
        })
    } else {
        None
    }
}

fn links(a: &DomainPlan, b: &DomainPlan) -> Vec<Link> {
    match (horizontal_link(a, b), vertical_link(a, b)) {
        (Some(h), Some(v)) => vec![h, v],
        (Some(h), None) => vec![h],
        (None, Some(v)) => vec![v],
        (None, None) => {
            let (ab, bb) = (a.bounds, b.bounds);
            let (x0, x1) = if a.cx <= b.cx {
                (right(ab), bb.x)
            } else {
                (ab.x, right(bb))
            };
            vec![Link {
                horizontal: true,
                x0,
                y0: a.anchor_y,
                x1,
                y1: b.anchor_y,
            }]
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct LabelSegment {
    a: CurvePoint,
    b: CurvePoint,
}

impl LabelSegment {
    fn length(self) -> i64 {
        (self.b.x - self.a.x).abs() + (self.b.y - self.a.y).abs()
    }
}

fn segments_by_length(path: &[CurvePoint]) -> Vec<LabelSegment> {
    let mut segments: Vec<LabelSegment> = path
        .iter()
        .enumerate()
        .map(|(i, point)| LabelSegment {
            a: path[i.saturating_sub(1)],
            b: *point,
        })
        .collect();
    segments.sort_by_key(|segment| Reverse(segment.length()));
    segments
}

pub(crate) fn axis_of(a: CurvePoint, b: CurvePoint) -> MarkerAxis {
    let (dx, dy) = (b.x - a.x, b.y - a.y);
    match (dx.abs() >= dy.abs(), dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

impl CynefinPlan<'_> {
    fn elbow(&self, from: usize, to: usize) -> Vec<CurvePoint> {
        let others: Vec<Area> = self
            .domains
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != from && *i != to)
            .map(|(_, d)| d.bounds)
            .collect();
        let mut first: Option<Vec<CurvePoint>> = None;
        for link in links(&self.domains[from], &self.domains[to]) {
            for mid in link.lanes(&others, self.c.pad) {
                let path = link.path(mid);
                if !others.iter().any(|o| crosses(&path, *o)) {
                    return path;
                }
                first.get_or_insert(path);
            }
        }
        first.unwrap_or_default()
    }

    pub(crate) fn route(&mut self) {
        self.paths.clear();
        for i in 0..self.routes.len() {
            let from = self.domain_index(&self.routes[i].from);
            let to = self.domain_index(&self.routes[i].to);
            let path = self.elbow(from, to);
            self.paths.push(path);
        }
        for i in 0..self.routes.len() {
            if !self.routes[i].label.is_empty() {
                self.route_label(i);
            }
        }
    }

    fn path_reach(&self) -> i64 {
        i64::from(matches!(self.profile, crate::scene::Profile::Cell))
    }

    fn label_blocked(&self, area: Area) -> bool {
        let reach = self.path_reach();
        self.domains.iter().any(|d| overlaps(area, d.bounds))
            || self.paths.iter().any(|p| hits_label(p, area, reach))
            || self.extents.iter().any(|e| overlaps(area, *e))
    }

    fn label_sides(&self, text: &TextBox, s: LabelSegment) -> Vec<(Area, Align)> {
        let (mx, my) = (floor_div(s.a.x + s.b.x, 2), floor_div(s.a.y + s.b.y, 2));
        let gap = self.c.label_gap;
        if s.a.y != s.b.y {
            return vec![
                (
                    Area::new(mx + gap, my - floor_div(text.h, 2), text.w, text.h),
                    Align::Start,
                ),
                (
                    Area::new(mx - gap - text.w, my - floor_div(text.h, 2), text.w, text.h),
                    Align::Start,
                ),
            ];
        }
        vec![
            (
                Area::new(mx - floor_div(text.w, 2), my + gap, text.w, text.h),
                Align::Middle,
            ),
            (
                Area::new(mx - floor_div(text.w, 2), my - gap - text.h, text.w, text.h),
                Align::Middle,
            ),
        ]
    }

    fn route_label(&mut self, index: usize) {
        let text = self.route_boxes[index].clone();
        let mut sides: Vec<(Area, Align)> = segments_by_length(&self.paths[index])
            .into_iter()
            .flat_map(|segment| self.label_sides(&text, segment))
            .collect();
        for (area, _) in &mut sides {
            area.x = area.x.max(0);
            area.y = area.y.max(0);
        }
        let chosen = sides
            .iter()
            .find(|(area, _)| !self.label_blocked(*area))
            .or(sides.first())
            .copied();
        if let Some((area, align)) = chosen {
            self.set_label(&route_label_id(index), area, align, text);
        }
    }

    pub(crate) fn set_label(&mut self, id: &str, at: Area, align: Align, text: TextBox) {
        self.labels.insert(
            id.to_owned(),
            super::cynefin::PlacedLabel { at, align, text },
        );
        self.extents.push(at);
    }
}
