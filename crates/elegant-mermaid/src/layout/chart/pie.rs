//! The pie plan: constants, the sweep rule, the measured texts, and the placement
//! (`spec/layout/charts.md`, charts-81 to charts-86). Geometry is in vector units only;
//! the text back end draws the vector scene as braille dots.

use std::collections::BTreeMap;

use crate::geom::{Size, floor_div, floor_mod, sin_q15};
use crate::measure::{self, Metric, Role};
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox,
    SceneLabel,
};

use super::xy::{MeasuredLine, TextBox};
use super::xy_axis::check_magnitude;
use super::{Area, LayoutError, Skeleton, ZERO_RECT, constant};

const KIND: &str = "pie";
pub(super) const PLOT_ID: &str = "plot";
const TITLE_ID: &str = "title";
pub(super) const FULL_TURN: i64 = 65536;
pub(super) const HALF_TURN: i64 = 32768;
pub(super) const QUARTER_TURN: i64 = 16384;
pub(super) const SCALE: i64 = 1000;
const DONUT_HOLE_KEY: &str = "donutHole";
const TEXT_POSITION_KEY: &str = "textPosition";
const DONUT_HOLE_MAX: i64 = 900;
const UNITS_PER_PX: i64 = 64;

/// One section of the pie, as the chart family reads it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PieSection {
    pub label: String,
    pub value: i64,
    pub index: usize,
}

/// The pie payload: the title, the typed config entries, and the sections.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PiePayload {
    pub title: String,
    pub config: BTreeMap<String, DumpValue>,
    pub show_data: bool,
    pub sections: Vec<PieSection>,
}

impl PiePayload {
    fn integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(value)) => Some(*value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Consts {
    pub height: i64,
    pub margin: i64,
    pub legend_row: i64,
    pub legend_size: i64,
    pub legend_offset: i64,
    pub title_pad: i64,
    pub text_position: i64,
}

fn load_consts() -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(Profile::Vector, &format!("pie.{name}"));
    Ok(Consts {
        height: get("height")?,
        margin: get("margin")?,
        legend_row: get("legend_row")?,
        legend_size: get("legend_size")?,
        legend_offset: get("legend_offset")?,
        title_pad: get("title_pad")?,
        text_position: get("text_position_m")?,
    })
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Slice {
    pub section: usize,
    pub start: i64,
    pub sweep: i64,
    pub percent: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LabelKind {
    Title,
    Percent,
    Legend,
}

#[derive(Debug, Clone)]
pub(super) struct Label {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub kind: LabelKind,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Geom {
    pub width: i64,
    pub height: i64,
    pub cx: i64,
    pub cy: i64,
    pub radius: i64,
    pub inner: i64,
    pub label_radius: i64,
}

pub(super) struct PiePlan<'a> {
    pub payload: &'a PiePayload,
    pub c: Consts,
    pub slices: Vec<Slice>,
    pub g: Geom,
    pub labels: Vec<Label>,
    pub texts: Vec<TextBox>,
    pub rects: Vec<Area>,
    pub swatches: Vec<Area>,
    pub boxes: Vec<Area>,
    pub canvas: Size,
    pub placed: bool,
}

pub(super) fn slice_id(section: usize) -> String {
    format!("s{section}")
}

fn legend_id(index: usize) -> String {
    format!("legend.{index}")
}

fn sweeps_of(values: &[i64], total: i64) -> Vec<i64> {
    let mut sweeps = vec![0; values.len()];
    if total == 0 {
        return sweeps;
    }
    let mut rems = vec![0; values.len()];
    let mut used = 0;
    for (i, &v) in values.iter().enumerate() {
        let num = v * FULL_TURN;
        sweeps[i] = floor_div(num, total);
        rems[i] = floor_mod(num, total);
        used += sweeps[i];
    }
    let mut order: Vec<usize> = (0..values.len()).collect();
    order.sort_by(|&a, &b| rems[b].cmp(&rems[a]).then(a.cmp(&b)));
    let extra = usize::try_from(FULL_TURN - used).unwrap_or(0);
    for &i in order.iter().take(extra) {
        sweeps[i] += 1;
    }
    sweeps
}

fn slices_of(values: &[i64], total: i64) -> Vec<Slice> {
    let mut out = Vec::new();
    let mut start = 0;
    for (i, sweep) in sweeps_of(values, total).into_iter().enumerate() {
        if sweep > 0 {
            out.push(Slice {
                section: i,
                start,
                sweep,
                percent: floor_div(200 * values[i] + total, 2 * total),
            });
        }
        start += sweep;
    }
    out
}

fn geometry(c: &Consts, donut: i64, text_position: i64) -> Geom {
    let (width, height) = (c.height, c.height);
    let (cx, cy) = (floor_div(width, 2), floor_div(height, 2));
    let radius = cx.min(cy) - c.margin;
    Geom {
        width,
        height,
        cx,
        cy,
        radius,
        inner: floor_div(radius * donut, SCALE),
        label_radius: floor_div(radius * text_position, SCALE),
    }
}

/// The vertex of the Arc rule at an angle in 1/65536 turn.
pub(super) fn arc_vertex(cx: i64, cy: i64, r: i64, angle: i64) -> (i64, i64) {
    let a = i32::try_from(floor_mod(angle, FULL_TURN)).unwrap_or(0);
    let cos = i64::from(sin_q15(a.wrapping_add(16384)));
    let sin = i64::from(sin_q15(a));
    (
        cx + floor_div(2 * r * cos + HALF_TURN, FULL_TURN),
        cy + floor_div(2 * r * sin + HALF_TURN, FULL_TURN),
    )
}

pub(super) fn role_of(label: &Label) -> (Role, i32) {
    if label.kind == LabelKind::Title {
        (Role::Title, Role::Title.size_px())
    } else {
        (Role::Label, Role::Label.size_px())
    }
}

fn measure_text(label: &Label) -> Result<TextBox, LayoutError> {
    let (role, size) = role_of(label);
    let metric = Metric::Vector {
        size_px: size,
        weight: role.weight(),
        font_family: false,
    };
    let lines = measure::styled_lines(&label.text, i32::MAX, metric)?;
    let widest = lines
        .iter()
        .map(|line| i64::from(line.width))
        .max()
        .unwrap_or(0);
    let line_h = measure::round_half_up(
        i64::from(size) * UNITS_PER_PX * i64::from(role.line_height_px()),
        i64::from(role.size_px()),
    );
    let count = i64::try_from(lines.len()).unwrap_or(i64::MAX);
    let lines = lines
        .iter()
        .map(|line| MeasuredLine {
            text: line.text.clone(),
            runs: line
                .runs
                .iter()
                .map(|run| Run {
                    text: run.text.to_owned(),
                    bold: run.bold,
                    italic: run.italic,
                })
                .collect(),
        })
        .collect();
    Ok(TextBox {
        lines,
        w: widest,
        h: count * line_h,
    })
}

#[derive(Debug, Clone, Copy, Default)]
struct Bounds {
    x0: i64,
    y0: i64,
    x1: i64,
    y1: i64,
    set: bool,
}

impl Bounds {
    fn add(&mut self, x: i64, y: i64) {
        if !self.set {
            *self = Bounds {
                x0: x,
                y0: y,
                x1: x,
                y1: y,
                set: true,
            };
            return;
        }
        self.x0 = self.x0.min(x);
        self.y0 = self.y0.min(y);
        self.x1 = self.x1.max(x);
        self.y1 = self.y1.max(y);
    }

    fn add_area(&mut self, a: Area) {
        self.add(a.x, a.y);
        self.add(a.x + a.w, a.y + a.h);
    }

    fn add_arc(&mut self, cx: i64, cy: i64, r: i64, a0: i64, sweep: i64) {
        let (x, y) = arc_vertex(cx, cy, r, a0);
        self.add(x, y);
        let (x, y) = arc_vertex(cx, cy, r, a0 + sweep);
        self.add(x, y);
        let (lo, hi) = (a0.min(a0 + sweep), a0.max(a0 + sweep));
        let mut q = floor_div(lo + QUARTER_TURN - 1, QUARTER_TURN) * QUARTER_TURN;
        while q <= hi {
            let (x, y) = arc_vertex(cx, cy, r, q);
            self.add(x, y);
            q += QUARTER_TURN;
        }
    }

    fn area(&self) -> Area {
        Area::new(self.x0, self.y0, self.x1 - self.x0, self.y1 - self.y0)
    }
}

impl<'a> PiePlan<'a> {
    pub(super) fn new(payload: &'a PiePayload) -> Result<PiePlan<'a>, LayoutError> {
        let c = load_consts()?;
        let values: Vec<i64> = payload.sections.iter().map(|s| s.value).collect();
        let total: i64 = values.iter().sum();
        let mut checked = values.clone();
        checked.push(total);
        check_magnitude(&checked)?;
        let donut = payload
            .integer(DONUT_HOLE_KEY)
            .filter(|n| *n > 0 && *n <= DONUT_HOLE_MAX)
            .unwrap_or(0);
        let text_position = payload
            .integer(TEXT_POSITION_KEY)
            .filter(|n| (0..=SCALE).contains(n))
            .unwrap_or(c.text_position);
        let slices = slices_of(&values, total);
        let mut plan = PiePlan {
            payload,
            c,
            slices,
            g: geometry(&c, donut, text_position),
            labels: Vec::new(),
            texts: Vec::new(),
            rects: Vec::new(),
            swatches: Vec::new(),
            boxes: Vec::new(),
            canvas: Size { w: 0, h: 0 },
            placed: false,
        };
        plan.labels = plan.label_specs();
        Ok(plan)
    }

    fn legend_text(&self, section: usize) -> String {
        let s = &self.payload.sections[section];
        if self.payload.show_data {
            format!("{} [{}]", s.label, super::scale::format_number(s.value))
        } else {
            s.label.clone()
        }
    }

    fn label_specs(&self) -> Vec<Label> {
        let mut out = Vec::new();
        if !self.payload.title.is_empty() {
            out.push(Label {
                id: TITLE_ID.to_owned(),
                owner: PLOT_ID.to_owned(),
                text: self.payload.title.clone(),
                kind: LabelKind::Title,
                index: 0,
            });
        }
        for (i, s) in self.slices.iter().enumerate() {
            if s.percent == 0 {
                continue;
            }
            let id = slice_id(s.section);
            out.push(Label {
                id: format!("{id}.pct"),
                owner: id,
                text: format!("{}%", s.percent),
                kind: LabelKind::Percent,
                index: i,
            });
        }
        for i in 0..self.payload.sections.len() {
            out.push(Label {
                id: legend_id(i),
                owner: PLOT_ID.to_owned(),
                text: self.legend_text(i),
                kind: LabelKind::Legend,
                index: i,
            });
        }
        out
    }

    /// The box ids in dump order: the plot, then one box for each drawn slice.
    pub(super) fn box_ids(&self) -> Vec<String> {
        let mut ids = vec![PLOT_ID.to_owned()];
        ids.extend(self.slices.iter().map(|s| slice_id(s.section)));
        ids
    }

    pub(super) fn dump_boxes(&self) -> Result<Vec<SceneBox>, LayoutError> {
        self.box_ids()
            .into_iter()
            .enumerate()
            .map(|(i, id)| {
                Ok(SceneBox {
                    id,
                    role: BoxRole::Node,
                    rect: if self.placed {
                        self.boxes[i].to_rect()?
                    } else {
                        ZERO_RECT
                    },
                    parent: if i == 0 {
                        String::new()
                    } else {
                        PLOT_ID.to_owned()
                    },
                    exclusive: false,
                })
            })
            .collect()
    }

    pub(super) fn dump_labels(&self) -> Result<Vec<SceneLabel>, LayoutError> {
        self.labels
            .iter()
            .enumerate()
            .map(|(i, l)| {
                let (rect, lines) = if self.placed {
                    (
                        self.rects[i].to_rect()?,
                        self.texts[i].lines.iter().map(|x| x.text.clone()).collect(),
                    )
                } else {
                    (ZERO_RECT, Vec::new())
                };
                Ok(SceneLabel {
                    id: l.id.clone(),
                    owner: l.owner.clone(),
                    text: l.text.clone(),
                    rect,
                    lines,
                })
            })
            .collect()
    }

    pub(super) fn measure_all(&mut self) -> Result<(), LayoutError> {
        self.texts = self
            .labels
            .iter()
            .map(measure_text)
            .collect::<Result<_, _>>()?;
        Ok(())
    }

    fn percent_area(&self, slice: &Slice, t: &TextBox) -> Area {
        let mid = slice.start + floor_div(slice.sweep, 2);
        let a = i32::try_from(floor_mod(mid, FULL_TURN)).unwrap_or(0);
        let sin = i64::from(sin_q15(a));
        let cos = i64::from(sin_q15(a.wrapping_add(16384)));
        let x = self.g.cx + floor_div(self.g.label_radius * sin, HALF_TURN);
        let y = self.g.cy - floor_div(self.g.label_radius * cos, HALF_TURN);
        Area::new(x - floor_div(t.w, 2), y - floor_div(t.h, 2), t.w, t.h)
    }

    fn slice_bounds(&self, slice: &Slice) -> Area {
        let g = &self.g;
        let a0 = floor_mod(slice.start - QUARTER_TURN, FULL_TURN);
        let mut b = Bounds::default();
        b.add_arc(g.cx, g.cy, g.radius, a0, slice.sweep);
        if g.inner == 0 {
            b.add(g.cx, g.cy);
        } else {
            b.add_arc(g.cx, g.cy, g.inner, a0, slice.sweep);
        }
        b.area()
    }

    pub(super) fn place(&mut self) -> Result<(), LayoutError> {
        let (g, c) = (self.g, self.c);
        let mut extent = Bounds::default();
        extent.add_area(Area::new(0, 0, g.width, g.height));
        let rows = i64::try_from(self.payload.sections.len()).unwrap_or(i64::MAX);
        let top = g.cy - floor_div(c.legend_row * rows, 2);
        let left = g.cx + c.legend_offset;
        let mut longest = 0;
        self.rects = Vec::with_capacity(self.labels.len());
        self.swatches.clear();
        for (i, label) in self.labels.iter().enumerate() {
            let t = &self.texts[i];
            let area = match label.kind {
                LabelKind::Title => Area::new(g.cx - floor_div(t.w, 2), c.title_pad, t.w, t.h),
                LabelKind::Percent => self.percent_area(&self.slices[label.index], t),
                LabelKind::Legend => {
                    let row = top + i64::try_from(label.index).unwrap_or(0) * c.legend_row;
                    self.swatches
                        .push(Area::new(left, row, c.legend_size, c.legend_size));
                    longest = longest.max(t.w);
                    Area::new(
                        left + c.legend_row,
                        row + floor_div(c.legend_size - t.h, 2),
                        t.w,
                        t.h,
                    )
                }
            };
            extent.add_area(area);
            self.rects.push(area);
        }
        for &sw in &self.swatches {
            extent.add_area(sw);
        }
        if rows > 0 {
            extent.add(g.width + c.margin + c.legend_row + longest, extent.y1);
        }
        let (dx, dy) = (-extent.x0, -extent.y0);
        for a in self.rects.iter_mut().chain(self.swatches.iter_mut()) {
            a.x += dx;
            a.y += dy;
        }
        self.g.cx += dx;
        self.g.cy += dy;
        let mut boxes = vec![Area::new(
            self.g.cx - g.cx,
            self.g.cy - g.cy,
            g.width,
            g.height,
        )];
        boxes.extend(self.slices.iter().map(|s| self.slice_bounds(s)));
        self.boxes = boxes;
        self.canvas = Size {
            w: super::to_i32(extent.x1 - extent.x0)?,
            h: super::to_i32(extent.y1 - extent.y0)?,
        };
        self.placed = true;
        Ok(())
    }

    pub(super) fn align_of(&self, index: usize) -> Align {
        if self.labels[index].kind == LabelKind::Legend {
            Align::Start
        } else {
            Align::Middle
        }
    }
}

pub(crate) fn layout_pie(
    payload: &PiePayload,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut plan = PiePlan::new(payload)?;
    plan.measure_all()?;
    plan.place()?;
    let mut dump_options = options.clone();
    dump_options.profile = Profile::Vector;
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes()?;
    dump.labels = plan.dump_labels()?;
    let groups = plan.groups()?;
    Ok((Scene::new(plan.canvas, dump, groups), false))
}

pub(crate) fn pie_skeleton(payload: &PiePayload) -> Result<Skeleton, LayoutError> {
    let plan = PiePlan::new(payload)?;
    Ok(Skeleton {
        boxes: plan.dump_boxes()?,
        labels: plan.dump_labels()?,
    })
}
