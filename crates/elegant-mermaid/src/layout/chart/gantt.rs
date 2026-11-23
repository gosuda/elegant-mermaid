//! The gantt plan: constants, the box and label records of the dump, and the phase order
//! of the layout (`spec/layout/charts.md`, gantt).

use crate::civil;
use crate::geom::{GeomError, Rect, Size, floor_div};
use crate::measure::{self, Metric, Role};
use crate::model::chart::{Chart, Gantt, GanttRowKind};
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, Profile, Run, Scene, SceneBox, SceneLabel,
};

use super::xy::{MeasuredLine, TextBox};
use super::{Area, LayoutError, Skeleton, ZERO_RECT, constant, to_i32};

pub(crate) const PLOT_ID: &str = "plot";
const KIND: &str = "gantt";
const TASK_FONT: i32 = 12;
const SECTION_FONT: i32 = 14;
pub(crate) const TICK_FONT: i32 = 10;
pub(crate) const DEFAULT_FORMAT: &str = "%Y-%m-%d";
const VECTOR_UNITS_PER_PX: i64 = 64;
const CELL_PX_HIGH: i64 = 16;
const CELL_PX_WIDE: i64 = 8;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Consts {
    pub width: i64,
    pub bar_h: i64,
    pub row_gap: i64,
    pub top_pad: i64,
    pub gutter: i64,
    pub side_pad: i64,
    pub axis_h: i64,
    pub tick_len: i64,
    pub tick_gap: i64,
    pub title_pad: i64,
    pub label_gap: i64,
    pub section_pad: i64,
    pub vert_w: i64,
    pub tick_cap: i64,
    pub estimate_cap: i64,
    pub exclude_years: i64,
    pub edge: i64,
}

const MAX_CONFIG_PX: u64 = 1 << 25;

fn canvas_side(profile: Profile, px: i64, cell_px: i64) -> i64 {
    if profile == Profile::Cell {
        measure::ceil_div(px, cell_px)
    } else {
        px * VECTOR_UNITS_PER_PX
    }
}

fn load_consts(profile: Profile, chart: &Chart) -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(profile, &format!("gantt.{name}"));
    let mut c = Consts {
        width: get("width")?,
        bar_h: get("bar_height")?,
        row_gap: get("row_gap")?,
        top_pad: get("top_pad")?,
        gutter: get("label_gutter")?,
        side_pad: get("side_pad")?,
        axis_h: get("axis_height")?,
        tick_len: get("tick_length")?,
        tick_gap: get("tick_label_gap")?,
        title_pad: get("title_pad")?,
        label_gap: get("label_gap")?,
        section_pad: get("section_pad")?,
        vert_w: get("vert_width")?,
        tick_cap: get("tick_cap")?,
        estimate_cap: get("tick_estimate_cap")?,
        exclude_years: get("exclude_years_max")?,
        edge: i64::from(profile == Profile::Cell),
    };
    for (key, cell_px, into) in [
        ("barHeight", CELL_PX_HIGH, &mut c.bar_h),
        ("barGap", CELL_PX_HIGH, &mut c.row_gap),
        ("topPadding", CELL_PX_HIGH, &mut c.top_pad),
        ("leftPadding", CELL_PX_WIDE, &mut c.gutter),
        ("rightPadding", CELL_PX_WIDE, &mut c.side_pad),
    ] {
        let Some(n) = chart.integer(key) else {
            continue;
        };
        if n.unsigned_abs() > MAX_CONFIG_PX {
            return Err(GeomError::Overflow);
        }
        *into = canvas_side(profile, n, cell_px);
    }
    Ok(c)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoxKind {
    Plot,
    Section,
    Task,
    Vert,
}

#[derive(Debug, Clone)]
pub(crate) struct GanttBox {
    pub id: String,
    pub kind: BoxKind,
    pub index: usize,
    pub row: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LabelKind {
    Title,
    Section,
    Task,
    Tick,
    TopTick,
}

#[derive(Debug, Clone)]
pub(crate) struct GanttLabel {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub kind: LabelKind,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct Placed {
    pub box_rects: Vec<Rect>,
    pub label_rects: Vec<Rect>,
    pub label_lines: Vec<Vec<String>>,
    pub shown: Vec<bool>,
    pub aligns: Vec<Align>,
    pub chips: Vec<bool>,
}

pub(crate) struct GanttPlan<'a> {
    pub title: &'a str,
    pub g: &'a Gantt,
    pub c: Consts,
    pub cell: bool,
    font_family: bool,
    pub boxes: Vec<GanttBox>,
    pub labels: Vec<GanttLabel>,
    pub d0: i64,
    pub d1: i64,
    pub ticks: Vec<i64>,
    pub tick_text: Vec<String>,
    pub capped: bool,
    pub width: i64,
    pub height: i64,
    pub pitch: i64,
    pub rows: i64,
    pub plot: Area,
    pub texts: Vec<TextBox>,
    pub placed: Option<Placed>,
}

pub(crate) fn box_id(kind: BoxKind, index: usize) -> String {
    match kind {
        BoxKind::Section => format!("s{index}"),
        BoxKind::Task | BoxKind::Vert => format!("t{index}"),
        BoxKind::Plot => PLOT_ID.to_owned(),
    }
}

impl<'a> GanttPlan<'a> {
    pub(crate) fn new(chart: &'a Chart, profile: Profile) -> Result<Self, LayoutError> {
        let g = chart.gantt.as_ref().ok_or(GeomError::Domain)?;
        let c = load_consts(profile, chart)?;
        let mut plan = Self {
            title: &chart.title,
            g,
            c,
            cell: profile == Profile::Cell,
            font_family: crate::scene::has_font_family(&chart.config),
            boxes: Vec::new(),
            labels: Vec::new(),
            d0: 0,
            d1: 0,
            ticks: Vec::new(),
            tick_text: Vec::new(),
            capped: false,
            width: 0,
            height: 0,
            pitch: c.bar_h + c.row_gap,
            rows: 0,
            plot: Area::default(),
            texts: Vec::new(),
            placed: None,
        };
        plan.check_rows()?;
        (plan.d0, plan.d1) = plan.domain();
        plan.compute_ticks();
        plan.build_boxes();
        plan.build_labels();
        Ok(plan)
    }

    fn check_rows(&self) -> Result<(), LayoutError> {
        for t in &self.g.tasks {
            if [t.start, t.end, t.render_end]
                .iter()
                .any(|v| !(-civil::MAX_ABS_SECONDS..=civil::MAX_ABS_SECONDS).contains(v))
            {
                return Err(GeomError::Overflow);
            }
            if t.section.is_some_and(|s| s >= self.g.sections.len()) {
                return Err(GeomError::Domain);
            }
        }
        for row in &self.g.rows {
            let limit = match row.kind {
                GanttRowKind::Section => self.g.sections.len(),
                GanttRowKind::Task => self.g.tasks.len(),
            };
            if row.index >= limit {
                return Err(GeomError::Domain);
            }
        }
        Ok(())
    }

    fn domain(&self) -> (i64, i64) {
        let mut tasks = self.g.tasks.iter();
        let Some(first) = tasks.next() else {
            return (0, civil::SECONDS_PER_DAY);
        };
        tasks.fold((first.start, first.end), |(lo, hi), t| {
            (lo.min(t.start), hi.max(t.end))
        })
    }

    fn build_boxes(&mut self) {
        self.boxes.push(GanttBox {
            id: PLOT_ID.to_owned(),
            kind: BoxKind::Plot,
            index: 0,
            row: None,
        });
        for (k, row) in self.g.rows.iter().enumerate() {
            let kind = match row.kind {
                GanttRowKind::Section => BoxKind::Section,
                GanttRowKind::Task => BoxKind::Task,
            };
            self.boxes.push(GanttBox {
                id: box_id(kind, row.index),
                kind,
                index: row.index,
                row: Some(k),
            });
        }
        for (i, t) in self.g.tasks.iter().enumerate() {
            if t.vert {
                self.boxes.push(GanttBox {
                    id: box_id(BoxKind::Vert, i),
                    kind: BoxKind::Vert,
                    index: i,
                    row: None,
                });
            }
        }
        self.rows = i64::try_from(self.g.rows.len()).unwrap_or(i64::MAX);
    }

    fn push_label(&mut self, label: GanttLabel) {
        if !label.text.is_empty() {
            self.labels.push(label);
        }
    }

    fn build_labels(&mut self) {
        self.push_label(GanttLabel {
            id: "title".into(),
            owner: PLOT_ID.into(),
            text: self.title.to_owned(),
            kind: LabelKind::Title,
            index: 0,
        });
        let row_labels: Vec<GanttLabel> = self
            .boxes
            .iter()
            .filter_map(|b| {
                let (text, kind) = match b.kind {
                    BoxKind::Section => (self.g.sections.get(b.index)?, LabelKind::Section),
                    BoxKind::Task | BoxKind::Vert => {
                        (&self.g.tasks.get(b.index)?.label, LabelKind::Task)
                    }
                    BoxKind::Plot => return None,
                };
                Some(GanttLabel {
                    id: format!("{}.label", b.id),
                    owner: b.id.clone(),
                    text: text.clone(),
                    kind,
                    index: b.index,
                })
            })
            .collect();
        for label in row_labels {
            self.push_label(label);
        }
        let ticks: Vec<GanttLabel> = self
            .tick_text
            .iter()
            .enumerate()
            .map(|(k, text)| GanttLabel {
                id: format!("x.t{k}"),
                owner: PLOT_ID.into(),
                text: text.clone(),
                kind: LabelKind::Tick,
                index: k,
            })
            .collect();
        for label in ticks {
            self.push_label(label);
        }
        if self.g.top_axis {
            let tops: Vec<GanttLabel> = self
                .tick_text
                .iter()
                .enumerate()
                .map(|(k, text)| GanttLabel {
                    id: format!("xt.t{k}"),
                    owner: PLOT_ID.into(),
                    text: text.clone(),
                    kind: LabelKind::TopTick,
                    index: k,
                })
                .collect();
            for label in tops {
                self.push_label(label);
            }
        }
    }

    pub(crate) fn dump_boxes(&self) -> Vec<SceneBox> {
        self.boxes
            .iter()
            .enumerate()
            .map(|(i, b)| SceneBox {
                id: b.id.clone(),
                role: BoxRole::Node,
                rect: self
                    .placed
                    .as_ref()
                    .map_or(ZERO_RECT, |placed| placed.box_rects[i]),
                parent: if b.kind == BoxKind::Plot {
                    String::new()
                } else {
                    PLOT_ID.to_owned()
                },
                exclusive: false,
            })
            .collect()
    }

    pub(crate) fn dump_labels(&self) -> Vec<SceneLabel> {
        self.labels
            .iter()
            .enumerate()
            .map(|(i, l)| {
                let (rect, lines) = match &self.placed {
                    Some(placed) => (placed.label_rects[i], placed.label_lines[i].clone()),
                    None => (ZERO_RECT, Vec::new()),
                };
                SceneLabel {
                    id: l.id.clone(),
                    owner: l.owner.clone(),
                    text: l.text.clone(),
                    rect,
                    lines,
                }
            })
            .collect()
    }

    pub(crate) fn time_x(&self, v: i64) -> Result<i64, LayoutError> {
        let (r0, r1) = (self.c.gutter, self.c.width - self.c.side_pad);
        if self.d1 == self.d0 {
            return Ok(floor_div(r0 + r1, 2));
        }
        let product = (v - self.d0)
            .checked_mul(r1 - r0)
            .ok_or(GeomError::Overflow)?;
        Ok(r0 + floor_div(product, self.d1 - self.d0))
    }

    pub(crate) fn axis_y(&self) -> i64 {
        self.c.top_pad + self.rows * self.pitch
    }

    pub(crate) fn top_axis_y(&self) -> i64 {
        self.c.top_pad - self.c.edge
    }

    pub(crate) fn row_top(&self, row: usize) -> i64 {
        self.c.top_pad + i64::try_from(row).unwrap_or(i64::MAX) * self.pitch
    }

    pub(crate) fn style_of(&self, l: &GanttLabel) -> (Role, i32) {
        match l.kind {
            LabelKind::Title => (Role::Title, Role::Title.size_px()),
            LabelKind::Section => (Role::Label, SECTION_FONT),
            LabelKind::Task => (Role::Label, TASK_FONT),
            LabelKind::Tick | LabelKind::TopTick => (Role::Label, TICK_FONT),
        }
    }

    pub(crate) fn line_height(&self, role: Role, size: i32) -> i64 {
        if self.cell {
            return 1;
        }
        measure::round_half_up(
            i64::from(size) * VECTOR_UNITS_PER_PX * i64::from(role.line_height_px()),
            i64::from(role.size_px()),
        )
    }

    fn metric(&self, role: Role, size: i32) -> Metric {
        if self.cell {
            Metric::cell()
        } else {
            Metric::Vector {
                size_px: size,
                weight: role.weight(),
                font_family: self.font_family,
            }
        }
    }

    fn measure_text(&self, text: &str, role: Role, size: i32) -> Result<TextBox, LayoutError> {
        let lines = measure::styled_lines(text, i32::MAX, self.metric(role, size))?;
        let widest = lines
            .iter()
            .map(|line| i64::from(line.width))
            .max()
            .unwrap_or(0);
        let height = i64::try_from(lines.len()).unwrap_or(i64::MAX) * self.line_height(role, size);
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
            h: height,
        })
    }

    pub(crate) fn measure_all(&mut self) -> Result<(), LayoutError> {
        let mut texts = Vec::with_capacity(self.labels.len());
        for label in &self.labels {
            let (role, size) = self.style_of(label);
            texts.push(self.measure_text(&label.text, role, size)?);
        }
        self.texts = texts;
        Ok(())
    }
}

pub(super) fn layout_gantt(
    chart: &Chart,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut plan = GanttPlan::new(chart, options.profile)?;
    plan.measure_all()?;
    plan.width = plan.c.width;
    plan.height = plan.c.top_pad + plan.rows * plan.pitch + plan.c.axis_h;
    plan.plot = Area::new(0, plan.c.top_pad, plan.width, plan.rows * plan.pitch);
    plan.place()?;
    let canvas = Size {
        w: to_i32(plan.width)?,
        h: to_i32(plan.height)?,
    };
    let mut dump_options = options.clone();
    dump_options.direction = Direction::Tb;
    let mut dump = Dump::new(KIND, dump_options);
    dump.boxes = plan.dump_boxes();
    dump.labels = plan.dump_labels();
    let groups = plan.groups()?;
    Ok((Scene::new(canvas, dump, groups), plan.capped))
}

pub(super) fn skeleton(chart: &Chart) -> Result<Skeleton, LayoutError> {
    let plan = GanttPlan::new(chart, Profile::Vector)?;
    Ok(Skeleton {
        boxes: plan.dump_boxes(),
        labels: plan.dump_labels(),
    })
}
