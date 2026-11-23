//! The Wardley plan: constants, projection, arranged positions, and measured texts.

use std::collections::BTreeMap;

use crate::geom::{Rect, floor_div};
use crate::measure::{self, Metric, Role};
use crate::scene::{Align, DumpOptions, DumpValue, Profile, SceneRoute};

use super::scale::clamp;
use super::wardley::{
    FULL_SCALE, Kind, Spec, Wardley, WardleyForce, WardleyNode, WardleyPipeline, WardleyStrategy,
};
use super::xy::{MeasuredLine, TextBox};
use super::{Area, LayoutError, constant};

const CELL_PX_WIDE: i64 = 8;
const CELL_PX_HIGH: i64 = 16;
const UNITS_PER_PX: i64 = 64;
const SCALE: i64 = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Pt {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Consts {
    pub pad_x: i64,
    pub pad_y: i64,
    pub width: i64,
    pub height: i64,
    pub node_radius: i64,
    pub label_gap: i64,
    pub square_size: i64,
    pub pipeline_pad: i64,
    pub pipeline_height: i64,
    pub inertia_gap: i64,
    pub inertia_width: i64,
    pub market_ring: i64,
    pub market_dot: i64,
    pub annotation_radius: i64,
    pub box_pad: i64,
    pub arrow_width: i64,
    pub arrow_shaft: i64,
    pub arrow_head: i64,
    pub arrow_tip: i64,
    pub link_label_gap: i64,
    pub axis_gap: i64,
    pub stage_gap: i64,
    pub label_size: i64,
    pub axis_size: i64,
    pub note_size: i64,
    pub edge: i64,
}

fn canvas_side(profile: Profile, px: i64, cell_px: i64) -> i64 {
    if profile == Profile::Cell {
        measure::ceil_div(px, cell_px)
    } else {
        px * UNITS_PER_PX
    }
}

fn config_integer(config: &BTreeMap<String, DumpValue>, key: &str) -> Option<i64> {
    match config.get(key) {
        Some(DumpValue::Integer(n)) => Some(*n),
        _ => None,
    }
}

pub(super) fn load_consts(
    profile: Profile,
    config: &BTreeMap<String, DumpValue>,
) -> Result<Consts, LayoutError> {
    let get = |name: &str| constant(profile, &format!("wardley.{name}"));
    let mut c = Consts {
        pad_x: get("padding_x")?,
        pad_y: get("padding_y")?,
        width: get("width")?,
        height: get("height")?,
        node_radius: get("node_radius")?,
        label_gap: get("label_gap")?,
        square_size: get("square_size")?,
        pipeline_pad: get("pipeline_pad")?,
        pipeline_height: get("pipeline_height")?,
        inertia_gap: get("inertia_gap")?,
        inertia_width: get("inertia_width")?,
        market_ring: get("market_ring")?,
        market_dot: get("market_dot")?,
        annotation_radius: get("annotation_radius")?,
        box_pad: get("box_pad")?,
        arrow_width: get("arrow_width")?,
        arrow_shaft: get("arrow_shaft")?,
        arrow_head: get("arrow_head")?,
        arrow_tip: get("arrow_tip")?,
        link_label_gap: get("link_label_gap")?,
        axis_gap: get("axis_gap")?,
        stage_gap: get("stage_gap")?,
        label_size: get("label_size")?,
        axis_size: get("axis_size")?,
        note_size: get("note_size")?,
        edge: i64::from(profile == Profile::Cell),
    };
    if let Some(n) = config_integer(config, "width") {
        c.width = canvas_side(profile, n, CELL_PX_WIDE);
    }
    if let Some(n) = config_integer(config, "height") {
        c.height = canvas_side(profile, n, CELL_PX_HIGH);
    }
    if let Some(n) = config_integer(config, "padding") {
        c.pad_x = canvas_side(profile, n, CELL_PX_WIDE);
        c.pad_y = canvas_side(profile, n, CELL_PX_HIGH);
    }
    Ok(c)
}

pub(super) struct Plan<'a> {
    pub w: &'a Wardley,
    pub c: Consts,
    pub cell: bool,
    font_family: bool,
    pub width: i64,
    pub height: i64,
    pub plot: Area,
    pub base: Vec<Pt>,
    pub pos: Vec<Pt>,
    pub frames: Vec<Area>,
    pub ghosts: Vec<Pt>,
    pub accels: Vec<Area>,
    pub decels: Vec<Area>,
    pub points: Vec<Pt>,
    pub notes: Vec<Pt>,
    pub box_area: Area,
    pub boxed: Vec<usize>,
    pub specs: Vec<Spec>,
    pub texts: Vec<TextBox>,
    pub shown: Vec<bool>,
    pub rects: Vec<Rect>,
    pub aligns: Vec<Align>,
    pub lines: Vec<Vec<String>>,
    pub box_rects: Vec<Rect>,
    pub routes: Vec<SceneRoute>,
}

impl<'a> Plan<'a> {
    pub(super) fn new(w: &'a Wardley, options: &DumpOptions) -> Result<Plan<'a>, LayoutError> {
        let c = load_consts(options.profile, &options.config)?;
        let width = c.width.max(2 * c.pad_x + c.arrow_width + c.edge);
        let height = c
            .height
            .max(2 * c.pad_y + 2 * (c.arrow_shaft + c.arrow_head) + c.edge);
        Ok(Plan {
            w,
            c,
            cell: options.profile == Profile::Cell,
            font_family: crate::scene::has_font_family(&options.config),
            width,
            height,
            plot: Area::new(c.pad_x, c.pad_y, width - 2 * c.pad_x, height - 2 * c.pad_y),
            base: Vec::new(),
            pos: Vec::new(),
            frames: Vec::new(),
            ghosts: Vec::new(),
            accels: Vec::new(),
            decels: Vec::new(),
            points: Vec::new(),
            notes: Vec::new(),
            box_area: Area::default(),
            boxed: w.box_lines(),
            specs: w.specs(),
            texts: Vec::new(),
            shown: Vec::new(),
            rects: Vec::new(),
            aligns: Vec::new(),
            lines: Vec::new(),
            box_rects: Vec::new(),
            routes: Vec::new(),
        })
    }

    pub(super) fn project(&self, x: i64, y: i64) -> Pt {
        let fx = clamp(x, 0, FULL_SCALE);
        let fy = clamp(y, 0, FULL_SCALE);
        Pt {
            x: self.plot.x + floor_div(fx * self.plot.w, FULL_SCALE),
            y: self.plot.y + self.plot.h - floor_div(fy * self.plot.h, FULL_SCALE),
        }
    }

    fn clamp_plot(&self, q: Pt) -> Pt {
        let p = self.plot;
        Pt {
            x: clamp(q.x, p.x, p.x + p.w),
            y: clamp(q.y, p.y, p.y + p.h),
        }
    }

    pub(super) fn fit_plot(&self, r: Area) -> Area {
        let p = self.plot;
        Area {
            x: clamp(r.x, p.x, (p.x + p.w - r.w).max(p.x)),
            y: clamp(r.y, p.y, (p.y + p.h - r.h).max(p.y)),
            ..r
        }
    }

    pub(super) fn fit_canvas(&self, r: Area) -> Area {
        Area {
            x: clamp(r.x, 0, (self.width - r.w).max(0)),
            y: clamp(r.y, 0, (self.height - r.h).max(0)),
            ..r
        }
    }

    fn clip_plot(&self, r: Area) -> Area {
        let p = self.plot;
        let (x0, y0) = (r.x.max(p.x), r.y.max(p.y));
        let (x1, y1) = ((r.x + r.w).min(p.x + p.w), (r.y + r.h).min(p.y + p.h));
        Area::new(x0, y0, (x1 - x0).max(0), (y1 - y0).max(0))
    }

    pub(super) fn arrange(&mut self) {
        let w = self.w;
        self.base = w.nodes.iter().map(|n| self.project(n.x, n.y)).collect();
        self.pos = self.base.clone();
        for pipeline in &w.pipelines {
            let frame = self.place_pipeline(pipeline);
            self.frames.push(frame);
        }
        self.ghosts = w
            .trends
            .iter()
            .map(|t| self.project(t.target_x, t.target_y))
            .collect();
        self.accels = w.accelerators.iter().map(|f| self.force_area(f)).collect();
        self.decels = w
            .deaccelerators
            .iter()
            .map(|f| self.force_area(f))
            .collect();
        self.points = w
            .annotations
            .iter()
            .map(|a| self.project(a.x, a.y))
            .collect();
        self.notes = w.notes.iter().map(|n| self.project(n.x, n.y)).collect();
    }

    fn place_pipeline(&mut self, pipeline: &WardleyPipeline) -> Area {
        let mut lo = self.base[pipeline.children[0]];
        let mut hi = lo;
        for &child in &pipeline.children[1..] {
            let b = self.base[child];
            lo = Pt {
                x: lo.x.min(b.x),
                y: lo.y.min(b.y),
            };
            hi = Pt {
                x: hi.x.max(b.x),
                y: hi.y.max(b.y),
            };
        }
        let c = self.c;
        let half = floor_div(c.pipeline_height, 2);
        let top = lo.y - half;
        let frame = self.clip_plot(Area::new(
            lo.x - c.pipeline_pad,
            top,
            hi.x - lo.x + 2 * c.pipeline_pad + c.edge,
            hi.y - lo.y + 2 * half + c.edge,
        ));
        let parent = Pt {
            x: floor_div(lo.x + hi.x, 2),
            y: top - floor_div(c.square_size, 6),
        };
        self.pos[pipeline.parent] = self.clamp_plot(parent);
        frame
    }

    fn force_area(&self, f: &WardleyForce) -> Area {
        let c = self.c;
        let at = self.project(f.x, f.y);
        let half = c.arrow_shaft + c.arrow_head;
        self.fit_plot(Area::new(
            at.x,
            at.y - half,
            c.arrow_width + c.edge,
            2 * half + c.edge,
        ))
    }

    pub(super) fn stage_span(&self, i: usize) -> (i64, i64) {
        let plot = self.plot;
        let at = |boundary: i64| plot.x + floor_div(clamp(boundary, 0, SCALE) * plot.w, SCALE);
        if self.w.boundaries.len() == self.w.stages.len() {
            let start = if i > 0 {
                at(self.w.boundaries[i - 1])
            } else {
                plot.x
            };
            return (start, at(self.w.boundaries[i]));
        }
        let stages = i64::try_from(self.w.stages.len()).unwrap_or(i64::MAX);
        let index = i64::try_from(i).unwrap_or(i64::MAX);
        (
            plot.x + floor_div(index * plot.w, stages),
            plot.x + floor_div((index + 1) * plot.w, stages),
        )
    }

    pub(super) fn style_of(&self, s: &Spec) -> (Role, i32) {
        let px = |units: i64| i32::try_from(units / UNITS_PER_PX).unwrap_or(0);
        match s.kind {
            Kind::Title => (Role::Title, Role::Title.size_px()),
            Kind::AxisX | Kind::AxisY | Kind::Stage => (Role::Label, px(self.c.axis_size)),
            Kind::Note | Kind::Number => (Role::Label, px(self.c.note_size)),
            Kind::Annotation => (Role::Body, px(self.c.note_size)),
            _ => (Role::Body, px(self.c.label_size)),
        }
    }

    pub(super) fn line_height(&self, role: Role, size: i32) -> i64 {
        if self.cell {
            return 1;
        }
        measure::round_half_up(
            i64::from(size) * UNITS_PER_PX * i64::from(role.line_height_px()),
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
                    .map(|run| crate::scene::Run {
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

    pub(super) fn measure_all(&mut self) -> Result<(), LayoutError> {
        let mut texts = Vec::with_capacity(self.specs.len());
        for spec in &self.specs {
            if spec.text.is_empty() {
                texts.push(TextBox::default());
                continue;
            }
            let (role, size) = self.style_of(spec);
            texts.push(self.measure_text(&spec.text, role, size)?);
        }
        self.texts = texts;
        Ok(())
    }

    pub(super) fn reach(&self, n: &WardleyNode) -> i64 {
        if n.pipeline_parent {
            return floor_div(self.c.square_size, 2);
        }
        if !self.cell && n.strategy != WardleyStrategy::None {
            return 2 * self.c.node_radius;
        }
        self.c.node_radius
    }
}
