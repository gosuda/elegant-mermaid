//! The chart-family model: the closed kind list and the payload that the chart layout
//! reads (`spec/layout/charts.md`). Numbers are integers in thousandths.

use std::collections::BTreeMap;

use crate::scene::DumpValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    XyChart,
    Radar,
    Gantt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chart {
    pub kind: Kind,
    pub title: String,
    pub config: BTreeMap<String, DumpValue>,
    pub xy: Option<Xy>,
    pub radar: Option<Radar>,
    pub gantt: Option<Gantt>,
}

impl Chart {
    pub fn integer(&self, key: &str) -> Option<i64> {
        match self.config.get(key) {
            Some(DumpValue::Integer(value)) => Some(*value),
            _ => None,
        }
    }

    pub fn boolean(&self, key: &str) -> Option<bool> {
        match self.config.get(key) {
            Some(DumpValue::Bool(value)) => Some(*value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Orientation {
    #[default]
    Vertical,
    Horizontal,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Xy {
    pub orientation: Orientation,
    pub x_title: String,
    pub y_title: String,
    pub x_axis: XAxis,
    pub y_axis: YAxis,
    pub plots: Vec<Plot>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct XAxis {
    pub band: bool,
    pub categories: Vec<String>,
    pub min: i64,
    pub max: i64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct YAxis {
    pub min: i64,
    pub max: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlotKind {
    Bar,
    Line,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Point {
    pub present: bool,
    pub slot: Option<usize>,
    pub has_x: bool,
    pub x: i64,
    pub value: i64,
    pub label: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plot {
    pub kind: PlotKind,
    pub title: String,
    pub points: Vec<Point>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Graticule {
    #[default]
    Circle,
    Polygon,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Radar {
    pub axes: Vec<String>,
    pub curves: Vec<RadarCurve>,
    pub show_legend: bool,
    pub ticks: i64,
    pub has_max: bool,
    pub max: i64,
    pub min: i64,
    pub graticule: Graticule,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RadarCurve {
    pub label: String,
    pub values: Vec<i64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GanttRowKind {
    Section,
    Task,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GanttRow {
    pub kind: GanttRowKind,
    pub index: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GanttTask {
    pub label: String,
    pub section: Option<usize>,
    pub start: i64,
    pub end: i64,
    pub render_end: i64,
    pub milestone: bool,
    pub vert: bool,
    pub crit: bool,
    pub active: bool,
    pub done: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Gantt {
    pub sections: Vec<String>,
    pub tasks: Vec<GanttTask>,
    pub rows: Vec<GanttRow>,
    pub excludes: Vec<String>,
    pub includes: Vec<String>,
    pub weekend: String,
    pub weekday: String,
    pub top_axis: bool,
    pub tick_every: i64,
    pub tick_unit: String,
    pub axis_form: String,
}
