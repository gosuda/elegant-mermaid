//! The Wardley payload of the chart family (`spec/layout/charts.md`) and its dump
//! skeleton: boxes, routes, and labels in declaration order, with no coordinates.

use crate::scene::{BoxRole, SceneBox, SceneLabel, SceneRoute};

use super::ZERO_RECT;

pub(super) const PLOT_ID: &str = "plot";
pub(super) const BOX_ID: &str = "ab";
const AXIS_X: &str = "Evolution";
const AXIS_Y: &str = "Visibility";
pub(super) const TITLE_ID: &str = "title";
const AXIS_X_ID: &str = "x.title";
const AXIS_Y_ID: &str = "y.title";
pub(super) const MARKER_POINT: &str = "point";
const MARKER_NONE: &str = "none";
pub(super) const STROKE_DASHED: &str = "dashed";
const STROKE_DOTTED: &str = "dotted";
pub(super) const FULL_SCALE: i64 = 100_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum WardleyStrategy {
    #[default]
    None,
    Build,
    Buy,
    Outsource,
    Market,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum WardleyFlow {
    #[default]
    None,
    Forward,
    Backward,
    Bidirectional,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WardleyNode {
    pub label: String,
    pub x: i64,
    pub y: i64,
    pub anchor: bool,
    pub inertia: bool,
    pub pipeline_parent: bool,
    pub has_offset: bool,
    pub offset_x: i64,
    pub offset_y: i64,
    pub strategy: WardleyStrategy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyLink {
    pub from: usize,
    pub to: usize,
    pub dashed: bool,
    pub label: String,
    pub flow: WardleyFlow,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyPipeline {
    pub parent: usize,
    pub children: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyTrend {
    pub node: usize,
    pub target_x: i64,
    pub target_y: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyNote {
    pub text: String,
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyForce {
    pub name: String,
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WardleyAnnotation {
    pub number: i64,
    pub x: i64,
    pub y: i64,
    pub text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WardleyPoint {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Wardley {
    pub title: String,
    pub stages: Vec<String>,
    pub boundaries: Vec<i64>,
    pub nodes: Vec<WardleyNode>,
    pub pipelines: Vec<WardleyPipeline>,
    pub links: Vec<WardleyLink>,
    pub trends: Vec<WardleyTrend>,
    pub notes: Vec<WardleyNote>,
    pub accelerators: Vec<WardleyForce>,
    pub deaccelerators: Vec<WardleyForce>,
    pub annotations: Vec<WardleyAnnotation>,
    pub box_point: Option<WardleyPoint>,
}

pub struct WardleySkeleton {
    pub boxes: Vec<SceneBox>,
    pub routes: Vec<SceneRoute>,
    pub labels: Vec<SceneLabel>,
}

fn indexed(prefix: &str, index: usize) -> String {
    format!("{prefix}{index}")
}

pub(super) fn node_id(k: usize) -> String {
    indexed("n", k)
}

pub(super) fn pipeline_id(k: usize) -> String {
    indexed("pl", k)
}

pub(super) fn ghost_id(k: usize) -> String {
    indexed("tg", k)
}

pub(super) fn accelerator_id(k: usize) -> String {
    indexed("ac", k)
}

pub(super) fn deaccelerator_id(k: usize) -> String {
    indexed("de", k)
}

pub(super) fn annotation_id(k: usize) -> String {
    indexed("an", k)
}

pub(super) fn annotation_prefix(number: i64) -> String {
    format!("{number}. ")
}

fn annotation_display(a: &WardleyAnnotation) -> String {
    if a.text.is_empty() {
        return String::new();
    }
    format!("{}{}", annotation_prefix(a.number), a.text)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Title,
    AxisX,
    AxisY,
    Stage,
    Node,
    Link,
    Note,
    Number,
    Annotation,
    Accelerator,
    Deaccelerator,
}

#[derive(Debug, Clone)]
pub(super) struct Spec {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub kind: Kind,
    pub index: usize,
}

impl Wardley {
    pub(super) fn box_lines(&self) -> Vec<usize> {
        let mut shown: Vec<usize> = (0..self.annotations.len())
            .filter(|&i| !self.annotations[i].text.is_empty())
            .collect();
        shown.sort_by_key(|&i| self.annotations[i].number);
        shown
    }

    pub(super) fn shows_box(&self) -> bool {
        self.box_point.is_some() && !self.box_lines().is_empty()
    }

    fn pipeline_of(&self, node: usize) -> Option<usize> {
        if self.nodes[node].pipeline_parent {
            return None;
        }
        self.pipelines
            .iter()
            .position(|p| p.children.contains(&node))
    }

    pub(super) fn pipeline_links(&self, k: usize) -> Vec<(usize, usize)> {
        let mut children = self.pipelines[k].children.clone();
        children.sort_by_key(|&c| self.nodes[c].x);
        children.windows(2).map(|pair| (pair[0], pair[1])).collect()
    }

    pub fn skeleton(&self) -> WardleySkeleton {
        WardleySkeleton {
            boxes: self.skeleton_boxes(),
            routes: self.skeleton_routes(),
            labels: self.skeleton_labels(),
        }
    }

    fn plot_child(id: String) -> SceneBox {
        SceneBox {
            id,
            role: BoxRole::Node,
            rect: ZERO_RECT,
            parent: PLOT_ID.to_owned(),
            exclusive: false,
        }
    }

    fn free_box(id: String) -> SceneBox {
        SceneBox {
            id,
            role: BoxRole::Node,
            rect: ZERO_RECT,
            parent: String::new(),
            exclusive: false,
        }
    }

    pub(super) fn skeleton_boxes(&self) -> Vec<SceneBox> {
        let mut boxes = vec![Self::free_box(PLOT_ID.to_owned())];
        boxes.extend((0..self.pipelines.len()).map(|k| Self::plot_child(pipeline_id(k))));
        for k in 0..self.nodes.len() {
            let parent = self
                .pipeline_of(k)
                .map_or_else(|| PLOT_ID.to_owned(), pipeline_id);
            boxes.push(SceneBox {
                parent,
                ..Self::free_box(node_id(k))
            });
        }
        boxes.extend((0..self.trends.len()).map(|k| Self::plot_child(ghost_id(k))));
        boxes.extend((0..self.accelerators.len()).map(|k| Self::free_box(accelerator_id(k))));
        boxes.extend((0..self.deaccelerators.len()).map(|k| Self::free_box(deaccelerator_id(k))));
        boxes.extend((0..self.annotations.len()).map(|k| Self::plot_child(annotation_id(k))));
        if self.shows_box() {
            boxes.push(Self::free_box(BOX_ID.to_owned()));
        }
        boxes
    }

    fn route(
        id: String,
        from: String,
        to: String,
        start: &str,
        end: &str,
        stroke: &str,
    ) -> SceneRoute {
        SceneRoute {
            id,
            from,
            to,
            orthogonal: false,
            points: Vec::new(),
            marker_start: start.to_owned(),
            marker_end: end.to_owned(),
            stroke: stroke.to_owned(),
        }
    }

    pub(super) fn skeleton_routes(&self) -> Vec<SceneRoute> {
        let mut routes = Vec::new();
        for k in 0..self.pipelines.len() {
            for (j, (a, b)) in self.pipeline_links(k).into_iter().enumerate() {
                routes.push(Self::route(
                    format!("{}.l{j}", pipeline_id(k)),
                    node_id(a),
                    node_id(b),
                    MARKER_NONE,
                    MARKER_NONE,
                    STROKE_DOTTED,
                ));
            }
        }
        for (k, l) in self.links.iter().enumerate() {
            let start = if matches!(l.flow, WardleyFlow::Backward | WardleyFlow::Bidirectional) {
                MARKER_POINT
            } else {
                MARKER_NONE
            };
            let end = if matches!(l.flow, WardleyFlow::Forward | WardleyFlow::Bidirectional) {
                MARKER_POINT
            } else {
                MARKER_NONE
            };
            let stroke = if l.dashed { STROKE_DASHED } else { "" };
            routes.push(Self::route(
                indexed("l", k),
                node_id(l.from),
                node_id(l.to),
                start,
                end,
                stroke,
            ));
        }
        for (k, t) in self.trends.iter().enumerate() {
            routes.push(Self::route(
                indexed("tr", k),
                node_id(t.node),
                ghost_id(k),
                MARKER_NONE,
                MARKER_POINT,
                STROKE_DOTTED,
            ));
        }
        routes
    }

    fn skeleton_labels(&self) -> Vec<SceneLabel> {
        self.specs()
            .into_iter()
            .map(|s| SceneLabel {
                id: s.id,
                owner: s.owner,
                text: s.text,
                rect: ZERO_RECT,
                lines: Vec::new(),
            })
            .collect()
    }

    pub(super) fn specs(&self) -> Vec<Spec> {
        let mut specs = Vec::new();
        let mut add = |kind: Kind, index: usize, id: String, owner: String, text: String| {
            specs.push(Spec {
                id,
                owner,
                text,
                kind,
                index,
            });
        };
        let plot = || PLOT_ID.to_owned();
        if !self.title.is_empty() {
            add(
                Kind::Title,
                0,
                TITLE_ID.to_owned(),
                plot(),
                self.title.clone(),
            );
        }
        add(
            Kind::AxisX,
            0,
            AXIS_X_ID.to_owned(),
            plot(),
            AXIS_X.to_owned(),
        );
        add(
            Kind::AxisY,
            0,
            AXIS_Y_ID.to_owned(),
            plot(),
            AXIS_Y.to_owned(),
        );
        for (k, stage) in self.stages.iter().enumerate() {
            add(Kind::Stage, k, indexed("st", k), plot(), stage.clone());
        }
        for (k, n) in self.nodes.iter().enumerate() {
            let id = node_id(k);
            add(Kind::Node, k, format!("{id}.label"), id, n.label.clone());
        }
        for (k, l) in self
            .links
            .iter()
            .enumerate()
            .filter(|(_, l)| !l.label.is_empty())
        {
            let id = indexed("l", k);
            add(Kind::Link, k, format!("{id}.label"), id, l.label.clone());
        }
        for (k, n) in self.notes.iter().enumerate() {
            add(Kind::Note, k, indexed("note", k), plot(), n.text.clone());
        }
        for (k, a) in self.annotations.iter().enumerate() {
            let id = annotation_id(k);
            add(
                Kind::Number,
                k,
                format!("{id}.label"),
                id.clone(),
                a.number.to_string(),
            );
            let owner = if self.shows_box() {
                BOX_ID.to_owned()
            } else {
                id.clone()
            };
            add(
                Kind::Annotation,
                k,
                format!("{id}.text"),
                owner,
                annotation_display(a),
            );
        }
        for (k, f) in self.accelerators.iter().enumerate() {
            let id = accelerator_id(k);
            add(
                Kind::Accelerator,
                k,
                format!("{id}.label"),
                id,
                f.name.clone(),
            );
        }
        for (k, f) in self.deaccelerators.iter().enumerate() {
            let id = deaccelerator_id(k);
            add(
                Kind::Deaccelerator,
                k,
                format!("{id}.label"),
                id,
                f.name.clone(),
            );
        }
        specs
    }
}
