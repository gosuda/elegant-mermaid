//! The `mindmap` kind: the model-stage input, the measured tidy-tree layout, and the
//! drawn scene (`spec/layout/tree.md`, requirements tree-05 through tree-13, tree-45, tree-46).

mod paint;

use std::collections::BTreeMap;

use super::input::{Box, Input, Label, Route, Spacing};
use super::layered::LayoutError;
use super::tree::{self, Gaps};
use crate::geom::{COORD_LIMIT, GeomError, Rect};
use crate::measure::{Metric, Role, styled_lines};
use crate::model::mindmap::Model;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox, SceneRoute,
    TextRole,
};

const KIND: &str = "mindmap";
const PADDING_KEY: &str = "padding";
const MAX_WIDTH_KEY: &str = "maxNodeWidth";
const PIXEL_UNITS: i64 = 64;

pub fn from_mindmap(
    model: &Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config = BTreeMap::new();
    if let Some(value) = model.config.max_node_width {
        options
            .config
            .insert(MAX_WIDTH_KEY.to_owned(), DumpValue::Integer(value));
    }
    if let Some(value) = model.config.padding {
        options
            .config
            .insert(PADDING_KEY.to_owned(), DumpValue::Integer(value));
    }
    options.profile = profile;
    options.direction = Direction::Tb;
    let mut input = Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    };
    for node in &model.nodes {
        let id = box_id(node.index);
        input.boxes.push(Box {
            id: id.clone(),
            role: BoxRole::Node,
            shape: node.shape.as_str().to_owned(),
            icon: false,
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        });
        if node.label != id {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: node.label.clone(),
            });
        }
        if let Some(parent) = node.parent {
            input.routes.push(Route {
                id: format!("e{}", input.routes.len()),
                from: box_id(parent),
                to: id,
                orthogonal: true,
                marker_start: String::new(),
                marker_end: "none".to_owned(),
                line: "normal".to_owned(),
                min_length: 0,
                from_side: None,
                to_side: None,
            });
        }
    }
    Ok(input)
}

fn box_id(index: usize) -> String {
    format!("n{index}")
}

struct Constants {
    padding: i32,
    max_width: i32,
    level_gap: i32,
    sibling_gap: i32,
    line_height: i32,
    margin: i32,
    corner: i32,
}

fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

impl Constants {
    fn load(input: &Input) -> Result<Self, GeomError> {
        let profile = input.profile;
        let mut constants = Self {
            padding: constant(profile, "mindmap.padding")?,
            max_width: constant(profile, "mindmap.max_node_width")?,
            level_gap: constant(profile, "mindmap.level_gap")?,
            sibling_gap: constant(profile, "mindmap.sibling_gap")?,
            line_height: constant(profile, "line_h")?,
            margin: constant(profile, "canvas_margin")?,
            corner: constant(profile, "corner_radius")?,
        };
        if profile == Profile::Vector {
            constants.apply_config(&input.options.config)?;
        }
        Ok(constants)
    }

    fn apply_config(&mut self, config: &BTreeMap<String, DumpValue>) -> Result<(), GeomError> {
        for (key, value) in config {
            let target = match key.as_str() {
                PADDING_KEY => &mut self.padding,
                MAX_WIDTH_KEY => &mut self.max_width,
                _ => continue,
            };
            let DumpValue::Integer(px) = value else {
                return Err(GeomError::Overflow);
            };
            let units = px.checked_mul(PIXEL_UNITS).ok_or(GeomError::Overflow)?;
            if *px < 0 || units > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            *target = i32::try_from(units).map_err(|_| GeomError::Overflow)?;
        }
        Ok(())
    }
}

/// One measured node: its wrapped runs and the tidy-tree node built from them.
struct Measured {
    runs: Vec<Vec<Run>>,
}

struct Plan<'a> {
    input: &'a Input,
    c: Constants,
    index: BTreeMap<&'a str, usize>,
    measured: Vec<Measured>,
    nodes: Vec<tree::Node>,
}

fn metric(profile: Profile) -> Metric {
    match profile {
        Profile::Cell => Metric::Cell,
        Profile::Vector => Metric::for_role(Role::Label),
    }
}

impl<'a> Plan<'a> {
    fn new(input: &'a Input) -> Result<Self, GeomError> {
        let mut plan = Self {
            input,
            c: Constants::load(input)?,
            index: input
                .boxes
                .iter()
                .enumerate()
                .map(|(i, b)| (b.id.as_str(), i))
                .collect(),
            measured: Vec::new(),
            nodes: Vec::new(),
        };
        plan.measure()?;
        Ok(plan)
    }

    fn label_text(&self, b: &'a Box) -> &'a str {
        self.input
            .labels
            .iter()
            .find(|label| label.owner == b.id)
            .map_or(b.id.as_str(), |label| label.text.as_str())
    }

    fn measure(&mut self) -> Result<(), GeomError> {
        let mut parents: Vec<Option<usize>> = vec![None; self.input.boxes.len()];
        for route in &self.input.routes {
            let (Some(to), Some(from)) = (
                self.index.get(route.to.as_str()),
                self.index.get(route.from.as_str()),
            ) else {
                return Err(GeomError::Domain);
            };
            parents[*to] = Some(*from);
        }
        let wrap = (i64::from(self.c.max_width) - 2 * i64::from(self.c.padding)).max(1);
        let wrap = i32::try_from(wrap).map_err(|_| GeomError::Overflow)?;
        for (b, parent) in self.input.boxes.iter().zip(parents) {
            let lines = styled_lines(self.label_text(b), wrap, metric(self.input.profile))?;
            let width = lines.iter().map(|line| line.width).max().unwrap_or(0);
            let (w, h) = self.box_size(width, lines.len())?;
            self.measured.push(Measured {
                runs: lines
                    .iter()
                    .map(|line| {
                        line.runs
                            .iter()
                            .map(|run| Run {
                                text: run.text.to_owned(),
                                bold: run.bold,
                                italic: run.italic,
                            })
                            .collect()
                    })
                    .collect(),
            });
            self.nodes.push(tree::Node {
                parent,
                width: w,
                height: h,
            });
        }
        Ok(())
    }

    fn box_size(&self, text_width: i32, line_count: usize) -> Result<(i32, i32), GeomError> {
        let padding = i64::from(self.c.padding);
        let w = i64::from(self.c.max_width).min(i64::from(text_width) + 2 * padding);
        let lines = i64::try_from(line_count.max(1)).map_err(|_| GeomError::Overflow)?;
        let h = lines * i64::from(self.c.line_height) + 2 * padding;
        if h > COORD_LIMIT || w > COORD_LIMIT {
            return Err(GeomError::Overflow);
        }
        let narrow = |v: i64| i32::try_from(v.max(1)).map_err(|_| GeomError::Overflow);
        Ok((narrow(w)?, narrow(h)?))
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let plan = Plan::new(input)?;
    let gaps = Gaps {
        level: plan.c.level_gap,
        sibling: plan.c.sibling_gap,
    };
    let mut placed = tree::mindmap(&plan.nodes, gaps)?;
    let canvas = tree::normalize(&mut placed, plan.c.margin)?;
    let mut dump = blank_dump(input);
    for (target, rect) in dump.boxes.iter_mut().zip(&placed.boxes) {
        target.rect = *rect;
    }
    for (target, route) in dump.routes.iter_mut().zip(&input.routes) {
        let to = plan.index.get(route.to.as_str()).ok_or(GeomError::Domain)?;
        target.points = placed.routes.get(*to).cloned().unwrap_or_default();
    }
    let groups = plan.groups(&dump);
    Ok((Scene::new(canvas, dump, groups), false))
}

fn blank_dump(input: &Input) -> Dump {
    let mut dump = Dump::new(KIND, input.options.clone());
    dump.boxes = input
        .boxes
        .iter()
        .map(|b| SceneBox {
            id: b.id.clone(),
            role: b.role,
            rect: Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            },
            parent: String::new(),
            exclusive: b.exclusive,
        })
        .collect();
    dump.routes = input
        .routes
        .iter()
        .map(|r| SceneRoute {
            id: r.id.clone(),
            from: r.from.clone(),
            to: r.to.clone(),
            orthogonal: r.orthogonal,
            points: Vec::new(),
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        })
        .collect();
    dump
}

#[cfg(test)]
mod tests;
