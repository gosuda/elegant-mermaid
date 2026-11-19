//! The `ishikawa` kind: the model-stage input, the measured fishbone layout, and
//! the drawn scene (`spec/layout/tree.md`, ishikawa requirements).
//!
//! The model stage writes the effect and cause boxes in statement order,
//! then one zero-size anchor box per node. Anchor `a_k` sits where bone `e_k`
//! leaves the spine or its parent rib, so every route runs from its anchor to
//! the label box it serves.

mod paint;

use super::input::{Box, Input, Label, Route, Spacing};
use super::layered::LayoutError;
use super::tree::{self, IshikawaParams};
use crate::geom::{COORD_LIMIT, GeomError, Rect};
use crate::measure::{Metric, Role, StyledLine, styled_lines, wrap_target};
use crate::model::ishikawa::Model;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, Profile, Run, Scene, SceneBox, SceneRoute, TextRole,
};

const KIND: &str = "ishikawa";
const EFFECT: &str = "effect";
const CAUSE: &str = "cause:";
const ANCHOR: &str = "anchor";
const MARKER: &str = "point";

pub fn from_ishikawa(
    model: &Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config.clear();
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
        let shape = if node.index > 0 {
            format!("{CAUSE}{}", node.depth)
        } else {
            EFFECT.to_owned()
        };
        input.boxes.push(label_box(&id, &shape));
        if node.label != id {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id,
                role: TextRole::Label,
                text: node.label.clone(),
            });
        }
    }
    if model.nodes.len() > 1 {
        add_routes(&mut input, model);
    }
    Ok(input)
}

fn box_id(index: usize) -> String {
    format!("n{index}")
}

fn anchor_id(index: usize) -> String {
    format!("a{index}")
}

fn anchor_box(id: &str) -> Box {
    Box {
        id: id.to_owned(),
        role: BoxRole::Node,
        shape: ANCHOR.to_owned(),
        icon: false,
        parent: String::new(),
        exclusive: false,
        text: String::new(),
        direction: String::new(),
    }
}

fn label_box(id: &str, shape: &str) -> Box {
    Box {
        shape: shape.to_owned(),
        exclusive: true,
        ..anchor_box(id)
    }
}

fn add_routes(input: &mut Input, model: &Model) {
    for node in &model.nodes {
        input.boxes.push(anchor_box(&anchor_id(node.index)));
        let (orthogonal, marker_start) = if node.index == 0 {
            (true, String::new())
        } else {
            (node.depth % 2 == 0, MARKER.to_owned())
        };
        input.routes.push(Route {
            id: format!("e{}", node.index),
            from: anchor_id(node.index),
            to: box_id(node.index),
            orthogonal,
            marker_start,
            marker_end: "none".to_owned(),
            line: "normal".to_owned(),
            min_length: 0,
            from_side: None,
            to_side: None,
        });
    }
}

struct Constants {
    pad_x: i32,
    pad_y: i32,
    border: i32,
    min_w: i32,
    min_h: i32,
    line_height: i32,
    margin: i32,
    corner: i32,
    params: IshikawaParams,
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
    fn load(profile: Profile) -> Result<Self, GeomError> {
        let get = |name: &str| constant(profile, name);
        Ok(Self {
            pad_x: get("node_pad_x")?,
            pad_y: get("node_pad_y")?,
            border: get("node_border")?,
            min_w: get("node_min_w")?,
            min_h: get("node_min_h")?,
            line_height: get("line_h")?,
            margin: get("canvas_margin")?,
            corner: get("corner_radius")?,
            params: IshikawaParams {
                spine_base: get("ishikawa.spine_base_length")?,
                rib_min: get("ishikawa.rib_min_length")?,
                rib_pool: get("ishikawa.rib_pool")?,
                min_spacing: get("ishikawa.cause_min_spacing")?,
                bone_stub: get("ishikawa.bone_stub")?,
                bone_base: get("ishikawa.bone_base")?,
                bone_per_child: get("ishikawa.bone_per_child")?,
                inset: get("ishikawa.spine_inset")?,
                cos: get("ishikawa.rib_cos_q15")?,
                sin: get("ishikawa.rib_sin_q15")?,
            },
        })
    }
}

struct Plan<'a> {
    input: &'a Input,
    c: Constants,
    count: usize,
    depth: Vec<usize>,
    runs: Vec<Vec<Vec<Run>>>,
    nodes: Vec<tree::Node>,
}

fn cause_depth(shape: &str) -> Option<usize> {
    let depth = shape.strip_prefix(CAUSE)?.parse::<usize>().ok()?;
    (1..=tree::ISHIKAWA_MAX_DEPTH)
        .contains(&depth)
        .then_some(depth)
}

fn runs_of(lines: &[StyledLine<'_>]) -> Vec<Vec<Run>> {
    lines
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
        .collect()
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
            c: Constants::load(input.profile)?,
            count: 0,
            depth: Vec::new(),
            runs: Vec::new(),
            nodes: Vec::new(),
        };
        plan.read_depths()?;
        plan.measure()?;
        Ok(plan)
    }

    /// Reads the effect and cause boxes, then requires only anchors after them.
    fn read_depths(&mut self) -> Result<(), GeomError> {
        let boxes = &self.input.boxes;
        if boxes
            .first()
            .is_some_and(|b| b.shape == EFFECT || b.shape.is_empty())
        {
            self.depth.push(0);
            self.count = 1;
        }
        while self.count > 0 {
            let Some(depth) = boxes.get(self.count).and_then(|b| cause_depth(&b.shape)) else {
                break;
            };
            self.depth.push(depth);
            self.count += 1;
        }
        if boxes.iter().skip(self.count).any(|b| b.shape != ANCHOR) {
            return Err(GeomError::Domain);
        }
        Ok(())
    }

    fn label_text(&self, b: &'a Box) -> &'a str {
        self.input
            .labels
            .iter()
            .find(|label| label.owner == b.id)
            .map_or(b.id.as_str(), |label| label.text.as_str())
    }

    fn parents(&self) -> Result<Vec<Option<usize>>, GeomError> {
        let mut parents = Vec::with_capacity(self.count);
        let mut path: Vec<usize> = Vec::new();
        for (i, d) in self.depth.iter().copied().enumerate() {
            if d > path.len() {
                return Err(GeomError::Domain);
            }
            path.truncate(d);
            path.push(i);
            parents.push(d.checked_sub(1).and_then(|up| path.get(up).copied()));
        }
        Ok(parents)
    }

    fn measure(&mut self) -> Result<(), GeomError> {
        let metric = metric(self.input.profile);
        let max_width = match self.input.profile {
            Profile::Cell => i32::try_from(self.input.options.max_width).unwrap_or(i32::MAX),
            Profile::Vector => 0,
        };
        let wrap = wrap_target(metric, 0, max_width);
        let parents = self.parents()?;
        let boxes = &self.input.boxes[..self.count];
        for (i, (b, parent)) in boxes.iter().zip(parents).enumerate() {
            let lines =
                styled_lines(self.label_text(b), wrap, metric).map_err(|_| GeomError::Overflow)?;
            let widest = lines.iter().map(|line| line.width).max().unwrap_or(0);
            let (width, height) = self.box_size(i, widest, lines.len())?;
            self.runs.push(runs_of(&lines));
            self.nodes.push(tree::Node {
                parent,
                width,
                height,
            });
        }
        Ok(())
    }

    /// The head and the causes carry a border; bare sub-causes only their text.
    fn box_size(
        &self,
        index: usize,
        text_width: i32,
        line_count: usize,
    ) -> Result<(i32, i32), GeomError> {
        let c = &self.c;
        let lines = i64::try_from(line_count.max(1)).map_err(|_| GeomError::Overflow)?;
        let mut w = i64::from(text_width) + 2 * i64::from(c.pad_x);
        let mut h = lines * i64::from(c.line_height);
        if self.depth[index] <= 1 {
            w = (w + 2 * i64::from(c.border)).max(i64::from(c.min_w));
            h = (h + 2 * i64::from(c.pad_y) + 2 * i64::from(c.border)).max(i64::from(c.min_h));
        }
        if w > COORD_LIMIT || h > COORD_LIMIT {
            return Err(GeomError::Overflow);
        }
        let narrow = |v: i64| i32::try_from(v.max(1)).map_err(|_| GeomError::Overflow);
        Ok((narrow(w)?, narrow(h)?))
    }

    fn node_of(&self, id: &str) -> Option<usize> {
        self.input.boxes[..self.count]
            .iter()
            .position(|b| b.id == id)
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let plan = Plan::new(input)?;
    let mut placed = tree::ishikawa(&plan.nodes, plan.c.params)?;
    let canvas = tree::normalize(&mut placed, plan.c.margin)?;
    let dump = plan.dump(&placed)?;
    let groups = plan.groups(&dump);
    Ok((Scene::new(canvas, dump, groups), false))
}

impl Plan<'_> {
    fn dump(&self, placed: &tree::Layout) -> Result<Dump, GeomError> {
        let mut dump = Dump::new(KIND, self.input.options.clone());
        for (i, b) in self.input.boxes.iter().enumerate() {
            let rect = placed.boxes.get(i).copied().filter(|_| i < self.count);
            dump.boxes.push(SceneBox {
                id: b.id.clone(),
                role: b.role,
                rect: rect.unwrap_or(Rect {
                    x: 0,
                    y: 0,
                    w: 0,
                    h: 0,
                }),
                parent: String::new(),
                exclusive: b.exclusive,
            });
        }
        for (offset, route) in self.input.routes.iter().enumerate() {
            let anchor = self.count + offset;
            let to = self.node_of(&route.to).ok_or(GeomError::Domain)?;
            let points = placed.routes.get(to).cloned().unwrap_or_default();
            let (Some(start), Some(slot)) = (points.first(), dump.boxes.get_mut(anchor)) else {
                return Err(GeomError::Domain);
            };
            if slot.id != route.from || points.len() < 2 {
                return Err(GeomError::Domain);
            }
            slot.rect = Rect {
                x: start.x,
                y: start.y,
                w: 0,
                h: 0,
            };
            dump.routes.push(SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: route.orthogonal,
                points,
                marker_start: String::new(),
                marker_end: String::new(),
                stroke: String::new(),
            });
        }
        Ok(dump)
    }
}

#[cfg(test)]
mod tests;
