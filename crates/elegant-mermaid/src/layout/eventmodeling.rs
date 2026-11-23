//! The eventmodeling adapter and family entry (`spec/layout/lanes.md`, Event modeling).
//!
//! [`from_eventmodeling`] authors the model-stage dump: one group box per swimlane with
//! its label, one exclusive node box per frame, and one route per relation. [`layout`]
//! decodes that input again, measures the texts, runs the lanes planner, and fills the
//! dump coordinates.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::Rect;
use crate::measure::{self, Metric, Role};
use crate::model::eventmodeling as me;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, Profile, Run, Scene, SceneBox, SceneLabel, SceneRoute,
    TextRole,
};

use super::input::{Box as InputBox, Input, Label as InputLabel, Route as InputRoute, Spacing};
use super::lanes::{
    self, EventFrame, EventLane, EventModelingInput, EventModelingResult, EventRelation, Text,
};
use super::layered::LayoutError;

const KIND: &str = "eventmodeling";
const LANE_PREFIX: &str = "lane";
const LANE_SHAPE: &str = "lane:";
const DATA_BREAK: &str = "\n\n";

pub(crate) fn from_eventmodeling(
    model: &me::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Input {
    options.set_kind_config(Default::default());
    options.profile = profile;
    let mut input = Input {
        kind: KIND,
        profile,
        direction: Direction::Lr,
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
    for lane in &model.lanes {
        let id = lane_id(lane.index);
        input.boxes.push(InputBox {
            icon: false,
            id: id.clone(),
            role: BoxRole::Group,
            shape: format!("{LANE_SHAPE}{}", lane.index),
            parent: String::new(),
            exclusive: false,
            text: lane.label.clone(),
            direction: String::new(),
        });
        input.labels.push(InputLabel {
            id: format!("{id}.label"),
            owner: id,
            role: TextRole::Label,
            text: lane.label.clone(),
        });
    }
    for frame in &model.frames {
        input.boxes.push(InputBox {
            icon: false,
            id: frame.name.clone(),
            role: BoxRole::Node,
            shape: frame.category.as_str().to_owned(),
            parent: lane_id(frame.lane),
            exclusive: true,
            text: frame_text(frame),
            direction: String::new(),
        });
    }
    for (k, relation) in model.relations.iter().enumerate() {
        input.routes.push(InputRoute {
            id: format!("e{k}"),
            from: model.frames[relation.source].name.clone(),
            to: model.frames[relation.target].name.clone(),
            orthogonal: false,
            marker_start: String::new(),
            marker_end: "point".to_owned(),
            line: "normal".to_owned(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
    input
}

fn lane_id(index: i64) -> String {
    format!("{LANE_PREFIX}{index}")
}

fn frame_text(frame: &me::Frame) -> String {
    let data = frame.data.trim_end_matches('\n');
    if data.is_empty() {
        frame.display.clone()
    } else {
        format!("{}{DATA_BREAK}{data}", frame.display)
    }
}

struct Decoded {
    graph: EventModelingInput,
    lane_at: BTreeMap<String, usize>,
    frame_at: BTreeMap<String, usize>,
}

fn lane_index(shape: &str) -> i64 {
    shape
        .strip_prefix(LANE_SHAPE)
        .and_then(|text| text.parse::<i64>().ok())
        .unwrap_or(0)
}

fn line_height(profile: Profile) -> Result<i32, LayoutError> {
    let key = format!("{}.line_h", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn metric(profile: Profile, role: TextRole) -> Metric {
    if profile == Profile::Cell {
        Metric::cell()
    } else if role == TextRole::Body {
        Metric::for_role(Role::Body)
    } else {
        Metric::for_role(Role::Label)
    }
}

fn measure_text(
    input: &Input,
    text: &str,
    target: i32,
    role: TextRole,
) -> Result<Text, LayoutError> {
    let height = line_height(input.profile)?;
    let metric = crate::scene::configured_metric(metric(input.profile, role), &input.options.config);
    let lines = measure::styled_lines(text, target, metric)
        .map_err(|_| LayoutError::Overflow)?;
    let widest = lines.iter().map(|line| line.width).max().unwrap_or(0);
    let count = i32::try_from(lines.len()).map_err(|_| LayoutError::Overflow)?;
    Ok(Text {
        runs: lines
            .iter()
            .map(|line| {
                line.runs
                    .iter()
                    .map(|run| Run {
                        text: run.text.to_string(),
                        bold: run.bold,
                        italic: run.italic,
                    })
                    .collect()
            })
            .collect(),
        lines: lines.iter().map(|line| line.text.clone()).collect(),
        w: widest,
        h: count.checked_mul(height).ok_or(LayoutError::Overflow)?,
        role,
    })
}

fn decode(input: &Input) -> Result<Decoded, LayoutError> {
    let wraps = lanes::event_modeling_wraps(input.profile)?;
    let mut decoded = Decoded {
        graph: EventModelingInput::default(),
        lane_at: BTreeMap::new(),
        frame_at: BTreeMap::new(),
    };
    for item in &input.boxes {
        if item.role == BoxRole::Group {
            decoded
                .lane_at
                .insert(item.id.clone(), decoded.graph.lanes.len());
            decoded.graph.lanes.push(EventLane {
                id: item.id.clone(),
                index: lane_index(&item.shape),
                label: None,
            });
        } else {
            let frame = decoded.frame(input, item, wraps.frame)?;
            decoded
                .frame_at
                .insert(item.id.clone(), decoded.graph.frames.len());
            decoded.graph.frames.push(frame);
        }
    }
    for route in &input.routes {
        let from = decoded.frame_at.get(&route.from).copied();
        let to = decoded.frame_at.get(&route.to).copied();
        let (Some(from), Some(to)) = (from, to) else {
            return Err(LayoutError::Domain);
        };
        decoded.graph.relations.push(EventRelation {
            id: route.id.clone(),
            from,
            to,
        });
    }
    decoded.labels(input, wraps.lane)?;
    Ok(decoded)
}

impl Decoded {
    fn frame(
        &mut self,
        input: &Input,
        item: &InputBox,
        wrap: i32,
    ) -> Result<EventFrame, LayoutError> {
        let lane = match self.lane_at.get(&item.parent) {
            Some(&lane) => lane,
            None => {
                let lane = self.graph.lanes.len();
                self.lane_at.insert(item.parent.clone(), lane);
                self.graph.lanes.push(EventLane {
                    id: String::new(),
                    index: i64::try_from(lane).map_err(|_| LayoutError::Overflow)?,
                    label: None,
                });
                lane
            }
        };
        let (name, data) = match item.text.split_once(DATA_BREAK) {
            Some((name, data)) => (name, Some(data)),
            None => (item.text.as_str(), None),
        };
        Ok(EventFrame {
            id: item.id.clone(),
            lane,
            category: item.shape.clone(),
            name: measure_text(input, name, wrap, TextRole::Label)?,
            data: data
                .map(|data| {
                    measure_text(input, &data.replace('\n', "<br>"), wrap, TextRole::Body)
                })
                .transpose()?,
        })
    }

    fn labels(&mut self, input: &Input, wrap: i32) -> Result<(), LayoutError> {
        for label in &input.labels {
            let Some(&lane) = self.lane_at.get(&label.owner) else {
                return Err(LayoutError::Domain);
            };
            let text = measure_text(input, &label.text, wrap, label.role)?;
            self.graph.lanes[lane].label = Some(text);
        }
        Ok(())
    }

    fn rect(&self, item: &InputBox, result: &EventModelingResult) -> Result<Rect, LayoutError> {
        let (list, at) = if item.role == BoxRole::Group {
            (&result.lanes, self.lane_at.get(&item.id))
        } else {
            (&result.frames, self.frame_at.get(&item.id))
        };
        at.and_then(|&index| list.get(index))
            .copied()
            .ok_or(LayoutError::Domain)
    }

    fn dump(&self, input: &Input, result: &EventModelingResult) -> Result<Dump, LayoutError> {
        let mut options = input.options.clone();
        options.profile = input.profile;
        options.direction = input.direction;
        let mut dump = Dump::new(KIND, options);
        for item in &input.boxes {
            dump.boxes.push(SceneBox {
                id: item.id.clone(),
                role: item.role,
                rect: self.rect(item, result)?,
                parent: item.parent.clone(),
                exclusive: item.exclusive,
            });
        }
        for (index, route) in input.routes.iter().enumerate() {
            dump.routes.push(SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: route.orthogonal,
                points: result.routes[index].clone(),
                marker_start: route.marker_start.clone(),
                marker_end: route.marker_end.clone(),
                stroke: route.line.clone(),
            });
        }
        for label in &input.labels {
            let lane = *self.lane_at.get(&label.owner).ok_or(LayoutError::Domain)?;
            let text = self.graph.lanes[lane]
                .label
                .as_ref()
                .ok_or(LayoutError::Domain)?;
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect: result.lane_labels[lane],
                lines: text.lines.clone(),
            });
        }
        Ok(dump)
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let decoded = decode(input)?;
    let result = lanes::event_modeling(&decoded.graph, input.profile)?;
    let dump = decoded.dump(input, &result)?;
    Ok((Scene::new(result.canvas, dump, result.groups), false))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
