//! The timeline adapter and family entry (`spec/layout/lanes.md`, Timeline).
//!
//! [`from_timeline`] authors the model-stage dump: one box per title, section, period, and
//! event, each carrying its unwrapped text, and one dotted route per event. [`layout`]
//! decodes that input again, measures the texts, runs the lanes planner, and fills the
//! dump coordinates.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{GeomError, Rect};
use crate::measure::{self, Metric, Role};
use crate::model::timeline as mt;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, Profile, Run, Scene, SceneBox, SceneRoute, TextRole,
};

use super::input::{Box as InputBox, Input, Route as InputRoute, Spacing};
use super::lanes::{
    self, Text, TimelineEvent, TimelineInput, TimelinePeriod, TimelineResult, TimelineSection,
    TimelineTitle,
};
use super::layered::LayoutError;

const KIND: &str = "timeline";
const TITLE_ID: &str = "title";
const SHAPE_TITLE: &str = "title";
const SHAPE_SECTION: &str = "section";
const SHAPE_PERIOD: &str = "period";
const SHAPE_EVENT: &str = "event";
const LINK_STROKE: &str = "dotted";
const UNITS_PER_PX: i32 = 64;

pub(crate) fn from_timeline(
    model: &mt::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(BTreeMap::new());
    options.profile = profile;
    let direction = if model.vertical() {
        Direction::Tb
    } else {
        Direction::Lr
    };
    let mut input = Input {
        kind: KIND,
        profile,
        direction,
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
    if !model.title_label.is_empty() {
        input
            .boxes
            .push(card_box(TITLE_ID, SHAPE_TITLE, &model.title_label));
    }
    for (s, section) in model.sections.iter().enumerate() {
        input
            .boxes
            .push(card_box(&format!("s{s}"), SHAPE_SECTION, &section.label));
    }
    let mut links = 0;
    for (i, period) in model.periods.iter().enumerate() {
        let head = card_box(
            &format!("p{i}"),
            &period_shape(period.section),
            &period.label,
        );
        let head_id = head.id.clone();
        input.boxes.push(head);
        let mut previous = head_id.clone();
        for (k, event) in period.events.iter().enumerate() {
            let next = card_box(&format!("{head_id}.e{k}"), SHAPE_EVENT, &event.label);
            input.routes.push(InputRoute {
                id: format!("e{links}"),
                from: previous.clone(),
                to: next.id.clone(),
                orthogonal: true,
                marker_start: String::new(),
                marker_end: String::new(),
                line: LINK_STROKE.to_owned(),
                min_length: 1,
                from_side: None,
                to_side: None,
            });
            links += 1;
            if !model.vertical() {
                previous = next.id.clone();
            }
            input.boxes.push(next);
        }
    }
    Ok(input)
}

fn card_box(id: &str, shape: &str, text: &str) -> InputBox {
    let id = if id == text {
        format!("{id}~")
    } else {
        id.to_owned()
    };
    InputBox {
        icon: false,
        id,
        role: BoxRole::Node,
        shape: shape.to_owned(),
        parent: String::new(),
        exclusive: true,
        text: text.to_owned(),
        direction: String::new(),
    }
}

fn period_shape(section: Option<usize>) -> String {
    match section {
        Some(index) => format!("{SHAPE_PERIOD}:{index}"),
        None => SHAPE_PERIOD.to_owned(),
    }
}

fn shape_kind(shape: &str) -> &str {
    match shape.split_once(':').map_or(shape, |(kind, _)| kind) {
        "" => SHAPE_PERIOD,
        kind => kind,
    }
}

fn section_of(shape: &str) -> Result<Option<usize>, LayoutError> {
    let Some((_, suffix)) = shape.split_once(':') else {
        return Ok(None);
    };
    suffix
        .parse::<usize>()
        .map(Some)
        .map_err(|_| LayoutError::Domain)
}

struct Meter {
    profile: Profile,
    font_family: bool,
    card_width: i32,
    column_gap: i32,
    card_padding: i32,
}

fn layout_constant(profile: Profile, name: &str) -> Result<i32, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn measured_role(role: TextRole) -> Role {
    match role {
        TextRole::Title => Role::Title,
        TextRole::Body => Role::Body,
        _ => Role::Label,
    }
}

impl Meter {
    fn new(input: &Input) -> Result<Self, LayoutError> {
        let profile = input.profile;
        Ok(Self {
            profile,
            font_family: crate::scene::has_font_family(&input.options.config),
            card_width: layout_constant(profile, "timeline.card_width")?,
            column_gap: layout_constant(profile, "timeline.column_gap")?,
            card_padding: layout_constant(profile, "timeline.card_padding")?,
        })
    }

    fn card_target(&self, slots: i32) -> Result<i32, LayoutError> {
        slots
            .checked_mul(self.card_width)
            .and_then(|width| width.checked_add((slots - 1).checked_mul(self.column_gap)?))
            .and_then(|width| width.checked_sub(2 * self.card_padding))
            .ok_or(LayoutError::Overflow)
    }

    fn text(&self, text: &str, role: TextRole, target: i32) -> Result<Text, LayoutError> {
        let (metric, line_height) = if self.profile == Profile::Cell {
            (Metric::cell(), 1)
        } else {
            let measured = measured_role(role);
            (
                Metric::for_role(measured),
                measured.line_height_px() * UNITS_PER_PX,
            )
        };
        let metric = if self.font_family { metric.with_font_family() } else { metric };
        let lines =
            measure::styled_lines(text, target, metric).map_err(|_| LayoutError::Overflow)?;
        let widest = lines.iter().map(|line| line.width).max().unwrap_or(0);
        let count = i32::try_from(lines.len().max(1)).map_err(|_| LayoutError::Overflow)?;
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
            h: count
                .checked_mul(line_height)
                .ok_or(LayoutError::Overflow)?,
            role,
        })
    }
}

struct Decoder {
    meter: Meter,
    graph: TimelineInput,
    links: BTreeMap<String, String>,
    sections: Vec<String>,
    counts: Vec<usize>,
}

fn decode(input: &Input) -> Result<TimelineInput, LayoutError> {
    let mut decoder = Decoder {
        meter: Meter::new(input)?,
        graph: TimelineInput {
            direction: input.direction,
            title: None,
            sections: Vec::new(),
            periods: Vec::new(),
        },
        links: input
            .routes
            .iter()
            .map(|route| (route.to.clone(), route.id.clone()))
            .collect(),
        sections: Vec::new(),
        counts: Vec::new(),
    };
    for item in &input.boxes {
        decoder.item(item)?;
    }
    decoder.section_labels()?;
    Ok(decoder.graph)
}

impl Decoder {
    fn item(&mut self, item: &InputBox) -> Result<(), LayoutError> {
        match shape_kind(&item.shape) {
            SHAPE_TITLE => {
                let label = self.meter.text(&item.text, TextRole::Title, i32::MAX)?;
                self.graph.title = Some(TimelineTitle {
                    id: item.id.clone(),
                    label,
                });
                Ok(())
            }
            SHAPE_SECTION => {
                self.sections.push(item.text.clone());
                self.counts.push(0);
                self.graph.sections.push(TimelineSection {
                    id: item.id.clone(),
                    label: empty_text(),
                });
                Ok(())
            }
            SHAPE_PERIOD => self.period(item),
            SHAPE_EVENT => self.event(item),
            _ => Err(LayoutError::Domain),
        }
    }

    fn period(&mut self, item: &InputBox) -> Result<(), LayoutError> {
        let section = section_of(&item.shape)?;
        if let Some(index) = section {
            *self.counts.get_mut(index).ok_or(LayoutError::Domain)? += 1;
        }
        let target = self.meter.card_target(1)?;
        let label = self.meter.text(&item.text, TextRole::Label, target)?;
        self.graph.periods.push(TimelinePeriod {
            id: item.id.clone(),
            section,
            label,
            events: Vec::new(),
        });
        Ok(())
    }

    fn event(&mut self, item: &InputBox) -> Result<(), LayoutError> {
        let link = self.links.get(&item.id).ok_or(LayoutError::Domain)?.clone();
        let target = self.meter.card_target(1)?;
        let label = self.meter.text(&item.text, TextRole::Body, target)?;
        let last = self.graph.periods.last_mut().ok_or(LayoutError::Domain)?;
        last.events.push(TimelineEvent {
            id: item.id.clone(),
            link,
            label,
        });
        Ok(())
    }

    fn section_labels(&mut self) -> Result<(), LayoutError> {
        for (s, text) in self.sections.iter().enumerate() {
            let mut slots = 1;
            if self.graph.direction == Direction::Lr {
                slots = i32::try_from(self.counts[s].max(1)).map_err(|_| LayoutError::Overflow)?;
            }
            let target = self.meter.card_target(slots)?;
            self.graph.sections[s].label = self.meter.text(text, TextRole::Label, target)?;
        }
        Ok(())
    }
}

fn empty_text() -> Text {
    Text {
        runs: Vec::new(),
        lines: Vec::new(),
        w: 0,
        h: 0,
        role: TextRole::Label,
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let graph = decode(input)?;
    let result = lanes::timeline(&graph, input.profile)?;
    let dump = dump(input, &result)?;
    Ok((Scene::new(result.canvas, dump, result.groups), false))
}

fn dump(input: &Input, result: &TimelineResult) -> Result<Dump, LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let mut dump = Dump::new(KIND, options);
    let (mut section, mut period, mut event) = (0, None::<usize>, 0);
    for item in &input.boxes {
        let rect: Rect = match shape_kind(&item.shape) {
            SHAPE_TITLE => result.title,
            SHAPE_SECTION => {
                section += 1;
                *result
                    .sections
                    .get(section - 1)
                    .ok_or(LayoutError::Domain)?
            }
            SHAPE_PERIOD => {
                let at = period.map_or(0, |index| index + 1);
                period = Some(at);
                event = 0;
                *result.periods.get(at).ok_or(LayoutError::Domain)?
            }
            _ => {
                event += 1;
                let at = period.ok_or(LayoutError::Domain)?;
                *result
                    .events
                    .get(at)
                    .and_then(|events| events.get(event - 1))
                    .ok_or(LayoutError::Domain)?
            }
        };
        dump.boxes.push(SceneBox {
            id: item.id.clone(),
            role: item.role,
            rect,
            parent: item.parent.clone(),
            exclusive: item.exclusive,
        });
    }
    let drawn: Vec<_> = result.routes.iter().flatten().collect();
    if drawn.len() != input.routes.len() {
        return Err(LayoutError::Domain);
    }
    for (route, points) in input.routes.iter().zip(drawn) {
        dump.routes.push(SceneRoute {
            id: route.id.clone(),
            from: route.from.clone(),
            to: route.to.clone(),
            orthogonal: route.orthogonal,
            points: points.clone(),
            marker_start: route.marker_start.clone(),
            marker_end: route.marker_end.clone(),
            stroke: route.line.clone(),
        });
    }
    Ok(dump)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
