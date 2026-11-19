//! The journey adapter and family entry (`spec/layout/lanes.md`, Journey).
//!
//! [`from_journey`] authors the model-stage dump: one box per title, section band, task,
//! and task actor list, each carrying its unwrapped text. [`layout`] decodes that input
//! again, measures the texts, runs the lanes planner, and fills the dump coordinates.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{COORD_LIMIT, GeomError, Rect};
use crate::measure::{self, Metric, Role};
use crate::model::journey as mj;
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox, TextRole,
};

use super::input::{Box as InputBox, Input, Spacing};
use super::lanes::{
    self, JourneyInput, JourneyResult, JourneySection, JourneyTask, JourneyTitle, Text,
};
use super::layered::LayoutError;

const KIND: &str = "journey";
const TITLE_ID: &str = "title";
const SHAPE_TITLE: &str = "title";
const SHAPE_SECTION: &str = "section";
const SHAPE_TASK: &str = "task";
const SHAPE_PEOPLE: &str = "people";
const WIDTH_KEY: &str = "width";
const HEIGHT_KEY: &str = "height";
const MARGIN_KEY: &str = "diagramMarginX";
const UNITS_PER_PX: i64 = 64;

pub(crate) fn from_journey(
    model: &mj::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config = config(&model.config);
    options.profile = profile;
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
    if !model.title_label.is_empty() {
        input
            .boxes
            .push(card(TITLE_ID, SHAPE_TITLE.to_owned(), &model.title_label));
    }
    let (bands, firsts) = bands(&model.tasks);
    for (b, task) in firsts.iter().enumerate() {
        input.boxes.push(InputBox {
            role: BoxRole::Group,
            exclusive: false,
            ..card(
                &section_id(b),
                SHAPE_SECTION.to_owned(),
                &model.tasks[*task].section_label,
            )
        });
    }
    for (i, task) in model.tasks.iter().enumerate() {
        let id = format!("t{i}");
        input.boxes.push(InputBox {
            parent: bands[i].map(section_id).unwrap_or_default(),
            ..card(&id, format!("{SHAPE_TASK}:{}", task.score), &task.label)
        });
        let people = people(&task.people);
        if !people.is_empty() {
            input.boxes.push(InputBox {
                parent: id.clone(),
                exclusive: false,
                ..card(&format!("{id}.people"), SHAPE_PEOPLE.to_owned(), &people)
            });
        }
    }
    Ok(input)
}

fn card(id: &str, shape: String, text: &str) -> InputBox {
    InputBox {
        icon: false,
        id: id.to_owned(),
        role: BoxRole::Node,
        shape,
        parent: String::new(),
        exclusive: true,
        text: text.to_owned(),
        direction: String::new(),
    }
}

fn section_id(band: usize) -> String {
    format!("s{band}")
}

fn config(config: &mj::Config) -> BTreeMap<String, DumpValue> {
    [
        (MARGIN_KEY, config.margin_x),
        (HEIGHT_KEY, config.height),
        (WIDTH_KEY, config.width),
    ]
    .into_iter()
    .filter_map(|(key, value)| Some((key.to_owned(), DumpValue::Integer(value?))))
    .collect()
}

fn people(names: &[String]) -> String {
    let shown: Vec<&str> = names
        .iter()
        .map(String::as_str)
        .filter(|name| !name.is_empty())
        .collect();
    shown.join(", ")
}

fn bands(tasks: &[mj::Task]) -> (Vec<Option<usize>>, Vec<usize>) {
    let mut of = Vec::with_capacity(tasks.len());
    let mut firsts: Vec<usize> = Vec::new();
    let mut previous = "";
    for (i, task) in tasks.iter().enumerate() {
        if task.section != previous {
            previous = &task.section;
            if !task.section.is_empty() {
                firsts.push(i);
            }
        }
        let band = (!task.section.is_empty()).then(|| firsts.len().saturating_sub(1));
        of.push(band);
    }
    (of, firsts)
}

fn shape_kind(shape: &str) -> &str {
    match shape.split_once(':').map_or(shape, |(kind, _)| kind) {
        "" => SHAPE_TASK,
        kind => kind,
    }
}

fn task_score(shape: &str, lowest: i64) -> Result<i64, LayoutError> {
    if shape.is_empty() {
        return Ok(lowest);
    }
    shape
        .split_once(':')
        .and_then(|(_, suffix)| suffix.parse().ok())
        .ok_or(LayoutError::Domain)
}

fn layout_constant(profile: Profile, name: &str) -> Result<i64, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| i64::from(row.value))
        .ok_or(LayoutError::Domain)
}

fn measured_role(role: TextRole) -> Role {
    match role {
        TextRole::Title => Role::Title,
        TextRole::Body => Role::Body,
        TextRole::Label => Role::Label,
    }
}

struct Meter {
    profile: Profile,
    task_width: i64,
    column_gap: i64,
    padding: i64,
    score_min: i64,
}

impl Meter {
    fn new(input: &Input, graph: &mut JourneyInput) -> Result<Self, LayoutError> {
        let profile = input.profile;
        let mut meter = Self {
            profile,
            task_width: layout_constant(profile, "journey.task_width")?,
            column_gap: layout_constant(profile, "journey.column_gap")?,
            padding: layout_constant(profile, "node_pad_x")?
                + layout_constant(profile, "node_border")?,
            score_min: layout_constant(profile, "journey.score_min")?,
        };
        if profile == Profile::Vector {
            meter.apply_config(&input.options.config, graph)?;
        }
        Ok(meter)
    }

    fn apply_config(
        &mut self,
        config: &BTreeMap<String, DumpValue>,
        graph: &mut JourneyInput,
    ) -> Result<(), LayoutError> {
        for (key, value) in config {
            let DumpValue::Integer(px) = value else {
                continue;
            };
            let units = px.checked_mul(UNITS_PER_PX).ok_or(LayoutError::Overflow)?;
            if *px < 0 || units > COORD_LIMIT {
                return Err(LayoutError::Overflow);
            }
            match key.as_str() {
                WIDTH_KEY => graph.task_width = units,
                HEIGHT_KEY => {
                    graph.task_height = units;
                    graph.band_height = units;
                }
                MARGIN_KEY => graph.column_gap = units,
                _ => {}
            }
        }
        if graph.task_width > 0 {
            self.task_width = graph.task_width;
        }
        if graph.column_gap > 0 {
            self.column_gap = graph.column_gap;
        }
        Ok(())
    }

    fn target(&self, slots: usize) -> Result<i32, LayoutError> {
        let n = i64::try_from(slots.max(1)).map_err(|_| LayoutError::Overflow)?;
        let width = n * self.task_width + (n - 1) * self.column_gap - 2 * self.padding;
        i32::try_from(width.max(1)).map_err(|_| LayoutError::Overflow)
    }

    fn text(&self, text: &str, role: TextRole, target: i32) -> Result<Text, LayoutError> {
        let (metric, line_height) = if self.profile == Profile::Cell {
            (Metric::cell(), 1)
        } else {
            let measured = measured_role(role);
            (Metric::for_role(measured), measured.line_height_px() * 64)
        };
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
    graph: JourneyInput,
    band_at: BTreeMap<String, usize>,
    sections: Vec<String>,
    counts: Vec<usize>,
}

fn decode(input: &Input) -> Result<JourneyInput, LayoutError> {
    let mut graph = JourneyInput::default();
    let meter = Meter::new(input, &mut graph)?;
    let mut decoder = Decoder {
        meter,
        graph,
        band_at: BTreeMap::new(),
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
                self.graph.title = Some(JourneyTitle {
                    id: item.id.clone(),
                    label,
                });
                Ok(())
            }
            SHAPE_SECTION => {
                self.band_at.insert(item.id.clone(), self.sections.len());
                self.sections.push(item.text.clone());
                self.counts.push(0);
                self.graph.sections.push(JourneySection {
                    id: item.id.clone(),
                    label: empty_text(),
                });
                Ok(())
            }
            SHAPE_TASK => self.task(item),
            SHAPE_PEOPLE => self.people(item),
            _ => Err(LayoutError::Domain),
        }
    }

    fn task(&mut self, item: &InputBox) -> Result<(), LayoutError> {
        let score = task_score(&item.shape, self.meter.score_min)?;
        let mut band = None;
        if !item.parent.is_empty() {
            let at = *self.band_at.get(&item.parent).ok_or(LayoutError::Domain)?;
            self.counts[at] += 1;
            band = Some(at);
        }
        let target = self.meter.target(1)?;
        let label = self.meter.text(&item.text, TextRole::Label, target)?;
        self.graph.tasks.push(JourneyTask {
            id: item.id.clone(),
            band,
            score,
            label,
            people: None,
        });
        Ok(())
    }

    fn people(&mut self, item: &InputBox) -> Result<(), LayoutError> {
        let target = self.meter.target(1)?;
        let label = self.meter.text(&item.text, TextRole::Body, target)?;
        let last = self
            .graph
            .tasks
            .last_mut()
            .filter(|task| task.id == item.parent)
            .ok_or(LayoutError::Domain)?;
        last.people = Some(label);
        Ok(())
    }

    fn section_labels(&mut self) -> Result<(), LayoutError> {
        for (s, text) in self.sections.iter().enumerate() {
            let target = self.meter.target(self.counts[s])?;
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
    let result = lanes::journey(&graph, input.profile)?;
    let dump = dump(input, &result)?;
    Ok((Scene::new(result.canvas, dump, result.groups), false))
}

fn dump(input: &Input, result: &JourneyResult) -> Result<Dump, LayoutError> {
    let mut options = input.options.clone();
    options.profile = input.profile;
    options.direction = input.direction;
    let mut dump = Dump::new(KIND, options);
    let (mut section, mut task) = (0, None::<usize>);
    for item in &input.boxes {
        let rect: Rect = match shape_kind(&item.shape) {
            SHAPE_TITLE => result.title,
            SHAPE_SECTION => {
                section += 1;
                *result.frames.get(section - 1).ok_or(LayoutError::Domain)?
            }
            SHAPE_TASK => {
                let at = task.map_or(0, |index| index + 1);
                task = Some(at);
                *result.tasks.get(at).ok_or(LayoutError::Domain)?
            }
            _ => {
                let at = task.ok_or(LayoutError::Domain)?;
                *result.people.get(at).ok_or(LayoutError::Domain)?
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
    Ok(dump)
}
