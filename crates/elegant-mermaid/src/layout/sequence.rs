//! The sequence layout family (`spec/layout/sequence.md`).
//!
//! [`from_sequence`] authors the model-stage dump: actor boxes, participant box frames,
//! fragment frames, note boxes, activation bars, message routes, and label records, with
//! the event stream carried in `region_sets`. [`layout`] widens the lifeline gaps, places
//! the rows, fills the dump coordinates, and draws the scene under both profiles. Every
//! coordinate is an integer in profile units, and every tie breaks on declaration order.

use std::collections::{BTreeMap, BTreeSet};

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{GeomError, Point, Rect, Size};
use crate::measure::{self, Metric, Role, StyledLine};
use crate::model::sequence as ms;
use crate::scene::{
    Align, BoxRole, Dump, DumpOptions, DumpValue, EllipseItem, Group as SceneGroup, GroupRole,
    Item, Line as StyleLine, MarkerAxis, MarkerName, MarkerRefItem, PolylineItem, Profile,
    RectItem, RoundRectItem, Run, Scene, SceneBox, SceneLabel, SceneRoute, Shape, ShapeStyle,
    TextItem, TextRole, TextStyle, Width,
};

use super::input::{
    Box as InputBox, Input, Label as InputLabel, RegionSet, Route as InputRoute, Spacing,
};
use super::layered::LayoutError;

const KIND: &str = "sequence";

const TAG_MESSAGE: usize = 0;
const TAG_NOTE: usize = 1;
const TAG_FRAGMENT_START: usize = 2;
const TAG_FRAGMENT_ELSE: usize = 3;
const TAG_FRAGMENT_END: usize = 4;
const TAG_ACTIVATE_START: usize = 5;
const TAG_ACTIVATE_END: usize = 6;
const TAG_MASK: usize = 15;

const FLAG_CREATES: usize = 1 << 10;
const FLAG_DESTROYS: usize = 1 << 11;
const FLAG_CENTRAL_START: usize = 1 << 12;
const FLAG_CENTRAL_END: usize = 1 << 13;
const FLAG_NUMBERED: usize = 64;
const WRAP_ON: usize = 16;
const WRAP_OFF: usize = 32;
const PLACEMENT_SHIFT: u32 = 8;
const NO_DESTROYED: usize = usize::MAX;

const FRAGMENT_KINDS: [&str; 8] = [
    "loop", "rect", "opt", "alt", "par", "par_over", "critical", "break",
];

const RULE_RADIUS_UNITS: i32 = 512;

pub(crate) fn from_sequence(
    model: &ms::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config = model
        .config
        .iter()
        .map(|(key, value)| (key.clone(), scene_value(value)))
        .collect();
    options.profile = profile;
    let mut author = Author {
        model,
        input: Input {
            kind: KIND,
            profile,
            direction: crate::scene::Direction::Tb,
            options,
            boxes: Vec::new(),
            routes: Vec::new(),
            labels: Vec::new(),
            groups: Vec::new(),
            sizes: Vec::new(),
            attachments: Vec::new(),
            region_sets: Vec::new(),
            spacing: Spacing::default(),
        },
        used: BTreeSet::new(),
        actor_ids: Vec::new(),
        actor_boxes: Vec::new(),
        slots: Vec::new(),
        box_ids: Vec::new(),
        fragment_boxes: Vec::new(),
        fragments_started: 0,
        section_titles: BTreeMap::new(),
    };
    author.participant_boxes();
    author.actors();
    author.events();
    author.labels();
    Ok(author.input)
}

fn scene_value(value: &ms::DumpValue) -> DumpValue {
    match value {
        ms::DumpValue::Bool(flag) => DumpValue::Bool(*flag),
        ms::DumpValue::Integer(number) => DumpValue::Integer(*number),
        ms::DumpValue::String(text) => DumpValue::String(text.clone()),
    }
}

fn wrap_token(wrap: Option<bool>) -> String {
    match wrap {
        Some(true) => String::from("w"),
        Some(false) => String::from("n"),
        None => String::new(),
    }
}

fn wrap_bits(wrap: Option<bool>) -> usize {
    match wrap {
        Some(true) => WRAP_ON,
        Some(false) => WRAP_OFF,
        None => 0,
    }
}

fn wrap_of(bits: usize) -> Option<bool> {
    if bits & WRAP_ON != 0 {
        return Some(true);
    }
    if bits & WRAP_OFF != 0 {
        return Some(false);
    }
    None
}

fn kind_code(kind: &str) -> usize {
    FRAGMENT_KINDS
        .iter()
        .position(|candidate| *candidate == kind)
        .unwrap_or(0)
}

fn is_fragment(shape: &str) -> bool {
    FRAGMENT_KINDS.contains(&shape)
}

struct Author<'m> {
    model: &'m ms::Model,
    input: Input,
    used: BTreeSet<String>,
    actor_ids: Vec<String>,
    actor_boxes: Vec<usize>,
    slots: Vec<usize>,
    box_ids: Vec<String>,
    fragment_boxes: Vec<usize>,
    fragments_started: usize,
    section_titles: BTreeMap<usize, Vec<String>>,
}
impl<'m> Author<'m> {
    fn unique(&mut self, wanted: String) -> String {
        let mut candidate = wanted.clone();
        let mut ordinal = 0;
        while self.used.contains(&candidate) {
            ordinal += 1;
            candidate = format!("{wanted}~{ordinal}");
        }
        self.used.insert(candidate.clone());
        candidate
    }

    fn anchored_box(&self, actor: &ms::Actor) -> Option<usize> {
        actor
            .created_at
            .is_none()
            .then_some(actor.box_index)
            .flatten()
            .filter(|index| *index < self.model.boxes.len())
    }

    fn participant_boxes(&mut self) {
        let mut members = vec![false; self.model.boxes.len()];
        for actor in &self.model.actors {
            if let Some(index) = self.anchored_box(actor) {
                members[index] = true;
            }
        }
        for (index, box_) in self.model.boxes.iter().enumerate() {
            if !members[index] {
                self.box_ids.push(String::new());
                continue;
            }
            let id = self.unique(format!("box{index}"));
            self.box_ids.push(id.clone());
            self.input.boxes.push(InputBox {
                icon: false,
                id,
                role: BoxRole::Group,
                shape: String::new(),
                parent: String::new(),
                exclusive: false,
                text: box_.label.clone(),
                direction: wrap_token(box_.wrap),
            });
        }
    }

    fn lifeline_order(&self) -> Vec<usize> {
        let mut order: Vec<usize> = Vec::with_capacity(self.model.actors.len());
        for (index, actor) in self.model.actors.iter().enumerate() {
            let mut at = order.len();
            if let Some(box_) = self.anchored_box(actor)
                && let Some(position) = order
                    .iter()
                    .rposition(|other| self.anchored_box(&self.model.actors[*other]) == Some(box_))
            {
                at = position + 1;
            }
            order.insert(at, index);
        }
        order
    }

    fn actors(&mut self) {
        let count = self.model.actors.len();
        self.actor_ids = vec![String::new(); count];
        self.actor_boxes = vec![0; count];
        self.slots = vec![0; count];
        for (slot, index) in self.lifeline_order().into_iter().enumerate() {
            let actor = &self.model.actors[index];
            let parent = self
                .anchored_box(actor)
                .and_then(|box_| self.box_ids.get(box_).cloned())
                .unwrap_or_default();
            let id = self.unique(actor.id.clone());
            self.actor_ids[index].clone_from(&id);
            self.actor_boxes[index] = self.input.boxes.len();
            self.slots[index] = slot;
            let shape = if actor.kind == "participant" {
                String::new()
            } else {
                actor.kind.to_string()
            };
            self.input.boxes.push(InputBox {
                icon: false,
                id,
                role: BoxRole::Node,
                shape,
                parent,
                exclusive: actor.created_at.is_none(),
                text: actor.label.clone(),
                direction: wrap_token(actor.wrap),
            });
        }
    }

    fn fragment_parent(&self) -> String {
        self.fragment_boxes
            .last()
            .and_then(|index| self.input.boxes.get(*index))
            .map(|box_| box_.id.clone())
            .unwrap_or_default()
    }

    fn push_region(&mut self, regions: Vec<usize>) {
        self.input.region_sets.push(RegionSet {
            parent: self.input.region_sets.len(),
            regions,
        });
    }

    fn events(&mut self) {
        let events = self.model.events.clone();
        for (event_index, event) in events.iter().enumerate() {
            match event {
                ms::Event::FragmentStart(start) => self.fragment_start(start),
                ms::Event::FragmentElse(else_) => self.fragment_else(else_),
                ms::Event::FragmentEnd { .. } => self.fragment_end(),
                ms::Event::Note(note) => self.note(note),
                ms::Event::ActivateStart { actor } => {
                    self.push_region(vec![TAG_ACTIVATE_START, self.slots[*actor]]);
                }
                ms::Event::ActivateEnd { actor } => {
                    self.push_region(vec![TAG_ACTIVATE_END, self.slots[*actor]]);
                }
                ms::Event::Message(message) => self.message(event_index, message),
            }
        }
    }

    fn fragment_start(&mut self, start: &ms::FragmentStart) {
        let parent = self.fragment_parent();
        let ordinal = self.fragments_started;
        self.fragments_started += 1;
        let id = self.unique(format!("f{ordinal}"));
        let index = self.input.boxes.len();
        self.input.boxes.push(InputBox {
            icon: false,
            id,
            role: BoxRole::Group,
            shape: start.kind.to_string(),
            parent,
            exclusive: false,
            text: start.title.clone(),
            direction: wrap_token(start.wrap),
        });
        self.fragment_boxes.push(index);
        let tag = TAG_FRAGMENT_START | (kind_code(start.kind) << 6) | wrap_bits(start.wrap);
        self.push_region(vec![tag, index]);
    }

    fn fragment_else(&mut self, else_: &ms::FragmentElse) {
        let box_index = self.fragment_boxes.last().copied().unwrap_or(0);
        let section = self.section_titles.entry(box_index).or_default().len();
        self.section_titles
            .entry(box_index)
            .or_default()
            .push(else_.title.clone());
        let tag = TAG_FRAGMENT_ELSE | wrap_bits(else_.wrap);
        self.push_region(vec![tag, box_index, section]);
    }

    fn fragment_end(&mut self) {
        let box_index = self.fragment_boxes.last().copied().unwrap_or(0);
        self.push_region(vec![TAG_FRAGMENT_END, box_index]);
        self.fragment_boxes.pop();
    }

    fn note(&mut self, note: &ms::Note) {
        let parent = self.fragment_parent();
        let ordinal = self.count_shape("note");
        let id = self.unique(format!("note{ordinal}"));
        let index = self.input.boxes.len();
        let [a, b] = note.actors.map(|actor| self.slots[actor]);
        let placement = match note.placement {
            ms::Placement::LeftOf => 0,
            ms::Placement::RightOf => 1,
            ms::Placement::Over => 2,
        };
        self.input.boxes.push(InputBox {
            icon: false,
            id,
            role: BoxRole::Node,
            shape: String::from("note"),
            parent,
            exclusive: false,
            text: note.text.clone(),
            direction: wrap_token(note.wrap),
        });
        let tag = TAG_NOTE | ((placement as usize) << PLACEMENT_SHIFT) | wrap_bits(note.wrap);
        self.push_region(vec![tag, a, b, index]);
    }

    fn count_shape(&self, shape: &str) -> usize {
        self.input
            .boxes
            .iter()
            .filter(|box_| box_.shape == shape)
            .count()
    }

    fn message(&mut self, event_index: usize, message: &ms::Message) {
        let from = self.actor_ids[message.from].clone();
        let to = self.actor_ids[message.to].clone();
        let mut ordinal = self.input.routes.len();
        let mut id = format!("e{ordinal}");
        while self.used.contains(&id) {
            ordinal += 1;
            id = format!("e{ordinal}");
        }
        self.used.insert(id.clone());
        let flags = (usize::from(message.creates) * FLAG_CREATES)
            | (usize::from(message.destroys) * FLAG_DESTROYS)
            | (usize::from(message.central_start) * FLAG_CENTRAL_START)
            | (usize::from(message.central_end) * FLAG_CENTRAL_END)
            | (usize::from(message.numbered) * FLAG_NUMBERED)
            | wrap_bits(message.wrap);
        let route_index = self.input.routes.len();
        let destroyed = if message.destroys {
            self.model
                .actors
                .iter()
                .position(|actor| actor.destroyed_at == Some(event_index))
                .map_or(NO_DESTROYED, |actor| self.slots[actor])
        } else {
            NO_DESTROYED
        };
        let frame = self.fragment_parent();
        if message.creates
            && let Some(box_) = self.input.boxes.get_mut(self.actor_boxes[message.to])
        {
            box_.parent.clone_from(&frame);
        }
        self.input.routes.push(InputRoute {
            id: id.clone(),
            from,
            to,
            orthogonal: true,
            marker_start: message.head_start.to_string(),
            marker_end: message.head_end.to_string(),
            line: if message.dotted {
                String::from("dotted")
            } else {
                String::from("normal")
            },
            min_length: 0,
            from_side: None,
            to_side: None,
        });
        if !message.text.is_empty() {
            self.input.labels.push(InputLabel {
                id: format!("{id}.label"),
                owner: id,
                role: TextRole::Body,
                text: message.text.clone(),
            });
        }
        self.push_region(vec![
            TAG_MESSAGE | flags,
            self.slots[message.from],
            self.slots[message.to],
            route_index,
            destroyed,
        ]);
    }

    fn labels(&mut self) {
        for (index, box_) in self.input.boxes.iter().enumerate() {
            if let Some(label) = box_label(box_) {
                let role = if box_.shape == "note" {
                    TextRole::Body
                } else {
                    TextRole::Label
                };
                let owner = box_.id.clone();
                self.input.labels.push(InputLabel {
                    id: format!("{owner}.label"),
                    owner,
                    role,
                    text: label,
                });
            }
            if let Some(titles) = self
                .section_titles
                .get(&index)
                .cloned()
                .filter(|titles| !titles.is_empty())
            {
                for (position, title) in titles.into_iter().enumerate() {
                    let owner = box_.id.clone();
                    self.input.labels.push(InputLabel {
                        id: format!("{owner}.s{position}"),
                        owner,
                        role: TextRole::Label,
                        text: title,
                    });
                }
            }
        }
    }
}

fn is_actor(box_: &InputBox) -> bool {
    box_.role == BoxRole::Node && box_.shape != "note"
}

fn box_label(box_: &InputBox) -> Option<String> {
    if box_.role == BoxRole::Group {
        return match box_.shape.as_str() {
            "rect" => None,
            kind if is_fragment(kind) => Some(format!("[{}]", box_.text)),
            _ => Some(box_.text.clone()),
        };
    }
    if is_actor(box_) {
        return None;
    }
    Some(box_.text.clone())
}

fn constant(profile: Profile, name: &str) -> Result<i32, LayoutError> {
    lookup(&format!(
        "{profile}.sequence.{name}",
        profile = profile.as_str()
    ))
}

fn corner_radius(profile: Profile) -> Result<i32, LayoutError> {
    lookup(&format!(
        "{profile}.corner_radius",
        profile = profile.as_str()
    ))
}

fn lookup(key: &str) -> Result<i32, LayoutError> {
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn metric_of(profile: Profile, role: Role) -> Metric {
    if profile == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(role)
    }
}

fn line_height(profile: Profile) -> i32 {
    if profile == Profile::Cell { 1 } else { 1280 }
}

fn wrap_target(shared: bool, override_: Option<bool>, width: i32, padding: i32) -> i32 {
    if !override_.unwrap_or(shared) {
        return i32::MAX;
    }
    (width - 2 * padding).max(1)
}

fn measure(text: &str, target: i32, metric: Metric) -> Result<Vec<StyledLine<'_>>, LayoutError> {
    measure::styled_lines(text, target, metric).map_err(|_| LayoutError::Overflow)
}

fn half(value: i32) -> i32 {
    value.div_euclid(2)
}

fn widen(gaps: &mut [i32], from: usize, to: usize, need: i32) {
    if from >= to || to > gaps.len() {
        return;
    }
    let sum: i32 = gaps[from..to].iter().sum();
    let extra = need - sum;
    if extra <= 0 {
        return;
    }
    let span = i32::try_from(to - from).unwrap_or(0);
    if span <= 0 {
        return;
    }
    let share = extra.div_euclid(span);
    let mut remainder = extra - share * span;
    for gap in &mut gaps[from..to] {
        *gap += share;
        if remainder > 0 {
            *gap += 1;
            remainder -= 1;
        }
    }
}

fn centres(widths: &[i32], gaps: &[i32]) -> Vec<i32> {
    let mut centre = widths.first().map_or(0, |width| half(*width));
    let mut steps = gaps.iter();
    widths
        .iter()
        .map(|_| {
            let here = centre;
            centre += steps.next().copied().unwrap_or(0);
            here
        })
        .collect()
}

fn runs_of(lines: &[StyledLine<'_>]) -> Vec<Vec<Run>> {
    lines
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
        .collect()
}

#[derive(Debug, Clone, Copy)]
enum Step {
    Message {
        from: usize,
        to: usize,
        flags: usize,
        route: usize,
        destroyed: usize,
    },
    Note {
        placement: usize,
        a: usize,
        b: usize,
        box_index: usize,
    },
    FragmentStart {
        kind: usize,
        box_index: usize,
    },
    FragmentElse {
        box_index: usize,
        section: usize,
    },
    FragmentEnd,
    ActivateStart {
        actor: usize,
    },
    ActivateEnd {
        actor: usize,
    },
}

fn decode_steps(input: &Input) -> Vec<Step> {
    let mut steps: Vec<(usize, Step)> = Vec::with_capacity(input.region_sets.len());
    for region in &input.region_sets {
        let tag = region.regions.first().copied().unwrap_or(0);
        let value = |at: usize| region.regions.get(at).copied().unwrap_or(0);
        let bits = tag & !TAG_MASK;
        let step = match tag & TAG_MASK {
            TAG_MESSAGE => Step::Message {
                from: value(1),
                to: value(2),
                flags: bits,
                route: value(3),
                destroyed: value(4),
            },
            TAG_NOTE => Step::Note {
                placement: (bits >> PLACEMENT_SHIFT) & 3,
                a: value(1),
                b: value(2),
                box_index: value(3),
            },
            TAG_FRAGMENT_START => Step::FragmentStart {
                kind: (bits >> 6) & 15,
                box_index: value(1),
            },
            TAG_FRAGMENT_ELSE => Step::FragmentElse {
                box_index: value(1),
                section: value(2),
            },
            TAG_FRAGMENT_END => Step::FragmentEnd,
            TAG_ACTIVATE_START => Step::ActivateStart { actor: value(1) },
            _ => Step::ActivateEnd { actor: value(1) },
        };
        steps.push((region.parent, step));
    }
    steps.sort_by_key(|(parent, _)| *parent);
    steps.into_iter().map(|(_, step)| step).collect()
}

struct Planner<'a> {
    input: &'a Input,
    profile: Profile,
    shared_wrap: bool,
    actor_boxes: Vec<usize>,
    widths: Vec<i32>,
    heights: Vec<i32>,
    centres: Vec<i32>,
    gaps: Vec<i32>,
    actor_lines: Vec<Vec<StyledLine<'a>>>,
    label_lines: Vec<Vec<StyledLine<'a>>>,
    corner: i32,
    band_top: i32,
    band_height: i32,
    shift_x: i32,
    shift_y: i32,
    bottom: i32,
    destroyed_ys: Vec<Option<i32>>,
    route_runs: Vec<RouteRun>,
    closed_frames: Vec<ClosedFrame>,
    bars: Vec<Rect>,
    dump: Dump,
}

impl<'a> Planner<'a> {
    fn new(input: &'a Input) -> Result<Self, LayoutError> {
        let profile = input.profile;
        let shared_wrap = matches!(
            input.options.config.get("wrap"),
            Some(DumpValue::Bool(true))
        );
        let width = constant(profile, "actor_width")?;
        let padding = constant(profile, "wrap_padding")?;
        let mut actor_boxes = Vec::new();
        let mut actor_lines = Vec::new();
        let mut actor_wraps = Vec::new();
        for (index, box_) in input.boxes.iter().enumerate() {
            if !is_actor(box_) {
                continue;
            }
            actor_boxes.push(index);
            actor_wraps.push(box_wrap(box_));
            let target = wrap_target(shared_wrap, box_wrap(box_), width, padding);
            let lines = measure(&box_.text, target, metric_of(profile, Role::Label))?;
            actor_lines.push(lines);
        }
        let mut label_lines = Vec::with_capacity(input.labels.len());
        for label in &input.labels {
            let wrap = if route_owned(input, &label.owner) {
                message_wrap(input, &label.owner)
            } else {
                input
                    .boxes
                    .iter()
                    .find(|box_| box_.id == label.owner)
                    .and_then(box_wrap)
            };
            let role = if label.role == TextRole::Body {
                Role::Body
            } else {
                Role::Label
            };
            let target = wrap_target(shared_wrap, wrap, width, padding);
            label_lines.push(measure(&label.text, target, metric_of(profile, role))?);
        }
        let mut planner = Planner {
            input,
            profile,
            shared_wrap,
            actor_boxes,
            widths: Vec::new(),
            heights: Vec::new(),
            centres: Vec::new(),
            gaps: Vec::new(),
            actor_lines,
            label_lines,
            corner: corner_radius(profile)?,
            band_top: 0,
            band_height: 0,
            shift_x: 0,
            shift_y: 0,
            bottom: 0,
            destroyed_ys: Vec::new(),
            route_runs: Vec::new(),
            closed_frames: Vec::new(),
            bars: Vec::new(),
            dump: blank_dump(input),
        };
        planner.actor_sizes()?;
        Ok(planner)
    }

    fn actor_sizes(&mut self) -> Result<(), LayoutError> {
        let width = constant(self.profile, "actor_width")?;
        let height = constant(self.profile, "actor_height")?;
        let margin = constant(self.profile, "actor_margin")?;
        let lh = line_height(self.profile);
        for (ordinal, index) in self.actor_boxes.iter().enumerate() {
            let wrapped = actor_wrap_at(self.input, *index).unwrap_or(self.shared_wrap);
            let text_w = self.actor_lines[ordinal]
                .iter()
                .map(|line| line.width)
                .max()
                .unwrap_or(0);
            let text_h = self.actor_lines[ordinal].len() as i32 * lh;
            self.widths.push(if wrapped {
                width
            } else {
                width.max(text_w + 2 * constant(self.profile, "wrap_padding")?)
            });
            self.heights
                .push(height.max(text_h + 2 * constant(self.profile, "box_text_margin")?));
        }
        if self.widths.len() >= 2 {
            for pair in self.widths.windows(2) {
                self.gaps.push(half(pair[0] + pair[1]) + margin);
            }
        }
        self.centres = centres(&self.widths, &self.gaps);
        let mut band_top = 0;
        let mut band_height = 0;
        for (index, box_) in self.input.boxes.iter().enumerate() {
            if box_.role == BoxRole::Group && box_.shape.is_empty() {
                let lines = self.title_lines(index);
                let header = lines.len() as i32 * lh + constant(self.profile, "box_margin")?;
                band_top = band_top.max(header);
            }
            if is_actor(box_) {
                let ordinal = self.actor_boxes.iter().position(|at| *at == index);
                if let Some(ordinal) = ordinal {
                    band_height = band_height.max(self.heights[ordinal]);
                }
            }
        }
        self.band_top = band_top;
        self.band_height = band_height;
        Ok(())
    }

    fn title_lines(&self, box_index: usize) -> &[StyledLine<'a>] {
        let Some(box_) = self.input.boxes.get(box_index) else {
            return &[];
        };
        let Some(position) = self
            .input
            .labels
            .iter()
            .position(|label| label.owner == box_.id && label.id.ends_with(".label"))
        else {
            return &[];
        };
        self.label_lines.get(position).map_or(&[], |lines| lines)
    }

    fn widen_gaps(&mut self) -> Result<(), LayoutError> {
        let padding = constant(self.profile, "wrap_padding")?;
        let margin = constant(self.profile, "actor_margin")?;
        let note_pad = constant(self.profile, "note_margin")?;
        let steps = decode_steps(self.input);
        for step in &steps {
            match *step {
                Step::Message {
                    from,
                    to,
                    flags,
                    route,
                    ..
                } => {
                    let width = self
                        .label_position_of_route(route)
                        .and_then(|position| self.label_lines.get(position))
                        .map_or(0, |lines| {
                            lines.iter().map(|line| line.width).max().unwrap_or(0)
                        });
                    let need = width + 2 * padding;
                    if from == to {
                        let dx =
                            half(need).max(constant(self.profile, "self_loop_min_dx")?) + margin;
                        if from < self.gaps.len() {
                            widen(&mut self.gaps, from, from + 1, dx);
                        }
                    } else {
                        let (low, high) = if from < to { (from, to) } else { (to, from) };
                        widen(&mut self.gaps, low, high, need + margin);
                    }
                    if flags & FLAG_CREATES != 0 && to > 0 {
                        let width_half = half(self.widths.get(to).copied().unwrap_or(0));
                        self.gaps[to - 1] += width_half;
                    }
                }
                Step::Note {
                    placement,
                    a,
                    b,
                    box_index,
                    ..
                } => {
                    let text_w = self.box_label_width(box_index);
                    match placement {
                        2 if a == b => {
                            let w = self.widths.get(a).copied().unwrap_or(0);
                            let width = w.max(text_w + 2 * note_pad);
                            let need = half(width) + margin;
                            if a > 0 {
                                widen(&mut self.gaps, a - 1, a, need);
                            }
                            if a < self.gaps.len() {
                                widen(&mut self.gaps, a, a + 1, need);
                            }
                        }
                        2 => {
                            let (low, high) = if a < b { (a, b) } else { (b, a) };
                            widen(&mut self.gaps, low, high, text_w + 2 * note_pad + margin);
                        }
                        1 => {
                            let w = self.widths.get(a).copied().unwrap_or(0);
                            let width = w.max(text_w + 2 * note_pad);
                            let need = half(w) + 2 * half(margin) + width;
                            if a < self.gaps.len() {
                                widen(&mut self.gaps, a, a + 1, need);
                            }
                        }
                        _ => {
                            let w = self.widths.get(a).copied().unwrap_or(0);
                            let width = w.max(text_w + 2 * note_pad);
                            let need = half(w) + 2 * half(margin) + width;
                            if a > 0 {
                                widen(&mut self.gaps, a - 1, a, need);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        self.centres = centres(&self.widths, &self.gaps);
        self.clear_participant_boxes()?;
        self.centres = centres(&self.widths, &self.gaps);
        Ok(())
    }

    /// Extra width of each participant box title beyond its members, with the first and
    /// last member ordinal of the box.
    fn participant_frames(&self) -> Result<Vec<(usize, usize, i32)>, LayoutError> {
        let btm = constant(self.profile, "box_text_margin")?;
        let padding = constant(self.profile, "wrap_padding")?;
        let mut frames = Vec::new();
        for (index, box_) in self.input.boxes.iter().enumerate() {
            if !(box_.role == BoxRole::Group && box_.shape.is_empty()) {
                continue;
            }
            let members: Vec<usize> = self
                .actor_boxes
                .iter()
                .enumerate()
                .filter(|(_, at)| self.input.boxes[**at].parent == box_.id)
                .map(|(ordinal, _)| ordinal)
                .collect();
            let (Some(first), Some(last)) = (members.first(), members.last()) else {
                continue;
            };
            let left = self.centres[*first] - half(self.widths[*first]);
            let right = self.centres[*last] + self.widths[*last] - half(self.widths[*last]);
            let title_w = self
                .title_lines(index)
                .iter()
                .map(|line| line.width)
                .max()
                .unwrap_or(0);
            let extra = (title_w + 2 * padding - ((right - left) + 2 * btm)).max(0);
            frames.push((*first, *last, extra));
        }
        Ok(frames)
    }

    fn clear_participant_boxes(&mut self) -> Result<(), LayoutError> {
        let btm = constant(self.profile, "box_text_margin")?;
        let frames = self.participant_frames()?;
        let reach_right = |ordinal: usize| {
            frames
                .iter()
                .find(|(_, last, _)| *last == ordinal)
                .map_or(0, |(_, _, extra)| btm + (extra - half(*extra)))
        };
        let reach_left = |ordinal: usize| {
            frames
                .iter()
                .find(|(first, _, _)| *first == ordinal)
                .map_or(0, |(_, _, extra)| btm + half(*extra))
        };
        let mut needs = Vec::new();
        for (first, last, _) in &frames {
            if *first > 0 {
                needs.push((*first - 1, reach_right(*first - 1) + reach_left(*first)));
            }
            if *last + 1 < self.widths.len() {
                needs.push((*last, reach_right(*last) + reach_left(*last + 1)));
            }
        }
        for (gap, reach) in needs {
            let need =
                self.widths[gap] - half(self.widths[gap]) + half(self.widths[gap + 1]) + reach;
            widen(&mut self.gaps, gap, gap + 1, need);
        }
        Ok(())
    }

    fn box_label_width(&self, box_index: usize) -> i32 {
        let Some(box_) = self.input.boxes.get(box_index) else {
            return 0;
        };
        self.label_lines
            .iter()
            .zip(self.input.labels.iter())
            .find(|(_, label)| label.owner == box_.id && label.id.ends_with(".label"))
            .map_or(0, |(lines, _)| {
                lines.iter().map(|line| line.width).max().unwrap_or(0)
            })
    }
}

fn box_wrap(box_: &InputBox) -> Option<bool> {
    match box_.direction.as_str() {
        "w" => Some(true),
        "n" => Some(false),
        _ => None,
    }
}

fn actor_wrap_at(input: &Input, box_index: usize) -> Option<bool> {
    input.boxes.get(box_index).and_then(box_wrap)
}

fn route_owned(input: &Input, owner: &str) -> bool {
    input.routes.iter().any(|route| route.id == owner)
}

fn message_wrap(input: &Input, owner: &str) -> Option<bool> {
    input
        .region_sets
        .iter()
        .filter(|region| region.regions.first().copied().unwrap_or(99) & TAG_MASK == TAG_MESSAGE)
        .find(|region| {
            input
                .routes
                .get(region.regions.get(3).copied().unwrap_or(0))
                .is_some_and(|route| route.id == owner)
        })
        .and_then(|region| wrap_of(region.regions.first().copied().unwrap_or(0)))
}

fn blank_dump(input: &Input) -> Dump {
    Dump {
        kind: KIND,
        options: input.options.clone(),
        boxes: input
            .boxes
            .iter()
            .map(|box_| SceneBox {
                id: box_.id.clone(),
                role: box_.role,
                rect: Rect {
                    x: 0,
                    y: 0,
                    w: 0,
                    h: 0,
                },
                parent: box_.parent.clone(),
                exclusive: box_.exclusive,
            })
            .collect(),
        routes: input
            .routes
            .iter()
            .map(|route| SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: route.orthogonal,
                points: Vec::new(),
                marker_start: route.marker_start.clone(),
                marker_end: route.marker_end.clone(),
                stroke: route.line.clone(),
            })
            .collect(),
        labels: input
            .labels
            .iter()
            .map(|label| SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect: Rect {
                    x: 0,
                    y: 0,
                    w: 0,
                    h: 0,
                },
                lines: Vec::new(),
            })
            .collect(),
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let mut planner = Planner::new(input)?;
    planner.widen_gaps()?;
    let walk = walk_rows(&planner)?;
    let canvas = planner.fill(&walk)?;
    planner.bottom = walk.bottom;
    planner.destroyed_ys = walk.destroyed_y.clone();
    planner.route_runs = walk.route_runs.clone();
    planner.closed_frames = walk.closed_frames.clone();
    planner.bars = walk.bars.clone();
    let items = planner.assemble();
    Ok((Scene::new(canvas, planner.dump, items), false))
}

/// The row of each `else` divider of a fragment and the position of its section label.
type Dividers = Vec<(i32, Option<usize>)>;

/// A closed fragment: its frame box index and its dividers.
type ClosedFrame = (usize, Dividers);

struct FragmentRun {
    box_index: usize,
    kind: usize,
    top: i32,
    members: Vec<Rect>,
    dividers: Dividers,
}

struct BarRun {
    actor: usize,
    top: i32,
    x: i32,
    depth: i32,
}

#[derive(Clone)]
struct RouteRun {
    points: Vec<Point>,
    start_marker: Option<(Point, MarkerName, MarkerAxis)>,
    end_marker: Option<(Point, MarkerName, MarkerAxis)>,
    central: Vec<(Point, bool)>,
    badge: Option<Point>,
}

struct Walk {
    cursor: i32,
    box_rects: Vec<Rect>,
    label_rects: Vec<Rect>,
    route_runs: Vec<RouteRun>,
    fragments: Vec<FragmentRun>,
    closed_frames: Vec<ClosedFrame>,
    open_bars: Vec<BarRun>,
    bars: Vec<Rect>,
    bar_depths: Vec<i32>,
    destroyed_y: Vec<Option<i32>>,
    bottom: i32,
}

fn walk_rows(planner: &Planner<'_>) -> Result<Walk, LayoutError> {
    let actors = planner.widths.len();
    let mut walk = Walk {
        cursor: 0,
        box_rects: vec![zero_rect(); planner.input.boxes.len()],
        label_rects: vec![zero_rect(); planner.input.labels.len()],
        route_runs: Vec::new(),
        fragments: Vec::new(),
        closed_frames: Vec::new(),
        open_bars: Vec::new(),
        bars: Vec::new(),
        bar_depths: vec![0; actors],
        destroyed_y: vec![None; actors],
        bottom: 0,
    };
    walk.place_headers(planner)?;
    walk.cursor =
        planner.band_top + planner.band_height + 2 * constant(planner.profile, "box_margin")?;
    walk.bottom = walk.cursor;
    let steps = decode_steps(planner.input);
    for step in &steps {
        walk.step(planner, step)?;
    }
    while let Some(run) = walk.fragments.pop() {
        walk.close_fragment(planner, run)?;
    }
    let bar_width = constant(planner.profile, "activation_width")?;
    while let Some(bar) = walk.open_bars.pop() {
        walk.bars.push(Rect {
            x: bar.x,
            y: bar.top,
            w: bar_width,
            h: (walk.cursor - bar.top).max(0),
        });
    }
    walk.bottom = walk.cursor;
    Ok(walk)
}

impl Walk {
    fn place_headers(&mut self, planner: &Planner<'_>) -> Result<(), LayoutError> {
        let btm = constant(planner.profile, "box_text_margin")?;
        let padding = constant(planner.profile, "wrap_padding")?;
        let bm = constant(planner.profile, "box_margin")?;
        let lh = line_height(planner.profile);
        for (ordinal, index) in planner.actor_boxes.iter().enumerate() {
            let centre = planner.centres.get(ordinal).copied().unwrap_or(0);
            let width = planner.widths[ordinal];
            let height = planner.heights[ordinal];
            self.box_rects[*index] = Rect {
                x: centre - half(width),
                y: planner.band_top,
                w: width,
                h: height,
            };
        }
        for (index, box_) in planner.input.boxes.iter().enumerate() {
            if !(box_.role == BoxRole::Group && box_.shape.is_empty()) {
                continue;
            }
            let members: Vec<usize> = planner
                .input
                .boxes
                .iter()
                .enumerate()
                .filter(|(_, candidate)| candidate.parent == box_.id)
                .map(|(candidate, _)| candidate)
                .collect();
            let left = members
                .iter()
                .filter_map(|at| self.box_rects.get(*at))
                .map(|rect| rect.x)
                .min()
                .unwrap_or(0);
            let right = members
                .iter()
                .filter_map(|at| self.box_rects.get(*at))
                .map(|rect| rect.x + rect.w)
                .max()
                .unwrap_or(0);
            let lines = planner.title_lines(index);
            let title_w = lines.iter().map(|line| line.width).max().unwrap_or(0);
            let inner = (right - left) + 2 * btm;
            let extra = (title_w + 2 * padding - inner).max(0);
            let header = lines.len() as i32 * lh + bm;
            let rect = Rect {
                x: left - btm - half(extra),
                y: planner.band_top - header,
                w: inner + extra,
                h: header + planner.band_height + bm,
            };
            self.box_rects[index] = rect;
            let title = planner.label_by_id(&format!("{}.label", box_.id));
            self.centre_label(planner, title, rect, rect.y + btm);
        }
        Ok(())
    }

    fn constant(&self, planner: &Planner<'_>, name: &str) -> Result<i32, LayoutError> {
        constant(planner.profile, name)
    }

    fn lh(planner: &Planner<'_>) -> i32 {
        line_height(planner.profile)
    }

    fn actor_centre(planner: &Planner<'_>, actor: usize) -> i32 {
        planner.centres.get(actor).copied().unwrap_or(0)
    }

    fn actor_box(planner: &Planner<'_>, actor: usize) -> Option<usize> {
        planner.actor_boxes.get(actor).copied()
    }

    fn step(&mut self, planner: &Planner<'_>, step: &Step) -> Result<(), LayoutError> {
        match *step {
            Step::Message {
                from,
                to,
                flags,
                route,
                destroyed,
            } => self.message(planner, from, to, flags, route, destroyed),
            Step::Note {
                placement,
                a,
                b,
                box_index,
                ..
            } => self.note(planner, placement, a, b, box_index),
            Step::FragmentStart { kind, box_index } => {
                self.fragments.push(FragmentRun {
                    box_index,
                    kind,
                    top: self.cursor,
                    members: Vec::new(),
                    dividers: Vec::new(),
                });
                self.cursor += if kind == kind_code("rect") {
                    self.constant(planner, "box_margin")?
                } else {
                    let title = planner
                        .label_by_id(&format!("{}.label", planner.input.boxes[box_index].id));
                    self.section_height(planner, title)?
                };
                Ok(())
            }
            Step::FragmentElse { box_index, section } => {
                let label = planner
                    .label_by_id(&format!("{}.s{section}", planner.input.boxes[box_index].id));
                if let Some(run) = self.fragments.last_mut() {
                    run.dividers.push((self.cursor, label));
                }
                self.cursor += self.section_height(planner, label)?;
                Ok(())
            }
            Step::FragmentEnd => {
                let run = self.fragments.pop();
                match run {
                    Some(run) => self.close_fragment(planner, run),
                    None => Ok(()),
                }
            }
            Step::ActivateStart { actor } => {
                let depth = self.bar_depths[actor];
                self.bar_depths[actor] += 1;
                let centre = Self::actor_centre(planner, actor);
                let width_half = half(self.constant(planner, "activation_width")?);
                let top = self.cursor + self.constant(planner, "activation_top")?;
                self.open_bars.push(BarRun {
                    actor,
                    top,
                    x: centre + depth * width_half,
                    depth: depth + 1,
                });
                Ok(())
            }
            Step::ActivateEnd { actor } => {
                let depth = self.bar_depths[actor].saturating_sub(1);
                self.bar_depths[actor] = depth;
                let width = self.constant(planner, "activation_width")?;
                let Some(position) = self
                    .open_bars
                    .iter()
                    .rposition(|bar| bar.actor == actor && bar.depth == depth + 1)
                else {
                    return Ok(());
                };
                let bar = self.open_bars.remove(position);
                self.bars.push(Rect {
                    x: bar.x,
                    y: bar.top,
                    w: width,
                    h: (self.cursor - bar.top).max(0),
                });
                Ok(())
            }
        }
    }

    fn section_height(
        &self,
        planner: &Planner<'_>,
        label: Option<usize>,
    ) -> Result<i32, LayoutError> {
        let title_top =
            self.constant(planner, "box_margin")? + self.constant(planner, "box_text_margin")?;
        let label_lines = label
            .and_then(|position| planner.label_lines.get(position))
            .map_or(0, Vec::len);
        let label_bottom = i32::try_from(label_lines)
            .ok()
            .and_then(|lines| lines.checked_mul(Self::lh(planner)))
            .and_then(|height| height.checked_add(title_top))
            .ok_or(LayoutError::Overflow)?;
        Ok((title_top + self.constant(planner, "label_box_height")?).max(label_bottom))
    }

    fn add_member(&mut self, rect: Rect) {
        if let Some(run) = self.fragments.last_mut() {
            run.members.push(rect);
        }
    }

    fn message(
        &mut self,
        planner: &Planner<'_>,
        from: usize,
        to: usize,
        flags: usize,
        route: usize,
        destroyed: usize,
    ) -> Result<(), LayoutError> {
        let label_position = planner.label_position_of_route(route);
        let lines = label_position.and_then(|position| planner.label_lines.get(position));
        let count = lines.map_or(0, |lines| lines.len()) as i32;
        let lh = Self::lh(planner);
        let label_w = lines.map_or(0, |lines| {
            lines.iter().map(|line| line.width).max().unwrap_or(0)
        });
        let c_from = Self::actor_centre(planner, from);
        let c_to = Self::actor_centre(planner, to);
        let y = self.cursor + self.constant(planner, "message_top")? + count * lh;
        let mut row_h = self.constant(planner, "message_top")?
            + count * lh
            + self.constant(planner, "box_margin")?;
        let creates = flags & FLAG_CREATES != 0;
        let destroys = flags & FLAG_DESTROYS != 0;
        let self_loop = from == to;
        let mut dx = 0;
        if self_loop {
            let padding = self.constant(planner, "wrap_padding")?;
            dx = half(label_w + 2 * padding).max(self.constant(planner, "self_loop_min_dx")?);
            row_h += self.constant(planner, "self_loop_depth")?;
        }
        if creates && let Some(box_index) = Self::actor_box(planner, to) {
            let width = planner.widths.get(to).copied().unwrap_or(0);
            let height = planner.heights.get(to).copied().unwrap_or(0);
            let rect = Rect {
                x: c_to - half(width),
                y,
                w: width,
                h: height,
            };
            self.box_rects[box_index] = rect;
            self.add_member(rect);
            row_h += height + self.constant(planner, "box_margin")?;
        }
        if destroys
            && destroyed != NO_DESTROYED
            && let Some(end) = self.destroyed_y.get_mut(destroyed)
        {
            *end = Some(y);
        }
        let points = if self_loop {
            let bottom = self.box_rects[Self::actor_box(planner, from).unwrap_or(0)];
            vec![
                Point {
                    x: c_from,
                    y: bottom.y + bottom.h,
                },
                Point { x: c_from, y },
                Point { x: c_from + dx, y },
                Point {
                    x: c_from + dx,
                    y: y + self.constant(planner, "self_loop_depth")?,
                },
                Point {
                    x: c_from,
                    y: y + self.constant(planner, "self_loop_depth")?,
                },
                Point {
                    x: c_from,
                    y: bottom.y + bottom.h,
                },
            ]
        } else {
            let from_box = Self::actor_box(planner, from).unwrap_or(0);
            let to_box = Self::actor_box(planner, to).unwrap_or(0);
            vec![
                Point {
                    x: c_from,
                    y: self.box_rects[from_box].y + self.box_rects[from_box].h,
                },
                Point { x: c_from, y },
                Point { x: c_to, y },
                Point {
                    x: c_to,
                    y: self.box_rects[to_box].y + self.box_rects[to_box].h,
                },
            ]
        };
        let loop_depth = self.constant(planner, "self_loop_depth")?;
        let label_top = self.cursor + self.constant(planner, "message_top")?;
        let start_marker = marker_start_name(planner, route).map(|name| {
            let axis = if c_to >= c_from {
                MarkerAxis::MinusX
            } else {
                MarkerAxis::PlusX
            };
            (points[1], name, axis)
        });
        let end_marker = marker_end_name(planner, route).map(|name| {
            let (point, axis) = if self_loop {
                (
                    Point {
                        x: c_from,
                        y: y + loop_depth,
                    },
                    MarkerAxis::MinusX,
                )
            } else if c_to >= c_from {
                (Point { x: c_to, y }, MarkerAxis::PlusX)
            } else {
                (Point { x: c_to, y }, MarkerAxis::MinusX)
            };
            (point, name, axis)
        });
        let mut central = Vec::new();
        if flags & FLAG_CENTRAL_START != 0 {
            central.push((Point { x: c_from, y }, true));
        }
        if flags & FLAG_CENTRAL_END != 0 {
            central.push((Point { x: c_to, y }, false));
        }
        let badge = if planner.profile == Profile::Vector && flags & FLAG_NUMBERED != 0 {
            Some(Point { x: c_from, y })
        } else {
            None
        };

        self.route_runs.push(RouteRun {
            points,
            start_marker,
            end_marker,
            central,
            badge,
        });
        if lines.is_some()
            && let Some(position) = label_position
        {
            self.label_rects[position] = Rect {
                x: half(c_from + c_to) - half(label_w),
                y: label_top,
                w: label_w,
                h: count * lh,
            };
        }
        let span = Rect {
            x: c_from.min(c_to) - dx,
            y: self.cursor,
            w: (c_from.max(c_to) - c_from.min(c_to)) + 2 * dx,
            h: row_h,
        };
        self.add_member(span);
        self.cursor += row_h;
        self.bottom = self.bottom.max(self.cursor);
        Ok(())
    }

    fn note(
        &mut self,
        planner: &Planner<'_>,
        placement: usize,
        a: usize,
        b: usize,
        box_index: usize,
    ) -> Result<(), LayoutError> {
        let note_pad = self.constant(planner, "note_margin")?;
        let margin = self.constant(planner, "actor_margin")?;
        let text_w = planner.box_label_width(box_index);
        let lines = planner
            .input
            .labels
            .iter()
            .position(|label| label.owner == planner.input.boxes[box_index].id)
            .and_then(|position| planner.label_lines.get(position));
        let count = lines.map_or(0, |lines| lines.len()) as i32;
        let lh = Self::lh(planner);
        let text_h = count * lh;
        let c_a = Self::actor_centre(planner, a);
        let c_b = Self::actor_centre(planner, b);
        let w_a = planner.widths.get(a).copied().unwrap_or(0);
        let (x, width) = match placement {
            2 if a == b => {
                let width = w_a.max(text_w + 2 * note_pad);
                (c_a - half(width), width)
            }
            2 => {
                let left = c_a.min(c_b) - half(margin);
                let right = c_a.max(c_b) + half(margin);
                (left, (right - left).max(text_w + 2 * note_pad))
            }
            1 => {
                let width = w_a.max(text_w + 2 * note_pad);
                (c_a + half(w_a) + half(margin), width)
            }
            _ => {
                let width = w_a.max(text_w + 2 * note_pad);
                (c_a - half(w_a) - half(margin) - width, width)
            }
        };
        let bm = self.constant(planner, "box_margin")?;
        let top = self.cursor + bm;
        let height = text_h + 2 * note_pad;
        let rect = Rect {
            x,
            y: top,
            w: width,
            h: height,
        };
        self.box_rects[box_index] = rect;
        self.add_member(rect);
        let position = planner
            .input
            .labels
            .iter()
            .position(|label| label.owner == planner.input.boxes[box_index].id);
        if let Some(position) = position {
            self.label_rects[position] = Rect {
                x: x + note_pad,
                y: top + note_pad,
                w: (width - 2 * note_pad).max(0),
                h: text_h,
            };
        }
        self.cursor += bm + height;
        self.bottom = self.bottom.max(self.cursor);
        Ok(())
    }

    fn close_fragment(
        &mut self,
        planner: &Planner<'_>,
        run: FragmentRun,
    ) -> Result<(), LayoutError> {
        let bm = self.constant(planner, "box_margin")?;
        let left = run.members.iter().map(|rect| rect.x).min().unwrap_or(0);
        let right = run
            .members
            .iter()
            .map(|rect| rect.x + rect.w)
            .max()
            .unwrap_or(0);
        let natural = (right - left) + 2 * bm;
        let mut width = natural;
        if run.kind != kind_code("rect") {
            let title = planner.input.boxes[run.box_index].text.clone();
            let metric = metric_of(planner.profile, Role::Label);
            let bracketed = format!("[{title}]");
            let title_w = measure(&bracketed, i32::MAX, metric)
                .map(|lines| lines.iter().map(|line| line.width).max().unwrap_or(0))
                .unwrap_or(0);
            let minimum = self.constant(planner, "label_box_width")? + 2 * bm;
            width = width.max(minimum).max(title_w + 2 * bm);
            for (_, section) in &run.dividers {
                let section_w = section
                    .and_then(|position| planner.label_lines.get(position))
                    .map_or(0, |lines| {
                        lines.iter().map(|line| line.width).max().unwrap_or(0)
                    });
                width = width.max(section_w + 2 * bm);
            }
        }
        let bottom = self.cursor + bm;
        let rect = Rect {
            x: left - bm - half(width - natural),
            y: run.top,
            w: width,
            h: bottom - run.top,
        };
        self.cursor = bottom;
        self.box_rects[run.box_index] = rect;
        self.bottom = self.bottom.max(bottom);
        if run.kind != kind_code("rect") {
            let title_top = self.constant(planner, "box_margin")?
                + self.constant(planner, "box_text_margin")?;
            let title =
                planner.label_by_id(&format!("{}.label", planner.input.boxes[run.box_index].id));
            self.centre_label(planner, title, rect, run.top + title_top);
            for (divider, section) in &run.dividers {
                self.centre_label(planner, *section, rect, divider + title_top);
            }
        }
        self.closed_frames.push((run.box_index, run.dividers));
        if let Some(parent) = self.fragments.last_mut() {
            parent.members.push(rect);
        }
        Ok(())
    }

    /// Centres a label horizontally in `frame`, with its top at `top`.
    fn centre_label(&mut self, planner: &Planner<'_>, label: Option<usize>, frame: Rect, top: i32) {
        let Some(position) = label else {
            return;
        };
        let Some(lines) = planner.label_lines.get(position) else {
            return;
        };
        let width = lines.iter().map(|line| line.width).max().unwrap_or(0);
        self.label_rects[position] = Rect {
            x: frame.x + half(frame.w - width),
            y: top,
            w: width,
            h: lines.len() as i32 * Self::lh(planner),
        };
    }
}

fn zero_rect() -> Rect {
    Rect {
        x: 0,
        y: 0,
        w: 0,
        h: 0,
    }
}

fn marker_start_name(planner: &Planner<'_>, route: usize) -> Option<MarkerName> {
    route_marker(planner, route, true)
}

fn marker_end_name(planner: &Planner<'_>, route: usize) -> Option<MarkerName> {
    route_marker(planner, route, false)
}

const MARKER_NAMES: [&str; 7] = [
    "arrowhead",
    "crosshead",
    "filled-head",
    "solidTopArrowHead",
    "solidBottomArrowHead",
    "stickTopArrowHead",
    "stickBottomArrowHead",
];

fn route_marker(planner: &Planner<'_>, route: usize, start: bool) -> Option<MarkerName> {
    let row = planner.input.routes.get(route)?;
    let name = if start {
        row.marker_start.as_str()
    } else {
        row.marker_end.as_str()
    };
    if name.is_empty() || name == "none" || name == "point" {
        return None;
    }
    let static_name = MARKER_NAMES.iter().find(|candidate| **candidate == name)?;
    MarkerName::new(static_name)
}

impl Planner<'_> {
    fn label_position_of_route(&self, route: usize) -> Option<usize> {
        let route = self.input.routes.get(route)?;
        self.input
            .labels
            .iter()
            .position(|label| label.owner == route.id)
    }

    fn fill(&mut self, walk: &Walk) -> Result<Size, LayoutError> {
        let margin_x = constant(self.profile, "diagram_margin_x")?;
        let margin_y = constant(self.profile, "diagram_margin_y")?;
        let mut min_x = 0;
        let mut max_x = 0;
        let mut max_y = walk.bottom;
        for rect in &walk.box_rects {
            min_x = min_x.min(rect.x);
            max_x = max_x.max(rect.x + rect.w);
            max_y = max_y.max(rect.y + rect.h);
        }
        for run in &walk.route_runs {
            for point in &run.points {
                min_x = min_x.min(point.x);
                max_x = max_x.max(point.x);
                max_y = max_y.max(point.y);
            }
        }
        for rect in &walk.bars {
            min_x = min_x.min(rect.x);
            max_x = max_x.max(rect.x + rect.w);
            max_y = max_y.max(rect.y + rect.h);
        }
        for rect in &walk.label_rects {
            if rect.w == 0 && rect.h == 0 {
                continue;
            }
            min_x = min_x.min(rect.x);
            max_x = max_x.max(rect.x + rect.w);
            max_y = max_y.max(rect.y + rect.h);
        }
        if min_x > max_x {
            self.shift_x = margin_x;
            self.shift_y = margin_y;
            return Ok(Size {
                w: 2 * margin_x,
                h: 2 * margin_y,
            });
        }
        self.shift_x = margin_x - min_x;
        self.shift_y = margin_y;
        for (box_, rect) in self.input.boxes.iter().zip(&walk.box_rects) {
            let Some(target) = self.dump.boxes.iter_mut().find(|scene| scene.id == box_.id) else {
                continue;
            };
            target.rect = Rect {
                x: rect.x + self.shift_x,
                y: rect.y + self.shift_y,
                w: rect.w,
                h: rect.h,
            };
        }
        for (route, run) in self.input.routes.iter().zip(&walk.route_runs) {
            let mut points: Vec<Point> = run
                .points
                .iter()
                .map(|point| Point {
                    x: point.x + self.shift_x,
                    y: point.y + self.shift_y,
                })
                .collect();
            let port = |id: &str| {
                let at = self.input.boxes.iter().position(|box_| box_.id == id)?;
                let rect = walk.box_rects.get(at)?;
                Some(rect.y + rect.h + self.shift_y)
            };
            if let (Some(first), Some(y)) = (points.first_mut(), port(&route.from)) {
                first.y = y;
            }
            if let (Some(last), Some(y)) = (points.last_mut(), port(&route.to)) {
                last.y = y;
            }
            let Some(target) = self
                .dump
                .routes
                .iter_mut()
                .find(|scene| scene.id == route.id)
            else {
                continue;
            };
            target.points = points;
        }
        for ((label, lines), rect) in self
            .input
            .labels
            .iter()
            .zip(&self.label_lines)
            .zip(&walk.label_rects)
        {
            let Some(target) = self
                .dump
                .labels
                .iter_mut()
                .find(|scene| scene.id == label.id)
            else {
                continue;
            };
            target.rect = Rect {
                x: rect.x + self.shift_x,
                y: rect.y + self.shift_y,
                w: rect.w,
                h: rect.h,
            };
            target.lines = lines.iter().map(|line| line.text.clone()).collect();
        }
        Ok(Size {
            w: max_x - min_x + 2 * margin_x,
            h: max_y + 2 * margin_y,
        })
    }

    fn assemble(&self) -> Vec<SceneGroup> {
        let mut groups = Vec::new();
        self.bar_group(&mut groups);
        self.group_frames(&mut groups);
        self.edge_groups(&mut groups);
        self.node_groups(&mut groups);
        groups
    }

    fn bar_group(&self, groups: &mut Vec<SceneGroup>) {
        if self.bars.is_empty() {
            return;
        }
        let cell = self.profile == Profile::Cell;
        let mut items = Vec::new();
        for bar in &self.bars {
            let rect = Rect {
                x: bar.x + self.shift_x,
                y: bar.y + self.shift_y,
                w: bar.w,
                h: bar.h,
            };
            if !cell {
                items.push(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Node),
                    rect,
                }));
                continue;
            }
            for (from, to) in self.free_runs(rect.x, rect.y, rect.y + rect.h - 1) {
                if to > from {
                    items.push(Item::Polyline(PolylineItem {
                        shape: Shape::plain(ShapeStyle::Node).with_width(Width::Emphasis),
                        points: vec![Point { x: rect.x, y: from }, Point { x: rect.x, y: to }],
                        corner: 0,
                    }));
                }
            }
        }
        groups.push(SceneGroup {
            role: GroupRole::Decor,
            owner: String::new(),
            items,
        });
    }

    fn group_frames(&self, groups: &mut Vec<SceneGroup>) {
        for (index, box_) in self.input.boxes.iter().enumerate() {
            if box_.role != BoxRole::Group {
                continue;
            }
            let rect = self.dump.boxes[index].rect;
            let mut items = Vec::new();
            let shape = box_.shape.as_str();
            if shape == "rect" {
                items.push(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Band),
                    rect,
                }));
            } else if is_fragment(shape) {
                items.push(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Group),
                    rect,
                }));
                self.kind_box(shape, rect, index, &mut items);
            } else {
                items.push(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Group),
                    rect,
                }));
            }
            if let Some(label) = self.box_title_position(index) {
                items.push(self.label_item(label));
            }
            groups.push(SceneGroup {
                role: GroupRole::Group,
                owner: box_.id.clone(),
                items,
            });
        }
    }

    fn kind_label_rect(&self, frame: Rect) -> Option<Rect> {
        let w = constant(self.profile, "label_box_width").ok()?;
        let h = constant(self.profile, "label_box_height").ok()?;
        let inset = i32::from(self.profile == Profile::Cell);
        Some(Rect {
            x: frame.x + inset,
            y: frame.y + inset,
            w,
            h,
        })
    }

    /// Inclusive row runs of column `column` between `first` and `last` that no text label
    /// covers. The cell profile leaves out the rows where a label crosses the column,
    /// because a label never overwrites a line; the vector profile leaves out nothing.
    fn free_runs(&self, column: i32, first: i32, last: i32) -> Vec<(i32, i32)> {
        if self.profile != Profile::Cell {
            return vec![(first, last)];
        }
        let kind_labels = self
            .input
            .boxes
            .iter()
            .zip(&self.dump.boxes)
            .filter(|(box_, _)| {
                box_.role == BoxRole::Group && is_fragment(&box_.shape) && box_.shape != "rect"
            })
            .filter_map(|(_, scene)| self.kind_label_rect(scene.rect));
        let mut blocked: Vec<(i32, i32)> = self
            .dump
            .labels
            .iter()
            .map(|label| label.rect)
            .chain(kind_labels)
            .filter(|rect| rect.w > 0 && rect.h > 0 && rect.x <= column && column < rect.x + rect.w)
            .map(|rect| (rect.y, rect.y + rect.h - 1))
            .collect();
        blocked.sort_unstable();
        let mut runs = Vec::new();
        let mut from = first;
        for (top, bottom) in blocked {
            if top > from {
                runs.push((from, top - 1));
            }
            from = from.max(bottom + 1);
        }
        if last >= from {
            runs.push((from, last));
        }
        runs
    }

    /// Lifeline pieces from `top` to `end`, without the rows that a cell label covers.
    fn lifeline_segments(&self, centre: i32, top: i32, end: i32) -> Vec<Vec<Point>> {
        self.free_runs(centre, top, end)
            .into_iter()
            .filter(|(from, to)| to > from)
            .map(|(from, to)| vec![Point { x: centre, y: from }, Point { x: centre, y: to }])
            .collect()
    }

    fn kind_box(&self, shape: &str, rect: Rect, index: usize, items: &mut Vec<Item>) {
        let Some(position) = self.kind_label_rect(rect) else {
            return;
        };
        let cell = self.profile == Profile::Cell;
        if !cell {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Ink),
                rect: position,
            }));
        }
        items.push(Item::Text(TextItem {
            rect: position,
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: if cell {
                TextStyle::Text
            } else {
                TextStyle::TextInverse
            },
            series: 0,
            lines: vec![vec![Run::plain(shape)]],
        }));
        let right = rect.x + rect.w - i32::from(cell);
        for (divider, section) in self.dividers(index) {
            let y = divider + self.shift_y;
            items.push(Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Rule).with_line(StyleLine::Dotted),
                points: vec![Point { x: rect.x, y }, Point { x: right, y }],
                corner: 0,
            }));
            if let Some(at) = section {
                items.push(self.label_item(at));
            }
        }
    }

    fn box_title_position(&self, index: usize) -> Option<usize> {
        let id = self.input.boxes.get(index)?.id.clone();
        self.input
            .labels
            .iter()
            .position(|label| label.owner == id && label.id.ends_with(".label"))
    }

    fn dividers(&self, index: usize) -> Dividers {
        self.closed_frames
            .iter()
            .find(|(frame, _)| *frame == index)
            .map(|(_, dividers)| dividers.clone())
            .unwrap_or_default()
    }

    fn label_by_id(&self, id: &str) -> Option<usize> {
        self.input.labels.iter().position(|label| label.id == id)
    }

    fn label_item(&self, position: usize) -> Item {
        let label = &self.input.labels[position];
        let scene = &self.dump.labels[position];
        let role = if label.role == TextRole::Body {
            TextRole::Body
        } else {
            TextRole::Label
        };
        Item::Text(TextItem {
            rect: scene.rect,
            role,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: runs_of(&self.label_lines[position]),
        })
    }

    fn edge_groups(&self, groups: &mut Vec<SceneGroup>) {
        for (index, route) in self.input.routes.iter().enumerate() {
            let Some(run) = self.route_runs.get(index) else {
                continue;
            };
            let mut shape = Shape::plain(ShapeStyle::Edge);
            if route.line == "dotted" {
                shape.line = StyleLine::Dotted;
            }
            let route_points = &self.dump.routes[index].points;
            let drawn = if route_points.len() > 2 {
                &route_points[1..route_points.len() - 1]
            } else {
                &route_points[..]
            };
            let mut items = vec![Item::Polyline(PolylineItem {
                shape,
                points: drawn.to_vec(),
                corner: self.corner,
            })];
            let radius = constant(self.profile, "autonumber_radius").unwrap_or(1);
            for (point, _) in &run.central {
                items.push(Item::Ellipse(EllipseItem {
                    shape: Shape::plain(ShapeStyle::Mark),
                    cx: point.x + self.shift_x,
                    cy: point.y + self.shift_y,
                    rx: radius,
                    ry: radius,
                }));
            }
            if let Some(point) = run.badge {
                items.push(Item::Ellipse(EllipseItem {
                    shape: Shape::plain(ShapeStyle::Ink),
                    cx: point.x + self.shift_x,
                    cy: point.y + self.shift_y,
                    rx: radius,
                    ry: radius,
                }));
            }
            for (point, name, axis) in [run.start_marker, run.end_marker].into_iter().flatten() {
                items.push(Item::MarkerRef(MarkerRefItem {
                    marker: name,
                    at: Point {
                        x: point.x + self.shift_x,
                        y: point.y + self.shift_y,
                    },
                    axis,
                }));
            }
            if let Some(position) = self
                .input
                .labels
                .iter()
                .position(|label| label.owner == route.id)
            {
                items.push(self.label_item(position));
            }
            groups.push(SceneGroup {
                role: GroupRole::Edge,
                owner: route.id.clone(),
                items,
            });
        }
    }

    fn node_groups(&self, groups: &mut Vec<SceneGroup>) {
        let radius = if self.profile == Profile::Cell {
            0
        } else {
            RULE_RADIUS_UNITS
        };
        for (index, box_) in self.input.boxes.iter().enumerate() {
            if box_.role != BoxRole::Node {
                continue;
            }
            let rect = self.dump.boxes[index].rect;
            let mut items = Vec::new();
            match box_.shape.as_str() {
                "note" => items.push(Item::Rect(RectItem {
                    shape: Shape::plain(ShapeStyle::Note),
                    rect,
                })),
                _ => {
                    let ordinal = self
                        .actor_boxes
                        .iter()
                        .position(|at| *at == index)
                        .unwrap_or(0);
                    let centre = self
                        .centres
                        .get(ordinal)
                        .copied()
                        .unwrap_or(rect.x + half(rect.w))
                        + self.shift_x;
                    let end = self
                        .destroyed_ys
                        .get(ordinal)
                        .copied()
                        .flatten()
                        .map_or(self.bottom + self.shift_y, |y| y + self.shift_y);
                    items.push(Item::RoundRect(RoundRectItem {
                        shape: Shape::plain(ShapeStyle::Node),
                        rect,
                        r: radius,
                    }));
                    for points in self.lifeline_segments(centre, rect.y + rect.h, end) {
                        items.push(Item::Polyline(PolylineItem {
                            shape: Shape::plain(ShapeStyle::Rule),
                            points,
                            corner: 0,
                        }));
                    }
                    let destroyed = self.destroyed_ys.get(ordinal).copied().flatten().is_some();
                    if destroyed && let Some(marker) = MarkerName::new("crosshead") {
                        items.push(Item::MarkerRef(MarkerRefItem {
                            marker,
                            at: Point { x: centre, y: end },
                            axis: MarkerAxis::PlusY,
                        }));
                    }
                    if let Some(lines) = self
                        .actor_lines
                        .get(ordinal)
                        .filter(|lines| !lines.is_empty())
                    {
                        let text_h = lines.len() as i32 * line_height(self.profile);
                        items.push(Item::Text(TextItem {
                            rect: Rect {
                                x: rect.x,
                                y: rect.y + half(rect.h - text_h),
                                w: rect.w,
                                h: text_h,
                            },
                            role: TextRole::Label,
                            size: 14,
                            align: Align::Middle,
                            style: TextStyle::Text,
                            series: 0,
                            lines: runs_of(lines),
                        }));
                    }
                }
            }
            if let Some(position) = self.box_title_position(index) {
                items.push(self.label_item(position));
            }
            groups.push(SceneGroup {
                role: GroupRole::Node,
                owner: box_.id.clone(),
                items,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{centres, half, widen};
    use crate::geom::Rect;
    use crate::model::sequence as ms;
    use crate::scene::{BoxRole, DumpOptions, GroupRole, Item, MarkerAxis, Profile, Scene};
    use crate::syntax::sequence::parse;

    fn model_of(source: &str) -> ms::Model {
        let parsed = parse(source, &[]);
        let (model, diagnostics) = ms::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        model
    }

    fn layout_of(source: &str, profile: Profile) -> Result<Scene, &'static str> {
        let model = model_of(source);
        let input = super::from_sequence(&model, profile, DumpOptions::default())
            .map_err(|_| "adapter failed")?;
        let (scene, _) = super::layout(&input).map_err(|_| "layout failed")?;
        Ok(scene)
    }

    #[test]
    fn widening_splits_with_floor_division_and_leading_remainder() {
        let mut gaps = [10, 10];
        widen(&mut gaps, 0, 2, 35);
        assert_eq!(gaps, [18, 17]);
        let mut gaps = [10, 10];
        widen(&mut gaps, 0, 2, 36);
        assert_eq!(gaps, [18, 18]);
        let mut gaps = [5];
        widen(&mut gaps, 0, 1, 40);
        assert_eq!(gaps, [40]);
        let mut gaps = [10];
        widen(&mut gaps, 0, 1, 5);
        assert_eq!(gaps, [10]);
    }

    fn bars(scene: &Scene) -> Vec<Rect> {
        let mut rects: Vec<Rect> = scene
            .items()
            .iter()
            .filter(|group| group.role == GroupRole::Decor)
            .flat_map(|group| group.items.iter())
            .filter_map(|item| match item {
                Item::Rect(rect) => Some(rect.rect),
                Item::Polyline(line) => {
                    let (first, last) = (line.points.first()?, line.points.last()?);
                    Some(Rect {
                        x: first.x,
                        y: first.y,
                        w: 1,
                        h: last.y - first.y + 1,
                    })
                }
                _ => None,
            })
            .collect();
        rects.sort_by_key(|rect| (rect.x, rect.y));
        rects
    }

    #[test]
    fn activation_offset_moves_by_half_width_per_depth() -> Result<(), &'static str> {
        assert_eq!(half(640), 320);
        let source = "sequenceDiagram\nparticipant A\nparticipant B\nA->>+B: one\nA->>+B: two\nB-->>-A: three\nB-->>-A: four\n";
        let scene = layout_of(source, Profile::Vector)?;
        let bars = bars(&scene);
        assert_eq!(bars.len(), 2);
        assert_eq!(bars[1].x - bars[0].x, 320);
        assert!(bars[0].y < bars[1].y);
        assert!(bars[1].y + bars[1].h < bars[0].y + bars[0].h);
        Ok(())
    }

    #[test]
    fn unclosed_activation_extends_to_the_last_row() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nloop L\nA->>+B: one\nend\nA->>B: two\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = layout_of(source, profile)?;
            let bars = bars(&scene);
            assert_eq!(bars.len(), 1);
            assert!(bars[0].h > 0, "{profile:?}: {:?}", bars[0]);
            let valid = scene.check().map_err(|_| "validate failed")?;
            assert!(valid, "{profile:?}: {:?}", scene.validate());
        }
        Ok(())
    }

    #[test]
    fn destroyed_actor_keeps_its_header_and_ends_its_lifeline() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nA->>B: one\ndestroy B\nA-xB: two\nA->>A: three\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = layout_of(source, profile)?;
            let header = |id: &str| {
                scene
                    .boxes()
                    .iter()
                    .find(|box_| box_.id == id)
                    .map(|box_| box_.rect)
            };
            let (a, b) = (
                header("A").ok_or("A missing")?,
                header("B").ok_or("B missing")?,
            );
            assert_eq!(a.y, b.y, "{profile:?}: both headers share the top band");
            let crosses = scene
                .items()
                .iter()
                .flat_map(|group| group.items.iter())
                .filter(|item| matches!(item, Item::MarkerRef(marker) if marker.axis == MarkerAxis::PlusY))
                .count();
            assert_eq!(crosses, 1, "{profile:?}: one destroy cross");
            assert!(scene.check().map_err(|_| "validate failed")?, "{profile:?}");
        }
        Ok(())
    }

    #[test]
    fn participant_box_title_and_else_titles_get_rects() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nbox Team Name\nparticipant A\nend\nalt first\nA->>A: x\nelse a long second title\nA->>A: y\nend\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = layout_of(source, profile)?;
            for label in scene.labels() {
                if label.id.ends_with(".label") || label.id.contains(".s") {
                    assert!(
                        label.rect.w > 0 && label.rect.h > 0,
                        "{profile:?}: {}",
                        label.id
                    );
                }
            }
            let frame = scene
                .boxes()
                .iter()
                .find(|box_| box_.id == "f0")
                .ok_or("frame missing")?;
            let section = scene
                .labels()
                .iter()
                .find(|label| label.id == "f0.s0")
                .ok_or("section label missing")?;
            assert!(
                section.rect.x > frame.rect.x
                    && section.rect.x + section.rect.w < frame.rect.x + frame.rect.w,
                "{profile:?}: section title inside its frame"
            );
            assert!(scene.check().map_err(|_| "validate failed")?, "{profile:?}");
        }
        Ok(())
    }

    #[test]
    fn lifeline_centres_are_one_gap_apart() -> Result<(), &'static str> {
        let scene = layout_of("sequenceDiagram\nA->>B: x\n", Profile::Vector)?;
        let centre = |id: &str| {
            scene
                .boxes()
                .iter()
                .find(|box_| box_.id == id)
                .map(|box_| box_.rect.x + half(box_.rect.w))
        };
        let (a, b) = (
            centre("A").ok_or("A missing")?,
            centre("B").ok_or("B missing")?,
        );
        assert_eq!(b - a, 9600 + 3200);
        Ok(())
    }

    fn centre_of(scene: &Scene, id: &str) -> Result<i32, &'static str> {
        scene
            .boxes()
            .iter()
            .find(|box_| box_.id == id)
            .map(|box_| box_.rect.x + half(box_.rect.w))
            .ok_or("box missing")
    }

    #[test]
    fn message_labels_follow_their_routes_after_an_empty_message() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nparticipant A\nparticipant B\nparticipant C\nA->>B:\nB->>C: a deliberately long message label\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = layout_of(source, profile)?;
            let constant = |name: &str| super::constant(profile, name).map_err(|_| "constant");
            let label = scene
                .labels()
                .iter()
                .find(|label| label.owner == "e1")
                .ok_or("label missing")?;
            let (a, b, c) = (
                centre_of(&scene, "A")?,
                centre_of(&scene, "B")?,
                centre_of(&scene, "C")?,
            );
            let margin = constant("actor_margin")?;
            assert_eq!(
                b - a,
                half(2 * constant("actor_width")?) + margin,
                "{profile:?}: an empty message widens nothing"
            );
            assert!(
                c - b >= label.rect.w + 2 * constant("wrap_padding")? + margin,
                "{profile:?}: the second gap covers its own label"
            );
            assert_eq!(
                label.rect.x,
                half(b + c) - half(label.rect.w),
                "{profile:?}"
            );
            let first = &scene.routes().first().ok_or("route missing")?.points;
            assert_eq!(
                first[1].y - first[0].y,
                2 * constant("box_margin")? + constant("message_top")?,
                "{profile:?}: an empty message row holds no label line"
            );
        }
        Ok(())
    }

    #[test]
    fn fragment_ids_count_fragments_in_declaration_order() -> Result<(), &'static str> {
        let ids_of = |source: &str| -> Result<Vec<String>, &'static str> {
            let scene = layout_of(source, Profile::Vector)?;
            Ok(scene.boxes().iter().map(|box_| box_.id.clone()).collect())
        };
        let nested = "sequenceDiagram\nloop a\nA->>B: x\nend\nalt b\nA->>B: y\nloop c\nA->>B: z\nend\nend\nopt d\nA->>B: w\nend\n";
        assert_eq!(ids_of(nested)?, ["A", "B", "f0", "f1", "f2", "f3"]);
        let clash = "sequenceDiagram\nparticipant f0\nloop a\nf0->>f0: x\nend\n";
        assert_eq!(ids_of(clash)?, ["f0", "f0~1"]);
        Ok(())
    }

    #[test]
    fn routes_take_the_shared_corner_radius() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nA->>A: self\nA->>B: out\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let want = super::corner_radius(profile).map_err(|_| "constant")?;
            let scene = layout_of(source, profile)?;
            let corners: Vec<i32> = scene
                .items()
                .iter()
                .filter(|group| group.role == GroupRole::Edge)
                .flat_map(|group| group.items.iter())
                .filter_map(|item| match item {
                    Item::Polyline(line) => Some(line.corner),
                    _ => None,
                })
                .collect();
            assert_eq!(corners, [want, want], "{profile:?}");
            if profile == Profile::Vector {
                assert_eq!(want, 512);
            }
        }
        Ok(())
    }

    #[test]
    fn centres_keep_declaration_order() {
        let widths = [30, 20];
        let centres = centres(&widths, &[25]);
        assert_eq!(centres, [15, 40]);
    }

    #[test]
    fn sequence_scene_validates_under_both_profiles() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nparticipant Alice as Alice\nparticipant Bob\nautonumber 5\nAlice->>+Bob: Request\nBob-->>-Alice: Reply\nNote right of Bob: thinking\nloop every day\nAlice->>Bob: ping\nend\nbox Team\nparticipant Carol\nend\n";
        for profile in [Profile::Vector, Profile::Cell] {
            let scene = layout_of(source, profile).map_err(|_| "layout failed")?;
            let valid = scene.check().map_err(|_| "validate failed")?;
            assert!(valid, "{profile:?}: {:?}", scene.validate());
        }
        Ok(())
    }

    #[test]
    fn frames_stay_clear_of_foreign_boxes_and_labels() -> Result<(), &'static str> {
        let sources = [
            "sequenceDiagram\nparticipant A\nbox Group\nend\nparticipant B\n",
            "sequenceDiagram\nA->>B: hi\nbox Group\nparticipant A\nparticipant C\nend\n",
            "sequenceDiagram\nparticipant A\nloop first<br>second\nend\n",
            "sequenceDiagram\nparticipant A\nalt ok\nA->>A: x\nelse first<br>second<br>third\nopt inner\nA->>A: y\nend\nend\n",
            "sequenceDiagram\nactor A\nactor B as wide wide wide wide\nbox Wide title for the box that is long\nactor C as mid size\nend\nNote over B,B: two<br>lines\nC-->>+B: hi\n",
        ];
        for source in sources {
            for profile in [Profile::Vector, Profile::Cell] {
                let scene = layout_of(source, profile)?;
                let valid = scene.check().map_err(|_| "validate failed")?;
                assert!(valid, "{source:?} {profile:?}: {:?}", scene.validate());
            }
        }
        Ok(())
    }

    #[test]
    fn box_members_have_adjacent_lifelines() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nA->>B: hi\nbox Group\nparticipant A\nparticipant C\nend\n";
        let scene = layout_of(source, Profile::Vector)?;
        let actors: Vec<&str> = scene
            .boxes()
            .iter()
            .filter(|box_| box_.role == BoxRole::Node)
            .map(|box_| box_.id.as_str())
            .collect();
        assert_eq!(actors, ["A", "C", "B"]);
        Ok(())
    }

    #[test]
    fn box_without_member_is_not_a_dump_box() -> Result<(), &'static str> {
        let source = "sequenceDiagram\nparticipant A\nbox Group\nend\n";
        let scene = layout_of(source, Profile::Vector)?;
        assert!(scene.boxes().iter().all(|box_| box_.role != BoxRole::Group));
        Ok(())
    }
}
