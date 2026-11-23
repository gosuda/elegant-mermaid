//! The packet kind adapter (`spec/layout/grid.md`, Packet): [`from_packet`] authors the
//! model-stage dump (an optional title box, one box per field piece, and the bit numbers
//! as labels) and [`layout`] feeds the grid packet engine with measured bit-number sizes,
//! then draws the scene under both profiles.
//!
//! Box encoding: the title box has shape `title`; a piece box has the shape
//! `field;start=S;end=E`. A box whose text is not its id owns a `<id>.label` record;
//! the bit numbers are `<id>.bit` for a single bit and `<id>.lead` and `<id>.trail`
//! otherwise. The layout-stage dump lists the bit numbers only.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{self, GeomError, Rect, Size};
use crate::layout::grid::packet::{self as engine, PacketInput, PacketLayout, PacketParams};
use crate::measure::{self, Metric, Role, StyledLine};
use crate::model::packet as mp;
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, DumpValue, Group as SceneGroup, GroupRole, Item,
    Profile, RectItem, Run, Scene, SceneBox, SceneLabel, Shape, ShapeStyle, TextItem, TextRole,
    TextStyle,
};

use super::input::{Box as InputBox, Input, Label as InputLabel, Spacing};
use super::layered::LayoutError;

const KIND: &str = "packet";
const TITLE_ID: &str = "title";
const TITLE_SHAPE: &str = "title";
const FIELD_SHAPE: &str = "field";
const UNITS_PER_PX: i32 = 64;

pub(crate) fn from_packet(
    model: &mp::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(model
        .config
        .iter()
        .map(|entry| (entry.key.to_owned(), dump_value(&entry.setting)))
        .collect::<BTreeMap<_, _>>());
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
    if !model.title.is_empty() {
        add_box(
            &mut input,
            TITLE_ID,
            TITLE_SHAPE,
            TextRole::Title,
            &model.title,
        );
    }
    for (i, piece) in model.pieces.iter().enumerate() {
        let id = piece_id(i);
        let shape = format!("{FIELD_SHAPE};start={};end={}", piece.start, piece.end);
        add_box(&mut input, &id, &shape, TextRole::Label, &piece.label);
        if model.show_bits {
            add_bit_labels(&mut input, &id, piece, model.descending);
        }
    }
    Ok(input)
}

fn piece_id(index: usize) -> String {
    format!("f{index}")
}

fn dump_value(setting: &mp::ConfigSetting) -> DumpValue {
    match setting {
        mp::ConfigSetting::Integer(n) => DumpValue::Integer(*n),
        mp::ConfigSetting::Bool(flag) => DumpValue::Bool(*flag),
        mp::ConfigSetting::Text(text) => DumpValue::String(text.clone()),
    }
}

fn add_box(input: &mut Input, id: &str, shape: &str, role: TextRole, text: &str) {
    input.boxes.push(InputBox {
        icon: false,
        id: id.into(),
        role: BoxRole::Node,
        shape: shape.into(),
        parent: String::new(),
        exclusive: true,
        text: text.into(),
        direction: String::new(),
    });
    if text != id {
        input.labels.push(InputLabel {
            id: format!("{id}.label"),
            owner: id.into(),
            role,
            text: text.into(),
        });
    }
}

fn add_bit_labels(input: &mut Input, owner: &str, piece: &mp::Piece, descending: bool) {
    let (mut lead, mut trail) = (piece.start, piece.end);
    if descending {
        (lead, trail) = (trail, lead);
    }
    let mut bit = |suffix: &str, value: i64| {
        input.labels.push(InputLabel {
            id: format!("{owner}.{suffix}"),
            owner: owner.into(),
            role: TextRole::Body,
            text: value.to_string(),
        });
    };
    if piece.end == piece.start {
        bit("bit", lead);
        return;
    }
    bit("lead", lead);
    bit("trail", trail);
}

fn is_bit_label(id: &str) -> bool {
    id.ends_with(".bit") || id.ends_with(".lead") || id.ends_with(".trail")
}

fn lookup(profile: Profile, name: &str) -> Result<i32, LayoutError> {
    let key = format!("{}.{name}", profile.as_str());
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}

fn measure_role(role: TextRole) -> Role {
    match role {
        TextRole::Title => Role::Title,
        TextRole::Body => Role::Body,
        TextRole::Label => Role::Label,
    }
}

const ZERO_SIZE: Size = Size { w: 0, h: 0 };

const NONE: Rect = Rect {
    x: 0,
    y: 0,
    w: 0,
    h: 0,
};

#[derive(Debug, Clone)]
struct Text {
    texts: Vec<String>,
    runs: Vec<Vec<Run>>,
    size: Size,
}

#[derive(Debug, Clone)]
struct Bit {
    owner: usize,
    trail: bool,
    text: Text,
}

#[derive(Debug, Clone)]
struct Slot {
    title: bool,
    piece: usize,
    start: i64,
    end: i64,
    text: Text,
    lead: Option<usize>,
    trail: Option<usize>,
}

impl Slot {
    fn at(start: i64, end: i64) -> Self {
        Self {
            title: false,
            piece: 0,
            start,
            end,
            text: Text {
                texts: Vec::new(),
                runs: Vec::new(),
                size: ZERO_SIZE,
            },
            lead: None,
            trail: None,
        }
    }
}

struct Placed {
    boxes: Vec<Rect>,
    bits: Vec<Rect>,
}

struct Plan<'a> {
    input: &'a Input,
    profile: Profile,
    params: PacketParams,
    slots: Vec<Slot>,
    bits: Vec<Option<Bit>>,
    owner: BTreeMap<&'a str, usize>,
}

pub(crate) fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let plan = Plan::new(input)?;
    let result = engine::packet(&plan.grid_input(), plan.params)?;
    let placed = plan.placed(&result);
    let dump = plan.dump(&placed);
    let groups = plan.groups(&placed);
    Ok((Scene::new(result.canvas, dump, groups), false))
}

impl<'a> Plan<'a> {
    fn new(input: &'a Input) -> Result<Self, LayoutError> {
        let mut plan = Plan {
            input,
            profile: input.profile,
            params: PacketParams {
                bits_per_row: 0,
                bit_width: 0,
                row_height: 0,
                padding_x: 0,
                padding_y: 0,
                show_bits_pad: 0,
                margin_x: 0,
                line_height: 0,
                show_bits: true,
                descending: false,
            },
            slots: Vec::new(),
            bits: vec![None; input.labels.len()],
            owner: BTreeMap::new(),
        };
        plan.constants()?;
        plan.decode_boxes()?;
        plan.decode_labels()?;
        Ok(plan)
    }

    fn line_height(&self, role: TextRole) -> i32 {
        if self.profile == Profile::Cell {
            return 1;
        }
        measure_role(role).line_height_px() * UNITS_PER_PX
    }

    fn constants(&mut self) -> Result<(), LayoutError> {
        let profile = self.profile;
        self.params.bits_per_row = lookup(profile, "packet.bits_per_row")?;
        self.params.bit_width = lookup(profile, "packet.bit_width")?;
        self.params.row_height = lookup(profile, "packet.row_height")?;
        self.params.padding_x = lookup(profile, "packet.padding_x")?;
        self.params.padding_y = lookup(profile, "packet.padding_y")?;
        self.params.show_bits_pad = lookup(profile, "packet.show_bits_pad")?;
        self.params.margin_x = lookup(profile, "packet.margin_x")?;
        self.params.line_height = lookup(profile, "line_h")?;
        for (key, value) in &self.input.options.config {
            self.apply_entry(key, value)?;
        }
        Ok(())
    }

    fn apply_entry(&mut self, key: &str, value: &DumpValue) -> Result<(), LayoutError> {
        match key {
            "showBits" => self.params.show_bits = matches!(value, DumpValue::Bool(true)),
            "bitOrder" => {
                self.params.descending =
                    matches!(value, DumpValue::String(text) if text == "descending");
            }
            "bitsPerRow" => self.params.bits_per_row = count(value)?,
            _ => return self.apply_size(key, value),
        }
        Ok(())
    }

    fn apply_size(&mut self, key: &str, value: &DumpValue) -> Result<(), LayoutError> {
        if self.profile != Profile::Vector {
            return Ok(());
        }
        let into = match key {
            "rowHeight" => &mut self.params.row_height,
            "bitWidth" => &mut self.params.bit_width,
            "paddingX" => &mut self.params.padding_x,
            "paddingY" => &mut self.params.padding_y,
            _ => return Ok(()),
        };
        let DumpValue::Integer(px) = value else {
            return Err(GeomError::Overflow);
        };
        let units = px
            .checked_mul(i64::from(UNITS_PER_PX))
            .filter(|units| *px >= 0 && *units <= geom::COORD_LIMIT)
            .ok_or(GeomError::Overflow)?;
        *into = i32::try_from(units).map_err(|_| GeomError::Overflow)?;
        Ok(())
    }

    fn decode_boxes(&mut self) -> Result<(), LayoutError> {
        let mut pieces = 0usize;
        let mut next = 0i64;
        for (i, candidate) in self.input.boxes.iter().enumerate() {
            let mut slot = decode_box(candidate, next)?;
            if !slot.title {
                slot.piece = pieces;
                pieces += 1;
                next = slot.end + 1;
            }
            self.owner.insert(candidate.id.as_str(), i);
            self.slots.push(slot);
        }
        Ok(())
    }

    fn measure_text(&self, text: &str, role: TextRole) -> Result<Text, LayoutError> {
        let metric = if self.profile == Profile::Vector {
            Metric::for_role(measure_role(role))
        } else {
            Metric::cell()
        };
        let metric = crate::scene::configured_metric(metric, &self.input.options.config);
        let lines =
            measure::styled_lines(text, i32::MAX, metric).map_err(|_| GeomError::Overflow)?;
        let height = i64::try_from(lines.len()).map_err(|_| GeomError::Overflow)?
            * i64::from(self.line_height(role));
        if height > geom::COORD_LIMIT {
            return Err(GeomError::Overflow);
        }
        Ok(Text::of(&lines, height))
    }

    fn slot_role(&self, index: usize) -> TextRole {
        if self.slots.get(index).is_some_and(|slot| slot.title) {
            TextRole::Title
        } else {
            TextRole::Label
        }
    }

    fn decode_labels(&mut self) -> Result<(), LayoutError> {
        let mut labelled = vec![false; self.slots.len()];
        for (j, label) in self.input.labels.iter().enumerate() {
            let owner = *self
                .owner
                .get(label.owner.as_str())
                .ok_or(GeomError::Domain)?;
            if label.id == format!("{}.label", label.owner) {
                let text = self.measure_text(&label.text, self.slot_role(owner))?;
                if let Some(slot) = self.slots.get_mut(owner) {
                    slot.text = text;
                }
                if let Some(flag) = labelled.get_mut(owner) {
                    *flag = true;
                }
            } else if is_bit_label(&label.id) && self.slot_role(owner) != TextRole::Title {
                self.attach_bit(owner, j, label)?;
            } else {
                return Err(GeomError::Domain);
            }
        }
        self.measure_unlabelled(&labelled)
    }

    fn attach_bit(
        &mut self,
        owner: usize,
        j: usize,
        label: &InputLabel,
    ) -> Result<(), LayoutError> {
        let text = self.measure_text(&label.text, TextRole::Body)?;
        let trail = label.id.ends_with(".trail");
        if let Some(entry) = self.bits.get_mut(j) {
            *entry = Some(Bit { owner, trail, text });
        }
        if let Some(slot) = self.slots.get_mut(owner) {
            if trail {
                slot.trail = Some(j);
            } else {
                slot.lead = Some(j);
            }
        }
        Ok(())
    }

    fn measure_unlabelled(&mut self, labelled: &[bool]) -> Result<(), LayoutError> {
        for (i, candidate) in self.input.boxes.iter().enumerate() {
            if labelled.get(i).copied().unwrap_or(false) {
                continue;
            }
            let text = self.measure_text(box_text(candidate), self.slot_role(i))?;
            if let Some(slot) = self.slots.get_mut(i) {
                slot.text = text;
            }
        }
        Ok(())
    }

    fn grid_input(&self) -> PacketInput {
        let mut input = PacketInput::default();
        for slot in &self.slots {
            if slot.title {
                input.has_title = true;
                continue;
            }
            let size_of = |at: Option<usize>| {
                at.and_then(|j| self.bits.get(j).and_then(Option::as_ref))
                    .map_or(ZERO_SIZE, |bit| bit.text.size)
            };
            input.pieces.push(engine::PacketPiece {
                start: slot.start,
                end: slot.end,
                lead: size_of(slot.lead),
                trail: size_of(slot.trail),
            });
        }
        input
    }

    fn placed(&self, result: &PacketLayout) -> Placed {
        let none = Rect {
            x: 0,
            y: 0,
            w: 0,
            h: 0,
        };
        let boxes = self
            .slots
            .iter()
            .map(|slot| {
                if slot.title {
                    result.title
                } else {
                    result.rects.get(slot.piece).copied().unwrap_or(none)
                }
            })
            .collect();
        let bits = self
            .bits
            .iter()
            .map(|entry| {
                let Some(bit) = entry else {
                    return none;
                };
                let piece = self.slots.get(bit.owner).map_or(0, |slot| slot.piece);
                let side = if bit.trail {
                    &result.trail
                } else {
                    &result.lead
                };
                side.get(piece).copied().unwrap_or(none)
            })
            .collect();
        Placed { boxes, bits }
    }

    fn dump(&self, placed: &Placed) -> Dump {
        let mut options = self.input.options.clone();
        options.profile = self.profile;
        options.direction = self.input.direction;
        let mut dump = Dump::new(KIND, options);
        for (candidate, rect) in self.input.boxes.iter().zip(&placed.boxes) {
            dump.boxes.push(SceneBox {
                id: candidate.id.clone(),
                role: candidate.role,
                rect: *rect,
                parent: candidate.parent.clone(),
                exclusive: candidate.exclusive,
            });
        }
        for (j, label) in self.input.labels.iter().enumerate() {
            let Some(bit) = self.bits.get(j).and_then(Option::as_ref) else {
                continue;
            };
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect: placed.bits.get(j).copied().unwrap_or(NONE),
                lines: bit.text.texts.clone(),
            });
        }
        dump
    }

    fn groups(&self, placed: &Placed) -> Vec<SceneGroup> {
        self.input
            .boxes
            .iter()
            .enumerate()
            .map(|(i, candidate)| SceneGroup {
                role: GroupRole::Node,
                owner: candidate.id.clone(),
                items: self.items(i, placed),
            })
            .collect()
    }

    fn items(&self, index: usize, placed: &Placed) -> Vec<Item> {
        let (Some(slot), Some(rect)) = (self.slots.get(index), placed.boxes.get(index).copied())
        else {
            return Vec::new();
        };
        if slot.title {
            return caption(slot, rect, TextRole::Title);
        }
        let mut items = Vec::new();
        if rect.w > 0 {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Node),
                rect,
            }));
        }
        items.extend(caption(slot, rect, TextRole::Label));
        let lead_align = if slot.start == slot.end {
            Align::Middle
        } else {
            Align::Start
        };
        for (at, align) in [(slot.lead, lead_align), (slot.trail, Align::End)] {
            let Some(j) = at else {
                continue;
            };
            let bit = self.bits.get(j).and_then(Option::as_ref);
            let rect = placed.bits.get(j).copied();
            if let (Some(bit), Some(rect)) = (bit, rect) {
                items.push(text_item(
                    rect,
                    TextRole::Body,
                    &bit.text,
                    align,
                    TextStyle::TextMuted,
                ));
            }
        }
        items
    }
}

impl Text {
    fn of(lines: &[StyledLine<'_>], height: i64) -> Self {
        let width = lines.iter().map(|line| line.width).max().unwrap_or(0);
        Self {
            texts: lines.iter().map(|line| line.text.clone()).collect(),
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
            size: Size {
                w: width,
                h: i32::try_from(height).unwrap_or(i32::MAX),
            },
        }
    }
}

fn count(value: &DumpValue) -> Result<i32, LayoutError> {
    let DumpValue::Integer(n) = value else {
        return Err(GeomError::Overflow);
    };
    i32::try_from(*n)
        .ok()
        .filter(|n| *n >= 1)
        .ok_or(GeomError::Overflow)
}

fn decode_box(candidate: &InputBox, next: i64) -> Result<Slot, LayoutError> {
    if candidate.role != BoxRole::Node {
        return Err(GeomError::Domain);
    }
    if candidate.shape == TITLE_SHAPE {
        return Ok(Slot {
            title: true,
            ..Slot::at(0, 0)
        });
    }
    if candidate.shape.is_empty() {
        return Ok(Slot::at(next, next));
    }
    let fields: Vec<&str> = candidate.shape.split(';').collect();
    let [kind, start, end] = fields.as_slice() else {
        return Err(GeomError::Domain);
    };
    let bounds = (
        start
            .strip_prefix("start=")
            .and_then(|v| v.parse::<i64>().ok()),
        end.strip_prefix("end=").and_then(|v| v.parse::<i64>().ok()),
    );
    match bounds {
        (Some(first), Some(last)) if *kind == FIELD_SHAPE => Ok(Slot::at(first, last)),
        _ => Err(GeomError::Domain),
    }
}

fn box_text(candidate: &InputBox) -> &str {
    if candidate.text.is_empty() {
        &candidate.id
    } else {
        &candidate.text
    }
}

fn caption(slot: &Slot, rect: Rect, role: TextRole) -> Vec<Item> {
    if slot.text.texts.is_empty() {
        return Vec::new();
    }
    let text_box = Rect {
        x: rect.x,
        y: rect.y + ((rect.h - slot.text.size.h) >> 1),
        w: rect.w,
        h: slot.text.size.h,
    };
    vec![text_item(
        text_box,
        role,
        &slot.text,
        Align::Middle,
        TextStyle::Text,
    )]
}

fn text_item(rect: Rect, role: TextRole, text: &Text, align: Align, style: TextStyle) -> Item {
    Item::Text(TextItem {
        rect,
        role,
        size: measure_role(role).size_px(),
        align,
        style,
        series: 0,
        lines: text.runs.clone(),
    })
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]
mod tests;
