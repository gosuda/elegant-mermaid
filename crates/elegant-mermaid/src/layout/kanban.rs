//! The `kanban` kind: the model-stage input, the measured grid layout, and the drawn
//! scene (`spec/layout/grid.md`, Kanban rules 1 to 5).

mod paint;

use std::collections::BTreeMap;

use super::grid::{self, KanbanCard, KanbanInput, KanbanLayout, KanbanParams, KanbanSection};
use super::input::{Box, Input, Spacing};
use super::layered::LayoutError;
use crate::geom::{COORD_LIMIT, GeomError, Rect, floor_div};
use crate::measure::{Metric, Role, styled_lines};
use crate::model::kanban::{Model, Node};
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Profile, Run, Scene, SceneBox,
};

const KIND: &str = "kanban";
const SECTION_SHAPE: &str = "kanbanSection";
const ITEM_SHAPE: &str = "kanbanItem";
const PADDING_KEY: &str = "padding";
const SECTION_KEY: &str = "sectionWidth";
const BREAK: &str = "<br>";
const CELL_PIXELS_X: i64 = 8;
const VECTOR_PER_PIXEL: i64 = 64;

pub(crate) fn from_kanban(
    model: &Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.config = BTreeMap::new();
    if let Some(value) = model.config.padding {
        options
            .config
            .insert(PADDING_KEY.to_owned(), DumpValue::Integer(value));
    }
    if let Some(value) = model.config.section_width {
        options
            .config
            .insert(SECTION_KEY.to_owned(), DumpValue::Integer(value));
    }
    options.profile = profile;
    options.direction = Direction::Tb;
    let mut boxes = Vec::new();
    for (s, column) in model.columns().iter().enumerate() {
        let id = format!("s{s}");
        let section = model.nodes.get(column.section).ok_or(GeomError::Domain)?;
        boxes.push(Box {
            id: id.clone(),
            role: BoxRole::Group,
            shape: SECTION_SHAPE.to_owned(),
            icon: false,
            parent: String::new(),
            exclusive: false,
            text: trim(&section.label).to_owned(),
            direction: String::new(),
        });
        for (c, index) in column.cards.iter().enumerate() {
            let card = model.nodes.get(*index).ok_or(GeomError::Domain)?;
            boxes.push(Box {
                id: format!("{id}.c{c}"),
                role: BoxRole::Node,
                shape: ITEM_SHAPE.to_owned(),
                icon: false,
                parent: id.clone(),
                exclusive: true,
                text: card_text(card),
                direction: String::new(),
            });
        }
    }
    Ok(Input {
        kind: KIND,
        profile,
        direction: Direction::Tb,
        options,
        boxes,
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    })
}

fn card_text(card: &Node) -> String {
    let mut lines = vec![trim(&card.label).to_owned()];
    if !card.ticket.is_empty() {
        lines.push(format!("ticket: {}", card.ticket));
    }
    if !card.assigned.is_empty() {
        lines.push(format!("assigned: {}", card.assigned));
    }
    if card.has_priority {
        lines.push(format!("priority: {}", card.priority));
    }
    lines.join(BREAK)
}

fn trim(text: &str) -> &str {
    text.trim_matches(|c: char| {
        matches!(
            c,
            '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
                ..='\u{200a}'
                    | '\u{2028}'
                    | '\u{2029}'
                    | '\u{202f}'
                    | '\u{205f}'
                    | '\u{3000}'
                    | '\u{feff}'
        )
    })
}

struct Constants {
    gutter: i32,
    padding: i32,
    section_width: i32,
    band_min: i32,
    card_pad_x: i32,
    card_pad_y: i32,
    card_gap: i32,
    section_min_height: i32,
    border: i32,
    line_height: i32,
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
            gutter: constant(profile, "kanban.gutter")?,
            padding: constant(profile, "kanban.padding")?,
            section_width: constant(profile, "kanban.section_width")?,
            band_min: constant(profile, "kanban.label_band_min")?,
            card_pad_x: constant(profile, "kanban.card_pad_x")?,
            card_pad_y: constant(profile, "kanban.card_pad_y")?,
            card_gap: constant(profile, "kanban.card_gap")?,
            section_min_height: constant(profile, "kanban.section_min_height")?,
            border: constant(profile, "node_border")?,
            line_height: constant(profile, "line_h")?,
            corner: constant(profile, "corner_radius")?,
        };
        constants.apply_config(profile, &input.options.config)?;
        Ok(constants)
    }

    fn apply_config(
        &mut self,
        profile: Profile,
        config: &BTreeMap<String, DumpValue>,
    ) -> Result<(), GeomError> {
        for (key, value) in config {
            let target = match key.as_str() {
                PADDING_KEY => &mut self.padding,
                SECTION_KEY => &mut self.section_width,
                _ => continue,
            };
            let DumpValue::Integer(px) = value else {
                return Err(GeomError::Overflow);
            };
            if *px < 0 || *px > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            let units = match profile {
                Profile::Cell => (*px + CELL_PIXELS_X - 1) / CELL_PIXELS_X,
                Profile::Vector => *px * VECTOR_PER_PIXEL,
            };
            if units > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            *target = i32::try_from(units).map_err(|_| GeomError::Overflow)?;
        }
        Ok(())
    }
}

struct Plan<'a> {
    input: &'a Input,
    c: Constants,
    sections: Vec<usize>,
    cards: Vec<usize>,
    owner: BTreeMap<&'a str, usize>,
    sizes: KanbanInput,
    titles: Vec<Vec<Vec<Run>>>,
    texts: Vec<Vec<Vec<Run>>>,
}

fn metric(profile: Profile) -> Metric {
    match profile {
        Profile::Cell => Metric::Cell,
        Profile::Vector => Metric::for_role(Role::Label),
    }
}

fn is_section(item: &Box) -> bool {
    item.role == BoxRole::Group || item.parent.is_empty()
}

fn box_text<'a>(input: &'a Input, item: &'a Box) -> &'a str {
    input
        .labels
        .iter()
        .find(|label| label.owner == item.id)
        .map_or(item.text.as_str(), |label| label.text.as_str())
}

fn wrapped_runs(profile: Profile, text: &str, wrap: i32) -> Result<Vec<Vec<Run>>, GeomError> {
    let lines =
        styled_lines(text, wrap.max(1), metric(profile)).map_err(|_| GeomError::Overflow)?;
    Ok(lines
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
        .collect())
}

impl<'a> Plan<'a> {
    fn new(input: &'a Input) -> Result<Self, GeomError> {
        let mut plan = Self {
            input,
            c: Constants::load(input)?,
            sections: Vec::new(),
            cards: Vec::new(),
            owner: BTreeMap::new(),
            sizes: KanbanInput::default(),
            titles: Vec::new(),
            texts: Vec::new(),
        };
        for (index, item) in input.boxes.iter().enumerate() {
            if !is_section(item) {
                plan.cards.push(index);
            } else if !item.parent.is_empty() {
                return Err(GeomError::Domain);
            } else {
                plan.owner.insert(item.id.as_str(), plan.sections.len());
                plan.sections.push(index);
            }
        }
        plan.measure()?;
        Ok(plan)
    }

    fn measure(&mut self) -> Result<(), GeomError> {
        self.measure_sections()?;
        self.measure_cards()
    }

    fn measure_sections(&mut self) -> Result<(), GeomError> {
        let input = self.input;
        let wrap = self.c.section_width - 2 * self.c.card_pad_x;
        for &index in &self.sections {
            let item = input.boxes.get(index).ok_or(GeomError::Domain)?;
            let lines = wrapped_runs(input.profile, box_text(input, item), wrap)?;
            let count = to_i32(i64::try_from(lines.len()).map_err(|_| GeomError::Overflow)?)?;
            let label_height = count
                .checked_mul(self.c.line_height)
                .ok_or(GeomError::Overflow)?;
            self.titles.push(lines);
            self.sizes.sections.push(KanbanSection { label_height });
        }
        Ok(())
    }

    fn measure_cards(&mut self) -> Result<(), GeomError> {
        let input = self.input;
        let card_width = self.c.section_width - to_i32(floor_div(3 * i64::from(self.c.gutter), 2))?;
        let wrap = card_width - 2 * self.c.card_pad_x;
        for &index in &self.cards {
            let item = input.boxes.get(index).ok_or(GeomError::Domain)?;
            let section = *self
                .owner
                .get(item.parent.as_str())
                .ok_or(GeomError::Domain)?;
            let lines = wrapped_runs(input.profile, box_text(input, item), wrap)?;
            let count = i64::try_from(lines.len().max(1)).map_err(|_| GeomError::Overflow)?;
            let height = count * i64::from(self.c.line_height)
                + 2 * i64::from(self.c.card_pad_y)
                + 2 * i64::from(self.c.border);
            if height > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            self.texts.push(lines);
            self.sizes.cards.push(KanbanCard {
                section,
                height: to_i32(height)?,
            });
        }
        Ok(())
    }

    fn params(&self) -> KanbanParams {
        KanbanParams {
            section_width: self.c.section_width,
            gutter: self.c.gutter,
            section_gap: self.c.card_gap,
            card_gap: self.c.card_gap,
            padding: self.c.padding,
            border: self.c.border,
            label_band_min: self.c.band_min,
            section_min_height: self.c.section_min_height,
        }
    }

    fn dump(&self, placed: &KanbanLayout) -> Dump {
        let mut rects = vec![
            Rect {
                x: 0,
                y: 0,
                w: 0,
                h: 0,
            };
            self.input.boxes.len()
        ];
        for (rect, index) in placed.sections.iter().zip(&self.sections) {
            if let Some(target) = rects.get_mut(*index) {
                *target = *rect;
            }
        }
        for (rect, index) in placed.cards.iter().zip(&self.cards) {
            if let Some(target) = rects.get_mut(*index) {
                *target = *rect;
            }
        }
        let mut dump = Dump::new(KIND, self.input.options.clone());
        dump.boxes = self
            .input
            .boxes
            .iter()
            .zip(rects)
            .map(|(item, rect)| SceneBox {
                id: item.id.clone(),
                role: item.role,
                rect,
                parent: item.parent.clone(),
                exclusive: item.exclusive,
            })
            .collect();
        dump
    }
}

fn to_i32(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let plan = Plan::new(input)?;
    let placed = grid::kanban(&plan.sizes, plan.params())?;
    let dump = plan.dump(&placed);
    let groups = plan.groups(&placed);
    Ok((Scene::new(placed.canvas, dump, groups), false))
}

#[cfg(test)]
mod tests;
