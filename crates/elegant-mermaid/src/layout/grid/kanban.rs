//! The kanban engine of the grid family (`spec/layout/grid.md`, Kanban rules 1 to 5):
//! sections side by side, each with a stack of cards under a header band.

use super::{to_i32, within};
use crate::geom::{GeomError, Rect, Size, floor_div};

#[derive(Debug, Clone, Copy)]
pub(crate) struct KanbanSection {
    pub label_height: i32,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct KanbanCard {
    pub section: usize,
    pub height: i32,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct KanbanInput {
    pub sections: Vec<KanbanSection>,
    pub cards: Vec<KanbanCard>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct KanbanParams {
    pub section_width: i32,
    pub gutter: i32,
    pub section_gap: i32,
    pub card_gap: i32,
    pub padding: i32,
    pub border: i32,
    pub label_band_min: i32,
    pub section_min_height: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct KanbanLayout {
    pub sections: Vec<Rect>,
    pub labels: Vec<Rect>,
    pub cards: Vec<Rect>,
    pub canvas: Size,
}

pub(crate) fn kanban(input: &KanbanInput, params: KanbanParams) -> Result<KanbanLayout, GeomError> {
    validate(input, params)?;
    let band = input
        .sections
        .iter()
        .fold(i64::from(params.label_band_min), |band, section| {
            band.max(i64::from(section.label_height) + i64::from(params.border))
        });
    let card_width = i64::from(params.section_width) - floor_div(3 * i64::from(params.gutter), 2);
    if card_width <= 0 {
        return Err(GeomError::Domain);
    }
    Builder {
        input,
        params,
        band,
        card_width,
    }
    .place()
}

fn validate(input: &KanbanInput, params: KanbanParams) -> Result<(), GeomError> {
    let negative = [
        params.section_width,
        params.gutter,
        params.section_gap,
        params.card_gap,
        params.padding,
        params.border,
        params.label_band_min,
        params.section_min_height,
    ]
    .iter()
    .any(|value| *value < 0);
    let bad_section = input
        .sections
        .iter()
        .any(|section| section.label_height < 0);
    let bad_card = input
        .cards
        .iter()
        .any(|card| card.section >= input.sections.len() || card.height < 0);
    if negative || bad_section || bad_card {
        return Err(GeomError::Domain);
    }
    Ok(())
}

struct Builder<'a> {
    input: &'a KanbanInput,
    params: KanbanParams,
    band: i64,
    card_width: i64,
}

impl Builder<'_> {
    fn place(&self) -> Result<KanbanLayout, GeomError> {
        let count = self.input.sections.len();
        let pad = i64::from(self.params.padding);
        let width = i64::from(self.params.section_width);
        let pitch = width + i64::from(self.params.section_gap);
        let card_gap = i64::from(self.params.card_gap);
        let mut cursor = vec![self.band; count];
        let inset = floor_div(width - self.card_width, 2);
        let mut cards = Vec::with_capacity(self.input.cards.len());
        for card in &self.input.cards {
            let Some(at) = cursor.get_mut(card.section) else {
                return Err(GeomError::Domain);
            };
            let section = i64::try_from(card.section).map_err(|_| GeomError::Overflow)?;
            let x = pad + section * pitch + inset;
            cards.push(rect(x, pad + *at, self.card_width, i64::from(card.height))?);
            *at += i64::from(card.height) + card_gap;
        }
        let mut sections = Vec::with_capacity(count);
        let mut labels = Vec::with_capacity(count);
        let (mut right, mut bottom) = (pad, pad);
        for (index, section) in self.input.sections.iter().enumerate() {
            let at = i64::try_from(index).map_err(|_| GeomError::Overflow)?;
            let x = pad + at * pitch;
            let end = cursor.get(index).copied().unwrap_or(self.band);
            let extent = end - self.band - card_gap + floor_div(i64::from(self.params.gutter), 2);
            let height = (extent + 3 * i64::from(self.params.gutter))
                .max(i64::from(self.params.section_min_height))
                + self.band
                - i64::from(self.params.label_band_min);
            sections.push(rect(x, pad, width, height)?);
            let label_height = i64::from(section.label_height);
            let label_y = pad
                + i64::from(self.params.border)
                + floor_div(self.band - i64::from(self.params.border) - label_height, 2);
            labels.push(rect(x, label_y, width, label_height)?);
            right = right.max(x + width);
            bottom = bottom.max(pad + height);
        }
        Ok(KanbanLayout {
            sections,
            labels,
            cards,
            canvas: Size {
                w: to_i32(within(right + pad)?),
                h: to_i32(within(bottom + pad)?),
            },
        })
    }
}

fn rect(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    let right = within(x + w)?;
    let bottom = within(y + h)?;
    Ok(Rect {
        x: to_i32(x),
        y: to_i32(y),
        w: to_i32(right - x),
        h: to_i32(bottom - y),
    })
}

#[cfg(test)]
mod tests;
