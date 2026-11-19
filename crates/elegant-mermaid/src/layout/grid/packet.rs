//! The packet engine of the grid family (`spec/layout/grid.md`, Packet): fields are
//! placed on a bit grid, one row per `bits_per_row` bits, and every field carries its
//! bit numbers in the band above it.

use super::{product, to_i32, within};
use crate::geom::{self, GeomError, Rect, Size};

#[derive(Debug, Clone, Copy)]
pub(crate) struct PacketPiece {
    pub start: i64,
    pub end: i64,
    pub lead: Size,
    pub trail: Size,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct PacketInput {
    pub pieces: Vec<PacketPiece>,
    pub has_title: bool,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct PacketParams {
    pub bits_per_row: i32,
    pub bit_width: i32,
    pub row_height: i32,
    pub padding_x: i32,
    pub padding_y: i32,
    pub show_bits_pad: i32,
    pub margin_x: i32,
    pub line_height: i32,
    pub show_bits: bool,
    pub descending: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PacketLayout {
    pub rects: Vec<Rect>,
    pub lead: Vec<Rect>,
    pub trail: Vec<Rect>,
    pub title: Rect,
    pub canvas: Size,
    pub rows: usize,
}

const NONE: Rect = Rect {
    x: 0,
    y: 0,
    w: 0,
    h: 0,
};

struct Plan {
    params: PacketParams,
    has_title: bool,
    pad_y: i64,
    pitch: i64,
    bits: i64,
    label_h: i64,
    max_rows: i64,
    width: i64,
    out: PacketLayout,
}

impl PacketParams {
    fn valid(&self) -> bool {
        let positive = self.bits_per_row >= 1 && self.bit_width >= 1 && self.row_height >= 1;
        positive
            && self.padding_x >= 0
            && self.padding_y >= 0
            && self.show_bits_pad >= 0
            && self.margin_x >= 0
            && self.line_height >= 0
    }
}

impl PacketPiece {
    fn valid(&self) -> bool {
        let sizes = self.lead.w >= 0 && self.lead.h >= 0 && self.trail.w >= 0 && self.trail.h >= 0;
        sizes && self.start >= 0 && self.end >= self.start
    }
}

pub(crate) fn packet(input: &PacketInput, params: PacketParams) -> Result<PacketLayout, GeomError> {
    if !params.valid() {
        return Err(GeomError::Domain);
    }
    let show_pad = if params.show_bits {
        i64::from(params.show_bits_pad)
    } else {
        0
    };
    let pad_y = i64::from(params.padding_y) + show_pad;
    let bits = i64::from(params.bits_per_row);
    let width = within(bits * i64::from(params.bit_width) + 2 * i64::from(params.margin_x))?;
    let count = input.pieces.len();
    let mut plan = Plan {
        params,
        has_title: input.has_title,
        pad_y,
        pitch: i64::from(params.row_height) + pad_y,
        bits,
        label_h: i64::from(params.line_height).min(pad_y),
        max_rows: 0,
        width,
        out: PacketLayout {
            rects: vec![NONE; count],
            lead: vec![NONE; count],
            trail: vec![NONE; count],
            title: NONE,
            canvas: Size { w: 0, h: 0 },
            rows: 0,
        },
    };
    for (i, piece) in input.pieces.iter().enumerate() {
        plan.place(i, piece)?;
    }
    plan.close()
}

impl Plan {
    fn locate(&self, piece: &PacketPiece) -> Result<(i64, i64, i64), GeomError> {
        if !piece.valid() {
            return Err(GeomError::Domain);
        }
        let n = piece.end - piece.start + 1;
        let row = geom::floor_div(piece.start, self.bits);
        let mut column = piece.start - row * self.bits;
        if column + n > self.bits {
            return Err(GeomError::Domain);
        }
        if self.params.descending {
            column = self.bits - column - n;
        }
        Ok((row, column, n))
    }

    fn place(&mut self, i: usize, piece: &PacketPiece) -> Result<(), GeomError> {
        let (row, column, n) = self.locate(piece)?;
        let offset = product(row, self.pitch)?;
        let y = within(offset + self.pad_y)?;
        let bit_width = i64::from(self.params.bit_width);
        let x = column * bit_width + i64::from(self.params.margin_x);
        let w = (n * bit_width - i64::from(self.params.padding_x)).max(0);
        self.max_rows = self.max_rows.max(row + 1);
        if let Some(slot) = self.out.rects.get_mut(i) {
            *slot = Rect {
                x: to_i32(x),
                y: to_i32(y),
                w: to_i32(w),
                h: self.params.row_height,
            };
        }
        if self.params.show_bits {
            self.bit_labels(i, n, (x, y, w), piece);
        }
        Ok(())
    }

    fn bit_labels(&mut self, i: usize, n: i64, at: (i64, i64, i64), piece: &PacketPiece) {
        let (x, y, w) = at;
        let top = to_i32(y - self.label_h);
        let h = to_i32(self.label_h);
        let lead = i64::from(piece.lead.w);
        if n == 1 {
            if let Some(slot) = self.out.lead.get_mut(i) {
                *slot = Rect {
                    x: to_i32((x + w / 2 - lead / 2).max(0)),
                    y: top,
                    w: piece.lead.w,
                    h,
                };
            }
            return;
        }
        let trail = i64::from(piece.trail.w);
        if let Some(slot) = self.out.lead.get_mut(i) {
            *slot = Rect {
                x: to_i32(x),
                y: top,
                w: piece.lead.w,
                h,
            };
        }
        if let Some(slot) = self.out.trail.get_mut(i) {
            *slot = Rect {
                x: to_i32((x + w - trail).max(0)),
                y: top,
                w: piece.trail.w,
                h,
            };
        }
    }

    fn close(mut self) -> Result<PacketLayout, GeomError> {
        let offset = product(self.max_rows, self.pitch)?;
        let title_height = if self.has_title {
            i64::from(self.params.row_height)
        } else {
            0
        };
        let height = within(offset + self.pad_y + title_height)?;
        if self.has_title {
            self.out.title = Rect {
                x: self.params.margin_x,
                y: to_i32(height) - self.params.row_height,
                w: to_i32(self.bits * i64::from(self.params.bit_width)),
                h: self.params.row_height,
            };
        }
        self.out.canvas = Size {
            w: to_i32(self.width),
            h: to_i32(height),
        };
        self.out.rows = usize::try_from(self.max_rows).unwrap_or(0);
        Ok(self.out)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests;
