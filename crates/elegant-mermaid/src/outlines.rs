//! Glyph outlines for text drawn as paths.
//!
//! [`GlyphOutlines`] holds, for each of the two Inter weights, the units per em
//! and the unhinted outline of every codepoint of the advance tables, in font
//! units with y up. [`text_commands`] places those outlines for one text item in
//! scene units with integer arithmetic only, so the SVG and raster back ends draw
//! the same contours. A codepoint without an outline draws nothing and keeps its
//! measured advance.

use crate::{
    geom::{GeomError, floor_div},
    measure::{Weight, advance_units, ceil_div, round_half_up},
    scene::{Align, Run, TextItem, TextRole},
};
use std::{collections::BTreeMap, fmt, sync::Arc};

const LINE_HEIGHT: i64 = 1280;
const TITLE_LINE_HEIGHT: i64 = 1536;
const UNITS_PER_PX: i64 = 64;
const SHEAR_NUMERATOR: i64 = 13;
const SHEAR_DENOMINATOR: i64 = 64;
const BASELINE_PERCENT: i64 = 35;

/// One outline command: font units with y up before placement, scene units with
/// y down after it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    not(any(feature = "png", test)),
    expect(dead_code, reason = "outlines are only loaded by the png feature")
)]
pub(crate) enum Command {
    Move(i32, i32),
    Line(i32, i32),
    Quad(i32, i32, i32, i32),
    Close,
}

pub(crate) type Contours = BTreeMap<u32, Vec<Command>>;

struct Font {
    upem: i64,
    glyphs: Contours,
}

/// Unhinted glyph outlines of the regular and semibold weights.
///
/// The value is cheap to clone. `raster::inter_outlines` builds it from the
/// embedded Inter fonts; an SVG renderer asked for text paths needs one.
#[derive(Clone)]
pub struct GlyphOutlines {
    fonts: Arc<[Font; 2]>,
}

impl fmt::Debug for GlyphOutlines {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GlyphOutlines")
            .field("regular_glyphs", &self.font(Weight::Regular).glyphs.len())
            .field("semibold_glyphs", &self.font(Weight::Semibold).glyphs.len())
            .finish_non_exhaustive()
    }
}

impl GlyphOutlines {
    #[cfg(any(feature = "png", test))]
    pub(crate) fn new(fonts: [(i64, Contours); 2]) -> GlyphOutlines {
        GlyphOutlines {
            fonts: Arc::new(fonts.map(|(upem, glyphs)| Font { upem, glyphs })),
        }
    }

    #[cfg(test)]
    pub(crate) fn has_outline(&self, weight: Weight, cp: u32) -> bool {
        self.font(weight).glyphs.contains_key(&cp)
    }

    fn font(&self, weight: Weight) -> &Font {
        match weight {
            Weight::Regular => &self.fonts[0],
            Weight::Semibold => &self.fonts[1],
        }
    }
}

/// The weight that draws a run: bold runs are semibold, italic runs are regular,
/// and other runs take the weight of their role.
pub(crate) fn run_weight(t: &TextItem, run: &Run) -> Weight {
    if run.bold || (!run.italic && t.role != TextRole::Body) {
        Weight::Semibold
    } else {
        Weight::Regular
    }
}

fn add(a: i64, b: i64) -> Result<i64, GeomError> {
    a.checked_add(b).ok_or(GeomError::Overflow)
}

fn scaled_numerator(units: i64, size: i32) -> Result<i64, GeomError> {
    units
        .checked_mul(i64::from(size))
        .and_then(|value| value.checked_mul(UNITS_PER_PX))
        .ok_or(GeomError::Overflow)
}

fn scaled(units: i64, size: i32, upem: i64) -> Result<i64, GeomError> {
    Ok(round_half_up(scaled_numerator(units, size)?, upem))
}

fn narrow(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

fn run_units(run: &Run, weight: Weight) -> Result<i64, GeomError> {
    run.text
        .chars()
        .try_fold(0, |sum, c| add(sum, advance_units(weight, u32::from(c))))
}

fn line_width(outlines: &GlyphOutlines, t: &TextItem, line: &[Run]) -> Result<i64, GeomError> {
    let mut total = 0;
    for run in line {
        let weight = run_weight(t, run);
        let units = run_units(run, weight)?;
        total = add(
            total,
            ceil_div(scaled_numerator(units, t.size)?, outlines.font(weight).upem),
        )?;
    }
    Ok(total)
}

struct RunPlacement<'a> {
    font: &'a Font,
    weight: Weight,
    size: i32,
    italic: bool,
    baseline: i64,
}

impl RunPlacement<'_> {
    fn point(&self, origin: i64, gx: i32, gy: i32) -> Result<(i32, i32), GeomError> {
        let height = scaled(i64::from(gy), self.size, self.font.upem)?;
        let shear = if self.italic {
            floor_div(SHEAR_NUMERATOR * height, SHEAR_DENOMINATOR)
        } else {
            0
        };
        let offset = scaled(i64::from(gx), self.size, self.font.upem)?;
        Ok((
            narrow(add(add(origin, offset)?, shear)?)?,
            narrow(self.baseline - height)?,
        ))
    }

    fn command(&self, origin: i64, command: Command) -> Result<Command, GeomError> {
        Ok(match command {
            Command::Move(x, y) => {
                let (x, y) = self.point(origin, x, y)?;
                Command::Move(x, y)
            }
            Command::Line(x, y) => {
                let (x, y) = self.point(origin, x, y)?;
                Command::Line(x, y)
            }
            Command::Quad(cx, cy, x, y) => {
                let (cx, cy) = self.point(origin, cx, cy)?;
                let (x, y) = self.point(origin, x, y)?;
                Command::Quad(cx, cy, x, y)
            }
            Command::Close => Command::Close,
        })
    }

    fn draw(&self, out: &mut Vec<Command>, run: &Run, start: i64) -> Result<i64, GeomError> {
        let mut prefix = 0;
        for c in run.text.chars() {
            let cp = u32::from(c);
            let origin = add(start, scaled(prefix, self.size, self.font.upem)?)?;
            for &command in self.font.glyphs.get(&cp).map_or(&[][..], Vec::as_slice) {
                out.push(self.command(origin, command)?);
            }
            prefix = add(prefix, advance_units(self.weight, cp))?;
        }
        add(start, scaled(prefix, self.size, self.font.upem)?)
    }
}

fn line_start(t: &TextItem, width: i64) -> Result<i64, GeomError> {
    add(
        i64::from(t.rect.x),
        match t.align {
            Align::Start => 0,
            Align::Middle => i64::from(t.rect.w).div_euclid(2) - width.div_euclid(2),
            Align::End => i64::from(t.rect.w) - width,
        },
    )
}

fn baseline_y(t: &TextItem, row: usize) -> Result<i64, GeomError> {
    let line_height = if t.role == TextRole::Title {
        TITLE_LINE_HEIGHT
    } else {
        LINE_HEIGHT
    };
    let top = i64::try_from(row)
        .ok()
        .and_then(|row| row.checked_mul(line_height))
        .ok_or(GeomError::Overflow)?;
    add(
        add(i64::from(t.rect.y), top)?,
        line_height / 2 + floor_div(i64::from(t.size) * UNITS_PER_PX * BASELINE_PERCENT, 100),
    )
}

/// The outline commands of every line of `t`, in scene units.
///
/// A line starts at the box edge its alignment names, less its measured width for
/// middle and end alignment. Glyph `i` of a run has its origin at
/// `x0 + round_half_up(prefix_i * size * 64, upem)` and its baseline on the text
/// baseline of the SVG text rule. A glyph point at height `h` above the baseline
/// moves right by `floor_div(13 * h, 64)` in an italic run.
pub(crate) fn text_commands(
    outlines: &GlyphOutlines,
    t: &TextItem,
) -> Result<Vec<Command>, GeomError> {
    let mut out = Vec::new();
    for (row, line) in t.lines.iter().enumerate() {
        let baseline = baseline_y(t, row)?;
        let mut x = line_start(t, line_width(outlines, t, line)?)?;
        for run in line {
            let weight = run_weight(t, run);
            let placement = RunPlacement {
                font: outlines.font(weight),
                weight,
                size: t.size,
                italic: run.italic,
                baseline,
            };
            x = placement.draw(&mut out, run, x)?;
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests;
