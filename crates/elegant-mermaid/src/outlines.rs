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

pub(crate) mod fallback;

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
    noto: fallback::NotoFonts,
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
    #[cfg(test)]
    pub(crate) fn new(fonts: [(i64, Contours); 2]) -> GlyphOutlines {
        GlyphOutlines {
            fonts: Arc::new(fonts.map(|(upem, glyphs)| Font { upem, glyphs })),
            noto: fallback::NotoFonts::empty(),
        }
    }
    #[cfg(feature = "png")]
    pub(crate) fn with_fallback(
        fonts: [(i64, Contours); 2],
        noto: fallback::NotoFonts,
    ) -> GlyphOutlines {
        GlyphOutlines {
            fonts: Arc::new(fonts.map(|(upem, glyphs)| Font { upem, glyphs })),
            noto,
        }
    }
    pub(crate) fn noto(&self) -> &fallback::NotoFonts {
        &self.noto
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
            let ctx = RunContext::for_run(
                outlines,
                run_weight(t, run),
                t.size,
                run.italic,
                baseline,
                x,
            );
            x = draw_run(&mut out, run, &ctx)?;
        }
    }
    Ok(out)
}

struct RunContext<'a> {
    inter: &'a Font,
    noto: &'a fallback::NotoFonts,
    placement: RunPlacement<'a>,
    weight: Weight,
    size: i32,
    italic: bool,
    baseline: i64,
    start: i64,
}

impl<'a> RunContext<'a> {
    fn for_run(
        outlines: &'a GlyphOutlines,
        weight: Weight,
        size: i32,
        italic: bool,
        baseline: i64,
        start: i64,
    ) -> Self {
        let inter = outlines.font(weight);
        Self {
            inter,
            noto: outlines.noto(),
            placement: RunPlacement {
                font: inter,
                size,
                italic,
                baseline,
            },
            weight,
            size,
            italic,
            baseline,
            start,
        }
    }
}

enum GlyphPlan<'a> {
    Slot {
        width: usize,
        loaded: fallback::LoadedGlyph,
    },
    Centered {
        commands: &'a Vec<Command>,
    },
    Direct {
        commands: &'a Vec<Command>,
    },
    Skip,
}

fn origin(ctx: &RunContext<'_>, prefix: &[i64], i: usize) -> Result<i64, GeomError> {
    add(ctx.start, scaled(prefix[i], ctx.size, ctx.inter.upem)?)
}

fn slot_span(
    ctx: &RunContext<'_>,
    prefix: &[i64],
    i: usize,
    width: usize,
    x0: i64,
) -> Result<i64, GeomError> {
    let x1 = add(
        ctx.start,
        scaled(prefix[i + width], ctx.size, ctx.inter.upem)?,
    )?;
    x1.checked_sub(x0).ok_or(GeomError::Overflow)
}

fn sequence_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    let (width, glyph) = fallback::longest_sequence(&scalars[i..])?;
    let loaded = fallback::load_emoji_glyph(ctx.noto.emoji, glyph)?;
    Some(GlyphPlan::Slot { width, loaded })
}

fn vs16_emoji_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    if i + 1 >= scalars.len() || scalars[i + 1] != 0xFE0F {
        return None;
    }
    let loaded = fallback::load_codepoint(ctx.noto.emoji, scalars[i])?;
    Some(GlyphPlan::Slot { width: 2, loaded })
}

fn vs16_inter_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    if i + 1 >= scalars.len() || scalars[i + 1] != 0xFE0F {
        return None;
    }
    let commands = ctx.inter.glyphs.get(&scalars[i])?;
    Some(GlyphPlan::Centered { commands })
}

fn inter_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    let commands = ctx.inter.glyphs.get(&scalars[i])?;
    Some(GlyphPlan::Direct { commands })
}

fn presentation_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    if !fallback::has_presentation(scalars[i]) {
        return None;
    }
    let loaded = fallback::load_codepoint(ctx.noto.emoji, scalars[i])?;
    Some(GlyphPlan::Slot { width: 1, loaded })
}

fn candidate_plan<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> Option<GlyphPlan<'a>> {
    for (_, data) in fallback::candidates(ctx.noto, ctx.weight) {
        if let Some(loaded) = fallback::load_codepoint(data, scalars[i]) {
            return Some(GlyphPlan::Slot { width: 1, loaded });
        }
    }
    None
}

fn plan_glyph<'a>(ctx: &RunContext<'a>, scalars: &[u32], i: usize) -> GlyphPlan<'a> {
    if let Some(plan) = sequence_plan(ctx, scalars, i) {
        return plan;
    }
    if let Some(plan) = vs16_emoji_plan(ctx, scalars, i) {
        return plan;
    }
    if let Some(plan) = vs16_inter_plan(ctx, scalars, i) {
        return plan;
    }
    if let Some(plan) = inter_plan(ctx, scalars, i) {
        return plan;
    }
    if let Some(plan) = presentation_plan(ctx, scalars, i) {
        return plan;
    }
    if let Some(plan) = candidate_plan(ctx, scalars, i) {
        return plan;
    }
    GlyphPlan::Skip
}

fn place_glyph(
    out: &mut Vec<Command>,
    ctx: &RunContext<'_>,
    scalars: &[u32],
    prefix: &[i64],
    i: usize,
) -> Result<usize, GeomError> {
    match plan_glyph(ctx, scalars, i) {
        GlyphPlan::Slot { width, loaded } => {
            let x0 = origin(ctx, prefix, i)?;
            let slot = slot_span(ctx, prefix, i, width, x0)?;
            fallback::place_into(out, &loaded, ctx.size, x0, slot, ctx.baseline, ctx.italic)?;
            Ok(width)
        }
        GlyphPlan::Centered { commands } => {
            let x0 = origin(ctx, prefix, i)?;
            let slot = slot_span(ctx, prefix, i, 2, x0)?;
            let natural = scaled(
                advance_units(ctx.weight, scalars[i]),
                ctx.size,
                ctx.inter.upem,
            )?;
            let at = add(
                x0,
                floor_div(slot.checked_sub(natural).ok_or(GeomError::Overflow)?, 2),
            )?;
            for command in commands.iter().copied() {
                out.push(ctx.placement.command(at, command)?);
            }
            Ok(2)
        }
        GlyphPlan::Direct { commands } => {
            let x0 = origin(ctx, prefix, i)?;
            for command in commands.iter().copied() {
                out.push(ctx.placement.command(x0, command)?);
            }
            Ok(1)
        }
        GlyphPlan::Skip => Ok(1),
    }
}

fn draw_run(out: &mut Vec<Command>, run: &Run, ctx: &RunContext<'_>) -> Result<i64, GeomError> {
    let scalars: Vec<u32> = run.text.chars().map(u32::from).collect();
    let count = scalars.len();
    let mut prefix: Vec<i64> = Vec::with_capacity(count + 1);
    prefix.push(0);
    for cp in scalars.iter().copied() {
        let last = prefix[prefix.len() - 1];
        prefix.push(add(last, advance_units(ctx.weight, cp))?);
    }
    let mut i = 0;
    while i < count {
        i += place_glyph(out, ctx, &scalars, &prefix, i)?;
    }
    add(ctx.start, scaled(prefix[count], ctx.size, ctx.inter.upem)?)
}

#[cfg(test)]
mod tests;
