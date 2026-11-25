use crate::r#gen::emojipresentation::EMOJI_PRESENTATION;
use crate::r#gen::emojiseq::EMOJI_SEQUENCES;
use crate::{
    geom::{GeomError, floor_div},
    measure::{Weight, round_half_up},
    outlines::Command,
};

pub(crate) struct NotoFonts {
    pub(crate) emoji: &'static [u8],
    pub(crate) sans_regular: &'static [u8],
    pub(crate) sans_semibold: &'static [u8],
    pub(crate) symbols_regular: &'static [u8],
    pub(crate) symbols_semibold: &'static [u8],
    pub(crate) symbols2: &'static [u8],
    pub(crate) math: &'static [u8],
    pub(crate) cjk_regular: &'static [u8],
    pub(crate) cjk_semibold: &'static [u8],
    pub(crate) coptic: &'static [u8],
}

impl Clone for NotoFonts {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for NotoFonts {}

impl NotoFonts {
    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self {
            emoji: &[],
            sans_regular: &[],
            sans_semibold: &[],
            symbols_regular: &[],
            symbols_semibold: &[],
            symbols2: &[],
            math: &[],
            cjk_regular: &[],
            cjk_semibold: &[],
            coptic: &[],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FallbackFont {
    Sans,
    Symbols,
    Symbols2,
    Math,
    Cjk,
    Coptic,
}

/// Step (d) text fonts in weight order. Noto Emoji is consulted only for
/// multi-scalar sequences (step a) and Emoji_Presentation/VS16 (step c).
pub(crate) fn candidates(noto: &NotoFonts, weight: Weight) -> [(FallbackFont, &'static [u8]); 6] {
    match weight {
        Weight::Regular => [
            (FallbackFont::Sans, noto.sans_regular),
            (FallbackFont::Symbols, noto.symbols_regular),
            (FallbackFont::Symbols2, noto.symbols2),
            (FallbackFont::Math, noto.math),
            (FallbackFont::Cjk, noto.cjk_regular),
            (FallbackFont::Coptic, noto.coptic),
        ],
        Weight::Semibold => [
            (FallbackFont::Sans, noto.sans_semibold),
            (FallbackFont::Symbols, noto.symbols_semibold),
            (FallbackFont::Symbols2, noto.symbols2),
            (FallbackFont::Math, noto.math),
            (FallbackFont::Cjk, noto.cjk_semibold),
            (FallbackFont::Coptic, noto.coptic),
        ],
    }
}

pub(crate) fn has_presentation(cp: u32) -> bool {
    let index = EMOJI_PRESENTATION.partition_point(|row| row.hi < cp);
    EMOJI_PRESENTATION
        .get(index)
        .is_some_and(|row| row.lo <= cp && row.value != 0)
}

pub(crate) fn sequence_at(prefix: &[u32]) -> Option<u16> {
    if prefix.len() < 2 || prefix[0] == 0xFE0F {
        return None;
    }
    for sequence in EMOJI_SEQUENCES {
        if matches_stripped(sequence.scalars, prefix) {
            return Some(sequence.glyph);
        }
    }
    None
}
fn matches_stripped(entry: &[u32], prefix: &[u32]) -> bool {
    let mut needed = entry.iter();
    let mut current = needed.next();
    for cp in prefix.iter().copied() {
        if cp == 0xFE0F {
            continue;
        }
        if current != Some(&cp) {
            return false;
        }
        current = needed.next();
    }
    current.is_none()
}
pub(crate) fn longest_sequence(scalars: &[u32]) -> Option<(usize, u16)> {
    if scalars.is_empty() || scalars[0] == 0xFE0F {
        return None;
    }
    for k in (2..=scalars.len()).rev() {
        if let Some(glyph) = sequence_at(&scalars[..k]) {
            return Some((k, glyph));
        }
    }
    None
}

pub(crate) struct LoadedGlyph {
    pub(crate) upem: i64,
    pub(crate) advance: i64,
    pub(crate) commands: Vec<Command>,
}

fn checked_mul3(a: i64, b: i64, c: i64) -> Result<i64, GeomError> {
    a.checked_mul(b)
        .and_then(|value| value.checked_mul(c))
        .ok_or(GeomError::Overflow)
}

fn checked_mul4(a: i64, b: i64, c: i64, d: i64) -> Result<i64, GeomError> {
    a.checked_mul(b)
        .and_then(|value| value.checked_mul(c))
        .and_then(|value| value.checked_mul(d))
        .ok_or(GeomError::Overflow)
}

pub(crate) fn natural_scene_units(advance: i64, size: i32, upem: i64) -> Result<i64, GeomError> {
    Ok(round_half_up(
        checked_mul3(advance, i64::from(size), 64)?,
        upem,
    ))
}

fn natural_point(
    origin: i64,
    baseline: i64,
    italic: bool,
    size: i32,
    upem: i64,
    gx: i32,
    gy: i32,
) -> Result<(i32, i32), GeomError> {
    let height = natural_scene_units(i64::from(gy), size, upem)?;
    let shear = if italic {
        floor_div(13i64.checked_mul(height).ok_or(GeomError::Overflow)?, 64)
    } else {
        0
    };
    let offset = natural_scene_units(i64::from(gx), size, upem)?;
    let x = origin
        .checked_add(offset)
        .and_then(|value| value.checked_add(shear))
        .ok_or(GeomError::Overflow)?;
    let y = baseline.checked_sub(height).ok_or(GeomError::Overflow)?;
    Ok((
        i32::try_from(x).map_err(|_| GeomError::Overflow)?,
        i32::try_from(y).map_err(|_| GeomError::Overflow)?,
    ))
}

struct SlotRequest {
    x0: i64,
    slot: i64,
    natural: i64,
    baseline: i64,
    italic: bool,
    size: i32,
    upem: i64,
}

fn scaled_point(fit: &SlotRequest, gx: i32, gy: i32) -> Result<(i32, i32), GeomError> {
    let denominator = fit
        .upem
        .checked_mul(fit.natural)
        .ok_or(GeomError::Overflow)?;
    if denominator <= 0 {
        return Err(GeomError::Overflow);
    }
    let numerator_x = checked_mul4(i64::from(gx), i64::from(fit.size), 64, fit.slot)?;
    let numerator_y = checked_mul4(i64::from(gy), i64::from(fit.size), 64, fit.slot)?;
    let height = round_half_up(numerator_y, denominator);
    let shear = if fit.italic {
        floor_div(13i64.checked_mul(height).ok_or(GeomError::Overflow)?, 64)
    } else {
        0
    };
    let x = fit
        .x0
        .checked_add(round_half_up(numerator_x, denominator))
        .and_then(|value| value.checked_add(shear))
        .ok_or(GeomError::Overflow)?;
    let y = fit
        .baseline
        .checked_sub(height)
        .ok_or(GeomError::Overflow)?;
    Ok((
        i32::try_from(x).map_err(|_| GeomError::Overflow)?,
        i32::try_from(y).map_err(|_| GeomError::Overflow)?,
    ))
}

pub(crate) fn place_into(
    out: &mut Vec<Command>,
    glyph: &LoadedGlyph,
    size: i32,
    x0: i64,
    slot: i64,
    baseline: i64,
    italic: bool,
) -> Result<(), GeomError> {
    let natural = natural_scene_units(glyph.advance, size, glyph.upem)?;
    if natural <= slot {
        let origin = x0
            .checked_add(floor_div(
                slot.checked_sub(natural).ok_or(GeomError::Overflow)?,
                2,
            ))
            .ok_or(GeomError::Overflow)?;
        for command in &glyph.commands {
            out.push(match *command {
                Command::Move(gx, gy) => {
                    let (x, y) = natural_point(origin, baseline, italic, size, glyph.upem, gx, gy)?;
                    Command::Move(x, y)
                }
                Command::Line(gx, gy) => {
                    let (x, y) = natural_point(origin, baseline, italic, size, glyph.upem, gx, gy)?;
                    Command::Line(x, y)
                }
                Command::Quad(cx, cy, gx, gy) => {
                    let (cx, cy) =
                        natural_point(origin, baseline, italic, size, glyph.upem, cx, cy)?;
                    let (x, y) = natural_point(origin, baseline, italic, size, glyph.upem, gx, gy)?;
                    Command::Quad(cx, cy, x, y)
                }
                Command::Close => Command::Close,
            });
        }
    } else {
        let fit = SlotRequest {
            x0,
            slot,
            natural,
            baseline,
            italic,
            size,
            upem: glyph.upem,
        };
        for command in &glyph.commands {
            out.push(match *command {
                Command::Move(gx, gy) => {
                    let (x, y) = scaled_point(&fit, gx, gy)?;
                    Command::Move(x, y)
                }
                Command::Line(gx, gy) => {
                    let (x, y) = scaled_point(&fit, gx, gy)?;
                    Command::Line(x, y)
                }
                Command::Quad(cx, cy, gx, gy) => {
                    let (cx, cy) = scaled_point(&fit, cx, cy)?;
                    let (x, y) = scaled_point(&fit, gx, gy)?;
                    Command::Quad(cx, cy, x, y)
                }
                Command::Close => Command::Close,
            });
        }
    }
    Ok(())
}

#[cfg(feature = "png")]
mod load {
    use super::LoadedGlyph;
    use crate::outlines::Command;
    use skrifa::{
        DrawMemory, GlyphId, MetadataProvider, ScalerFont,
        font::Font,
        instance::{NormalizedCoord, Size},
        raw::FontRef,
    };
    #[derive(Default)]
    struct Collect {
        commands: Vec<Command>,
        unsupported: bool,
    }

    impl Collect {
        fn keeps(&self) -> bool {
            !self.unsupported && !self.commands.is_empty()
        }

        fn unit(&mut self, value: f32) -> i32 {
            if (value * 2.0).fract() != 0.0 {
                self.unsupported = true;
            }
            (value + 0.5).floor() as i32
        }
    }

    impl skrifa::font::glyph::outline::PathSink for Collect {
        fn move_to(&mut self, x: f32, y: f32) {
            let command = Command::Move(self.unit(x), self.unit(y));
            self.commands.push(command);
        }

        fn line_to(&mut self, x: f32, y: f32) {
            let command = Command::Line(self.unit(x), self.unit(y));
            self.commands.push(command);
        }

        fn quad_to(&mut self, cx: f32, cy: f32, x: f32, y: f32) {
            let command = Command::Quad(self.unit(cx), self.unit(cy), self.unit(x), self.unit(y));
            self.commands.push(command);
        }

        fn curve_to(&mut self, _: f32, _: f32, _: f32, _: f32, _: f32, _: f32) {
            self.unsupported = true;
        }

        fn close(&mut self) {
            self.commands.push(Command::Close);
        }
    }

    fn outline_commands(data: &'static [u8], id: GlyphId) -> Option<(i64, Vec<Command>)> {
        let scaler = Font::new(data, 0).map(|font| ScalerFont::unhinted(font, None))?;
        let outline = scaler.outline(id)?;
        let mut sink = Collect::default();
        if outline.draw(DrawMemory::Scratch, &mut sink).is_ok() && sink.keeps() {
            Some((i64::from(scaler.font().units_per_em()), sink.commands))
        } else {
            None
        }
    }

    fn advance_units(data: &'static [u8], id: GlyphId) -> Option<i64> {
        let font = FontRef::new(data).ok()?;
        let coords: &[NormalizedCoord] = &[];
        let width = font
            .glyph_metrics(Size::unscaled(), coords)
            .advance_width(id)?;
        if !width.is_finite() || width < 0.0 {
            return None;
        }
        let rounded = width.round();
        if rounded > i64::MAX as f32 {
            return None;
        }
        Some(rounded as i64)
    }

    pub(super) fn load_by_id(data: &'static [u8], glyph: u16) -> Option<LoadedGlyph> {
        if data.is_empty() {
            return None;
        }
        let id = GlyphId::new(u32::from(glyph));
        let (upem, commands) = outline_commands(data, id)?;
        let advance = advance_units(data, id)?;
        if upem <= 0 || advance < 0 {
            return None;
        }
        Some(LoadedGlyph {
            upem,
            advance,
            commands,
        })
    }

    pub(super) fn load_by_codepoint(data: &'static [u8], cp: u32) -> Option<LoadedGlyph> {
        if data.is_empty() {
            return None;
        }
        let scaler = Font::new(data, 0).map(|font| ScalerFont::unhinted(font, None))?;
        let id = char::from_u32(cp).and_then(|c| scaler.font().charmap().map_unicode(c))?;
        let (upem, commands) = outline_commands(data, id)?;
        let advance = advance_units(data, id)?;
        if upem <= 0 || advance < 0 {
            return None;
        }
        Some(LoadedGlyph {
            upem,
            advance,
            commands,
        })
    }
}

#[cfg(feature = "png")]
pub(crate) fn load_emoji_glyph(data: &'static [u8], glyph: u16) -> Option<LoadedGlyph> {
    load::load_by_id(data, glyph)
}

#[cfg(feature = "png")]
pub(crate) fn load_codepoint(data: &'static [u8], cp: u32) -> Option<LoadedGlyph> {
    load::load_by_codepoint(data, cp)
}

#[cfg(not(feature = "png"))]
pub(crate) fn load_emoji_glyph(_: &'static [u8], _: u16) -> Option<LoadedGlyph> {
    None
}

#[cfg(not(feature = "png"))]
pub(crate) fn load_codepoint(_: &'static [u8], _: u32) -> Option<LoadedGlyph> {
    None
}

#[cfg(all(feature = "png", test))]
pub(crate) fn font_for_codepoint(
    noto: &NotoFonts,
    weight: Weight,
    cp: u32,
) -> Option<(FallbackFont, LoadedGlyph)> {
    for (font, data) in candidates(noto, weight) {
        if let Some(loaded) = load_codepoint(data, cp) {
            return Some((font, loaded));
        }
    }
    None
}
