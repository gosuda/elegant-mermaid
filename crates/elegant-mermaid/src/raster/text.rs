use super::{RasterError, encode, invalid, paint};
use crate::{
    r#gen::advances::ADVANCES,
    outlines::{self, Command, Contours, GlyphOutlines, fallback::NotoFonts},
    scene::TextItem,
    theme::{TextChoice, Theme, Token},
};
use skrifa::{
    DrawMemory, ScalerFont,
    font::{Font, glyph::outline::PathSink},
};
use std::sync::LazyLock;
use tiny_skia::{FillRule, PathBuilder, Pixmap, Transform};

static EMBEDDED: LazyLock<GlyphOutlines> = LazyLock::new(|| {
    let fonts: [(u8, &[u8]); 2] = [
        (0, include_bytes!("../../assets/fonts/Inter-Regular.ttf")),
        (1, include_bytes!("../../assets/fonts/Inter-SemiBold.ttf")),
    ];
    let noto = NotoFonts {
        emoji: include_bytes!("../../assets/fonts/NotoEmoji-Regular.ttf"),
        sans_regular: include_bytes!("../../assets/fonts/NotoSans-Regular.ttf"),
        sans_semibold: include_bytes!("../../assets/fonts/NotoSans-SemiBold.ttf"),
        symbols_regular: include_bytes!("../../assets/fonts/NotoSansSymbols-Regular.ttf"),
        symbols_semibold: include_bytes!("../../assets/fonts/NotoSansSymbols-SemiBold.ttf"),
        symbols2: include_bytes!("../../assets/fonts/NotoSansSymbols2-Regular.ttf"),
        math: include_bytes!("../../assets/fonts/NotoSansMath-Regular.ttf"),
        cjk_regular: include_bytes!("../../assets/fonts/NotoSansCJKsc-Regular.ttf"),
        cjk_semibold: include_bytes!("../../assets/fonts/NotoSansCJKsc-SemiBold.ttf"),
        coptic: include_bytes!("../../assets/fonts/NotoSansCoptic-Regular.ttf"),
    };
    GlyphOutlines::with_fallback(fonts.map(|(weight, data)| load(weight, data)), noto)
});

/// The outlines of the embedded Inter fonts, built on first use.
///
/// Implied on-curve points of a TrueType contour, which fall on half font units,
/// round half up. A codepoint whose outline has any other fraction, such as a
/// scaled composite component, or uses a cubic segment, has no outline; the
/// embedded fonts have neither.
pub fn inter_outlines() -> GlyphOutlines {
    EMBEDDED.clone()
}

fn load(weight: u8, data: &'static [u8]) -> (i64, Contours) {
    let Some(scaler) = Font::new(data, 0).map(|font| ScalerFont::unhinted(font, None)) else {
        return (0, Contours::new());
    };
    let charmap = scaler.font().charmap();
    let mut glyphs = Contours::new();
    for row in ADVANCES.iter().filter(|row| row.weight == weight) {
        let Some(outline) = char::from_u32(row.cp)
            .and_then(|c| charmap.map_unicode(c))
            .and_then(|id| scaler.outline(id))
        else {
            continue;
        };
        let mut sink = Collect::default();
        if outline.draw(DrawMemory::Scratch, &mut sink).is_ok() && sink.keeps() {
            glyphs.insert(row.cp, sink.commands);
        }
    }
    (i64::from(scaler.font().units_per_em()), glyphs)
}

#[derive(Default)]
struct Collect {
    commands: Vec<Command>,
    unsupported: bool,
}
impl Collect {
    fn keeps(&self) -> bool {
        !self.unsupported && !self.commands.is_empty()
    }
    fn unit(&mut self, v: f32) -> i32 {
        if (v * 2.0).fract() != 0.0 {
            self.unsupported = true;
        }
        (v + 0.5).floor() as i32
    }
}
impl PathSink for Collect {
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

pub(super) fn draw(
    pix: &mut Pixmap,
    t: &TextItem,
    theme: &Theme,
    outlines: &GlyphOutlines,
    tr: Transform,
) -> Result<(), RasterError> {
    let row = crate::r#gen::styles::STYLES
        .iter()
        .find(|r| r.name == t.style.name())
        .ok_or_else(invalid)?;
    let name = if row.fill == "on-series" {
        match theme.series_text(t.series) {
            TextChoice::Background => "bg",
            _ => "fg",
        }
    } else {
        row.fill
    };
    let token = Token::ALL
        .into_iter()
        .find(|t| t.id() == name)
        .ok_or_else(invalid)?;
    let mut path = PathBuilder::new();
    for command in outlines::text_commands(outlines, t).map_err(encode)? {
        match command {
            Command::Move(x, y) => path.move_to(x as f32, y as f32),
            Command::Line(x, y) => path.line_to(x as f32, y as f32),
            Command::Quad(cx, cy, x, y) => path.quad_to(cx as f32, cy as f32, x as f32, y as f32),
            Command::Close => path.close(),
        }
    }
    if let Some(path) = path.finish() {
        pix.fill_path(
            &path,
            &paint(theme.colour(token), 255),
            FillRule::Winding,
            tr,
            None,
        );
    }
    Ok(())
}

#[cfg(test)]
mod missing_glyph_regression {
    use super::{draw, inter_outlines};
    use crate::r#gen::advances::ADVANCES;
    use crate::r#gen::unicodewidth::UNICODE_WIDTH;
    use crate::geom::{Rect, floor_div};
    use crate::measure::{Weight, ceil_div, upem};
    use crate::scene::{Align, Run, TextItem, TextRole, TextStyle};
    use std::error::Error;
    use tiny_skia::{Pixmap, Transform};

    const MISSING_NARROW: char = match char::from_u32(0x378) {
        Some(c) => c,
        None => '?',
    };
    const MISSING_NARROW_2: char = match char::from_u32(0x379) {
        Some(c) => c,
        None => '?',
    };
    const VISIBLE: char = 'A';
    const X0: i32 = 1280;
    const Y0: i32 = 1280;
    const BOX_W: i32 = 4096;
    const BOX_H: i32 = 1280;
    const SIZE_PX: i32 = 14;
    const CANVAS_PX: u32 = 96;
    const CANVAS_ROWS_PX: u32 = 48;

    fn weight_for(role: TextRole) -> Weight {
        match role {
            TextRole::Body => Weight::Regular,
            TextRole::Title | TextRole::Label => Weight::Semibold,
        }
    }

    fn table_width(cp: u32) -> u8 {
        let index = UNICODE_WIDTH.partition_point(|row| row.hi < cp);
        UNICODE_WIDTH
            .get(index)
            .filter(|row| row.lo <= cp)
            .map_or(1, |row| row.value)
    }

    fn table_advance(w: Weight, cp: u32) -> Result<u16, Box<dyn Error>> {
        let key = (w.index(), cp);
        let index = ADVANCES.partition_point(|row| (row.weight, row.cp) < key);
        match ADVANCES.get(index) {
            Some(row) if (row.weight, row.cp) == key => Ok(row.units),
            _ => Err(format!("no advance row for cp {cp}").into()),
        }
    }

    fn assert_missing_glyphs_have_no_outline(w: Weight) -> Result<(), Box<dyn Error>> {
        let outlines = inter_outlines();
        for (name, c, expected_width) in [
            ("narrow", MISSING_NARROW, 1_u8),
            ("narrow2", MISSING_NARROW_2, 1_u8),
        ] {
            assert_eq!(
                table_width(u32::from(c)),
                expected_width,
                "{name} fallback class drifted in the generated width table"
            );
            assert!(
                !outlines.has_outline(w, u32::from(c)),
                "{name} {c:?} gained an Inter outline; choose another missing glyph"
            );
            assert!(
                crate::outlines::fallback::font_for_codepoint(outlines.noto(), w, u32::from(c))
                    .is_none(),
                "{name} {c:?} gained a fallback outline; choose another missing glyph"
            );
            let key = (w.index(), u32::from(c));
            let index = ADVANCES.partition_point(|row| (row.weight, row.cp) < key);
            assert!(
                ADVANCES
                    .get(index)
                    .is_none_or(|row| (row.weight, row.cp) != key),
                "{name} {c:?} gained an advance row; the fallback is no longer exercised"
            );
        }
        assert!(
            outlines.has_outline(w, u32::from(VISIBLE)),
            "the visible glyph must exist so the render is not empty"
        );
        Ok(())
    }

    fn item(role: TextRole, align: Align, text: &str, x: i32) -> TextItem {
        TextItem {
            rect: Rect {
                x,
                y: Y0,
                w: BOX_W,
                h: BOX_H,
            },
            role,
            size: SIZE_PX,
            align,
            style: TextStyle::Text,
            series: 0,
            lines: vec![vec![Run::plain(text)]],
        }
    }

    fn render(role: TextRole, align: Align, text: &str, x: i32) -> Result<Pixmap, Box<dyn Error>> {
        let mut pix = Pixmap::new(CANVAS_PX, CANVAS_ROWS_PX).ok_or("pixmap allocation failed")?;
        let theme = crate::theme::resolve("elegant-light")?;
        let geometry_to_pixels = Transform::from_scale(1.0 / 64.0, 1.0 / 64.0);
        draw(
            &mut pix,
            &item(role, align, text, x),
            &theme,
            &inter_outlines(),
            geometry_to_pixels,
        )?;
        Ok(pix)
    }

    fn assert_painted(pix: &Pixmap, name: &str) {
        assert!(
            pix.data().iter().any(|&byte| byte != 0),
            "{name}: the visible glyph must paint pixels"
        );
    }

    #[test]
    fn missing_glyph_prefix_moves_visible_glyph_by_the_upem_rule() -> Result<(), Box<dyn Error>> {
        let prefixed = format!("{MISSING_NARROW}{MISSING_NARROW_2}{VISIBLE}");
        for (role, name) in [(TextRole::Body, "regular"), (TextRole::Label, "semibold")] {
            let w = weight_for(role);
            assert_missing_glyphs_have_no_outline(w)?;
            let em = upem(w);
            let prefix_units = 2 * floor_div(6 * em + 5, 10);
            let factor = SIZE_PX as f32 * 64.0 / em as f32;
            let required_offset =
                i32::try_from((prefix_units as f32 * factor + 0.5).floor() as i64)
                    .map_err(|_| "prefix offset out of range")?;
            assert!(
                required_offset > 0,
                "{name}: the missing-glyph prefix must move the visible glyph"
            );
            let composed = render(role, Align::Start, prefixed.as_str(), X0)?;
            let visible = VISIBLE.to_string();
            let shifted = render(role, Align::Start, visible.as_str(), X0 + required_offset)?;
            assert_painted(&composed, name);
            assert_eq!(
                composed.data(),
                shifted.data(),
                "{name}: visible glyph must land at the independently computed origin"
            );
        }
        Ok(())
    }

    #[test]
    fn missing_glyph_width_shifts_end_aligned_glyph() -> Result<(), Box<dyn Error>> {
        let suffixed = format!("{VISIBLE}{MISSING_NARROW}{MISSING_NARROW_2}");
        for (role, name) in [(TextRole::Body, "regular"), (TextRole::Label, "semibold")] {
            let w = weight_for(role);
            assert_missing_glyphs_have_no_outline(w)?;
            let em = upem(w);
            let visible_units = i64::from(table_advance(w, u32::from(VISIBLE))?);
            let missing_units = 2 * floor_div(6 * em + 5, 10);
            let scaled = |units: i64| ceil_div(units * i64::from(SIZE_PX) * 64, em);
            let required_shift =
                i32::try_from(scaled(visible_units + missing_units) - scaled(visible_units))
                    .map_err(|_| "width shift out of range")?;
            assert!(
                required_shift > 0,
                "{name}: the missing-glyph suffix must widen the line"
            );
            let composed = render(role, Align::End, suffixed.as_str(), X0)?;
            let visible = VISIBLE.to_string();
            let shifted = render(role, Align::End, visible.as_str(), X0 - required_shift)?;
            assert_painted(&composed, name);
            assert_eq!(
                composed.data(),
                shifted.data(),
                "{name}: end-aligned glyph must land at the independently computed origin"
            );
        }
        Ok(())
    }
    #[test]
    fn fallback_cjk_emoji_math_symbols_paint() -> Result<(), Box<dyn Error>> {
        for glyph in ["中", "文", "😀", "𝔘", "⚗"] {
            let pix = render(TextRole::Body, Align::Start, glyph, X0)?;
            assert_painted(&pix, glyph);
        }
        let pix = render(TextRole::Body, Align::Start, "中文 😀 𝔘 ⚗", X0)?;
        assert_painted(&pix, "fallback label");
        Ok(())
    }
}
