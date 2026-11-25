use super::{Command, Contours, GlyphOutlines, run_weight, text_commands};
use crate::{
    geom::{GeomError, Rect},
    measure::{Weight, advance_units},
    scene::{Align, Run, TextItem, TextRole, TextStyle},
};
use std::error::Error;

const UPEM: i64 = 2048;
const SIZE: i32 = 16;
const BOX_X: i32 = 640;
const BOX_Y: i32 = 1280;
const BOX_W: i32 = 6400;
const REGULAR_SIDE: i32 = 1000;
const SEMIBOLD_SIDE: i32 = 2000;
const GLYPH: u32 = 65;
const SPACE: u32 = 32;

fn square(side: i32) -> Vec<Command> {
    vec![
        Command::Move(0, 0),
        Command::Line(side, 0),
        Command::Line(side, side),
        Command::Line(0, side),
        Command::Close,
    ]
}

fn synthetic() -> GlyphOutlines {
    let font = |side| {
        let mut glyphs = Contours::new();
        glyphs.insert(GLYPH, square(side));
        (UPEM, glyphs)
    };
    GlyphOutlines::new([font(REGULAR_SIDE), font(SEMIBOLD_SIDE)])
}

fn item(role: TextRole, align: Align, lines: Vec<Vec<Run>>) -> TextItem {
    TextItem {
        rect: Rect {
            x: BOX_X,
            y: BOX_Y,
            w: BOX_W,
            h: 1280,
        },
        role,
        size: SIZE,
        align,
        style: TextStyle::Text,
        series: 0,
        lines,
    }
}

fn plain(role: TextRole, align: Align, text: &str) -> TextItem {
    item(role, align, vec![vec![Run::plain(text)]])
}

fn rounded(numerator: i64) -> i64 {
    (2 * numerator + UPEM).div_euclid(2 * UPEM)
}

fn scaled(units: i64) -> i64 {
    rounded(units * i64::from(SIZE) * 64)
}

fn first_move(commands: &[Command]) -> Result<(i32, i32), Box<dyn Error>> {
    match commands.first() {
        Some(&Command::Move(x, y)) => Ok((x, y)),
        other => Err(format!("expected a leading move, observed {other:?}").into()),
    }
}

fn moves(commands: &[Command]) -> Vec<(i32, i32)> {
    commands
        .iter()
        .filter_map(|c| match *c {
            Command::Move(x, y) => Some((x, y)),
            _ => None,
        })
        .collect()
}

fn advance(weight: Weight, cp: u32) -> i64 {
    advance_units(weight, cp)
}

#[test]
fn start_aligned_glyph_lands_on_the_body_baseline() -> Result<(), Box<dyn Error>> {
    let commands = text_commands(&synthetic(), &plain(TextRole::Body, Align::Start, "A"))?;
    let baseline = 1280 + 640 + 358;
    let half = REGULAR_SIDE / 2;
    assert_eq!(
        commands,
        vec![
            Command::Move(BOX_X, baseline),
            Command::Line(BOX_X + half, baseline),
            Command::Line(BOX_X + half, baseline - half),
            Command::Line(BOX_X, baseline - half),
            Command::Close,
        ]
    );
    Ok(())
}

#[test]
fn title_role_uses_the_title_line_height() -> Result<(), Box<dyn Error>> {
    let commands = text_commands(&synthetic(), &plain(TextRole::Title, Align::Start, "A"))?;
    assert_eq!(first_move(&commands)?, (BOX_X, 1280 + 768 + 358));
    Ok(())
}

#[test]
fn each_line_drops_by_one_line_height() -> Result<(), Box<dyn Error>> {
    let lines = vec![vec![Run::plain("A")], vec![Run::plain("A")]];
    let commands = text_commands(&synthetic(), &item(TextRole::Body, Align::Start, lines))?;
    let at = moves(&commands);
    assert_eq!(at.len(), 2);
    assert_eq!(at[1].1 - at[0].1, 1280);
    Ok(())
}

#[test]
fn italic_run_shears_by_height() -> Result<(), Box<dyn Error>> {
    let italic = Run {
        text: "A".into(),
        bold: false,
        italic: true,
    };
    let commands = text_commands(
        &synthetic(),
        &item(TextRole::Body, Align::Start, vec![vec![italic]]),
    )?;
    let baseline = 1280 + 640 + 358;
    let half = REGULAR_SIDE / 2;
    let shear = (13 * i64::from(half)).div_euclid(64);
    let shear = i32::try_from(shear)?;
    assert_eq!(shear, 101);
    assert_eq!(
        commands,
        vec![
            Command::Move(BOX_X, baseline),
            Command::Line(BOX_X + half, baseline),
            Command::Line(BOX_X + half + shear, baseline - half),
            Command::Line(BOX_X + shear, baseline - half),
            Command::Close,
        ]
    );
    Ok(())
}

#[test]
fn end_and_middle_alignment_subtract_the_measured_width() -> Result<(), Box<dyn Error>> {
    let units = advance(Weight::Regular, GLYPH);
    let numerator = units * i64::from(SIZE) * 64;
    let width = (numerator + UPEM - 1).div_euclid(UPEM);
    let end = text_commands(&synthetic(), &plain(TextRole::Body, Align::End, "A"))?;
    assert_eq!(
        i64::from(first_move(&end)?.0),
        i64::from(BOX_X) + i64::from(BOX_W) - width
    );
    let middle = text_commands(&synthetic(), &plain(TextRole::Body, Align::Middle, "A"))?;
    assert_eq!(
        i64::from(first_move(&middle)?.0),
        i64::from(BOX_X) + i64::from(BOX_W).div_euclid(2) - width.div_euclid(2)
    );
    Ok(())
}

#[test]
fn glyph_origins_follow_the_prefix_advance_and_skip_outline_free_codepoints()
-> Result<(), Box<dyn Error>> {
    let commands = text_commands(&synthetic(), &plain(TextRole::Body, Align::Start, "AA A"))?;
    let a = advance(Weight::Regular, GLYPH);
    let space = advance(Weight::Regular, SPACE);
    let origins: Vec<i64> = [0, a, 2 * a + space]
        .into_iter()
        .map(|prefix| i64::from(BOX_X) + scaled(prefix))
        .collect();
    let observed: Vec<i64> = moves(&commands)
        .into_iter()
        .map(|(x, _)| i64::from(x))
        .collect();
    assert_eq!(observed, origins);
    Ok(())
}

#[test]
fn runs_choose_their_weight_and_continue_where_the_previous_run_ended() -> Result<(), Box<dyn Error>>
{
    let label = plain(TextRole::Label, Align::Start, "A");
    let body = plain(TextRole::Body, Align::Start, "A");
    let bold = Run {
        text: "A".into(),
        bold: true,
        italic: false,
    };
    let italic = Run {
        text: "A".into(),
        bold: false,
        italic: true,
    };
    let weights = [
        (run_weight(&label, &label.lines[0][0]), Weight::Semibold),
        (run_weight(&body, &body.lines[0][0]), Weight::Regular),
        (run_weight(&body, &bold), Weight::Semibold),
        (run_weight(&label, &italic), Weight::Regular),
    ];
    for (observed, expected) in weights {
        assert_eq!(observed, expected);
    }
    let semibold = text_commands(&synthetic(), &label)?;
    assert_eq!(
        semibold.get(1),
        Some(&Command::Line(BOX_X + SEMIBOLD_SIDE / 2, 1280 + 640 + 358))
    );
    let two_runs = item(
        TextRole::Body,
        Align::Start,
        vec![vec![Run::plain("A"), bold]],
    );
    let at = moves(&text_commands(&synthetic(), &two_runs)?);
    let a = advance(Weight::Regular, GLYPH);
    assert_eq!(
        at.get(1).map(|p| i64::from(p.0)),
        Some(i64::from(BOX_X) + scaled(a))
    );
    Ok(())
}

#[test]
fn placement_overflow_is_reported() {
    let mut text = plain(TextRole::Body, Align::Start, "A");
    text.rect.x = i32::MAX;
    assert_eq!(text_commands(&synthetic(), &text), Err(GeomError::Overflow));
}

#[cfg(feature = "png")]
mod inter {
    use super::*;
    use crate::raster::inter_outlines;

    #[test]
    fn embedded_fonts_outline_letters_but_not_spaces() {
        let outlines = inter_outlines();
        for weight in [Weight::Regular, Weight::Semibold] {
            for cp in u32::from('A')..=u32::from('z') {
                assert!(outlines.has_outline(weight, cp), "{weight:?} U+{cp:04X}");
            }
            assert!(!outlines.has_outline(weight, SPACE));
        }
    }

    #[test]
    fn embedded_fonts_outline_nearly_every_advance_row() {
        let outlines = inter_outlines();
        for (weight, index) in [(Weight::Regular, 0u8), (Weight::Semibold, 1u8)] {
            let rows = crate::r#gen::advances::ADVANCES
                .iter()
                .filter(|row| row.weight == index);
            let total = rows.clone().count();
            let outlined = rows
                .filter(|row| outlines.has_outline(weight, row.cp))
                .count();
            assert!(
                outlined * 100 >= total * 90,
                "{weight:?}: {outlined} of {total} advance rows have an outline"
            );
        }
    }

    #[test]
    fn embedded_text_places_closed_contours_deterministically() -> Result<(), Box<dyn Error>> {
        let text = plain(TextRole::Label, Align::Middle, "Hi there");
        let first = text_commands(&inter_outlines(), &text)?;
        let second = text_commands(&inter_outlines(), &text)?;
        assert_eq!(first, second);
        let contours = moves(&first).len();
        let closes = first.iter().filter(|c| **c == Command::Close).count();
        assert!(contours >= 7, "observed {contours} contours");
        assert_eq!(contours, closes);
        Ok(())
    }
}

#[test]
fn fallback_order_checks_sans_first_and_coptic_last() {
    use crate::outlines::fallback::{FallbackFont, candidates};
    let empty = crate::outlines::fallback::NotoFonts::empty();
    let regular = candidates(&empty, Weight::Regular);
    assert_eq!(regular[0].0, FallbackFont::Sans);
    assert_eq!(regular[5].0, FallbackFont::Coptic);
    let semibold = candidates(&empty, Weight::Semibold);
    assert_eq!(semibold[0].0, FallbackFont::Sans);
    assert_eq!(semibold[1].0, FallbackFont::Symbols);
    assert_eq!(semibold[5].0, FallbackFont::Coptic);
}

#[test]
fn fitted_narrow_glyph_centres_with_exact_integers() -> Result<(), Box<dyn Error>> {
    use crate::outlines::fallback::{LoadedGlyph, place_into};
    let glyph = LoadedGlyph {
        upem: 2048,
        advance: 1000,
        commands: square(1000),
    };
    let mut out = Vec::new();
    place_into(&mut out, &glyph, SIZE, i64::from(BOX_X), 700, 2278, false)?;
    assert_eq!(
        out,
        vec![
            Command::Move(BOX_X + 100, 2278),
            Command::Line(BOX_X + 100 + 500, 2278),
            Command::Line(BOX_X + 100 + 500, 2278 - 500),
            Command::Line(BOX_X + 100, 2278 - 500),
            Command::Close,
        ]
    );
    Ok(())
}

#[test]
fn fitted_wide_glyph_scales_down_with_exact_integers() -> Result<(), Box<dyn Error>> {
    use crate::outlines::fallback::{LoadedGlyph, place_into};
    let glyph = LoadedGlyph {
        upem: 2048,
        advance: 2000,
        commands: square(2000),
    };
    let mut out = Vec::new();
    place_into(&mut out, &glyph, SIZE, i64::from(BOX_X), 500, 2278, false)?;
    assert_eq!(
        out,
        vec![
            Command::Move(BOX_X, 2278),
            Command::Line(BOX_X + 500, 2278),
            Command::Line(BOX_X + 500, 2278 - 500),
            Command::Line(BOX_X, 2278 - 500),
            Command::Close,
        ]
    );
    Ok(())
}

#[cfg(feature = "png")]
mod fallback {
    use super::*;
    use crate::{
        geom::floor_div,
        measure::{round_half_up, upem},
        outlines::fallback,
    };

    fn noto() -> crate::outlines::fallback::NotoFonts {
        *crate::raster::inter_outlines().noto()
    }

    fn baseline() -> i64 {
        i64::from(BOX_Y) + 640 + floor_div(i64::from(SIZE) * 64 * 35, 100)
    }

    fn slot_for(weight: Weight, cps: &[u32]) -> i64 {
        let sum: i64 = cps.iter().copied().map(|cp| advance(weight, cp)).sum();
        round_half_up(sum * i64::from(SIZE) * 64, upem(weight))
    }

    fn expect_single(weight: Weight, cp: u32, text: &str) -> Result<Vec<Command>, Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        let (_, loaded) =
            fallback::font_for_codepoint(outlines.noto(), weight, cp).ok_or("no fallback font")?;
        let slot = slot_for(weight, &[cp]);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, text))?;
        assert_eq!(observed, expected);
        Ok(expected)
    }

    #[test]
    fn inter_wins_for_a() {
        let outlines = crate::raster::inter_outlines();
        assert!(outlines.has_outline(Weight::Regular, u32::from('A')));
        assert!(outlines.has_outline(Weight::Semibold, u32::from('A')));
    }

    #[test]
    fn cjk_zhong_comes_from_the_cjk_font() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x4E2D));
        let (font, loaded) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x4E2D)
            .ok_or("U+4E2D has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Cjk);
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0x4E2D, "中")?;
        Ok(())
    }

    #[test]
    fn house_comes_from_the_symbols_font() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x2302));
        let (font, loaded) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x2302)
            .ok_or("U+2302 has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Symbols);
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0x2302, "⌂")?;
        Ok(())
    }

    #[test]
    fn fraktur_u_comes_from_the_math_font() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x1D518));
        let (font, loaded) =
            fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x1D518)
                .ok_or("U+1D518 has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Math);
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0x1D518, "𝔘")?;
        Ok(())
    }

    #[test]
    fn coptic_sima_comes_from_the_coptic_font() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x03E7));
        let (font, loaded) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x03E7)
            .ok_or("U+03E7 has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Coptic);
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0x03E7, "ϧ")?;
        Ok(())
    }

    #[test]
    fn cyllic_comes_from_noto_sans() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0xA66E));
        let (font, loaded) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0xA66E)
            .ok_or("U+A66E has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Sans);
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0xA66E, "ꙮ")?;
        Ok(())
    }

    #[test]
    fn regional_pair_is_one_glyph_with_the_summed_slot() -> Result<(), Box<dyn Error>> {
        let pair = [0x1F1EFu32, 0x1F1F5u32];
        let (len, glyph) =
            fallback::longest_sequence(&pair).ok_or("flag pair is not a sequence")?;
        assert_eq!(len, 2);
        let outlines = crate::raster::inter_outlines();
        let loaded =
            fallback::load_emoji_glyph(outlines.noto().emoji, glyph).ok_or("no emoji glyph")?;
        let slot = slot_for(Weight::Regular, &pair);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, "🇯🇵"))?;
        assert_eq!(observed, expected);
        Ok(())
    }

    #[test]
    fn inter_wins_for_heart() {
        let outlines = crate::raster::inter_outlines();
        assert!(outlines.has_outline(Weight::Regular, 0x2764));
        assert!(outlines.has_outline(Weight::Semibold, 0x2764));
    }

    #[test]
    fn alembic_alone_takes_symbols_fallback_while_vs16_merges_the_emoji_slot()
    -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x2697));
        assert!(!fallback::has_presentation(0x2697));
        let (font, _) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x2697)
            .ok_or("U+2697 has no fallback font")?;
        assert_eq!(font, fallback::FallbackFont::Symbols);
        expect_single(Weight::Regular, 0x2697, "⚗")?;
        let pair = [0x2697u32, 0xFE0Fu32];
        let loaded =
            fallback::load_codepoint(outlines.noto().emoji, 0x2697).ok_or("no emoji alembic")?;
        let slot = slot_for(Weight::Regular, &pair);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let text: String = pair.iter().copied().filter_map(char::from_u32).collect();
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, &text))?;
        assert_eq!(observed, expected);
        Ok(())
    }

    #[test]
    fn white_smiling_face_alone_comes_from_a_text_font() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(!outlines.has_outline(Weight::Regular, 0x263A));
        assert!(!fallback::has_presentation(0x263A));
        let (font, loaded) = fallback::font_for_codepoint(outlines.noto(), Weight::Regular, 0x263A)
            .ok_or("U+263A has no fallback font")?;
        assert!(matches!(
            font,
            fallback::FallbackFont::Sans
                | fallback::FallbackFont::Symbols
                | fallback::FallbackFont::Symbols2
                | fallback::FallbackFont::Math
                | fallback::FallbackFont::Cjk
                | fallback::FallbackFont::Coptic
        ));
        assert!(!loaded.commands.is_empty());
        expect_single(Weight::Regular, 0x263A, "☺")?;
        Ok(())
    }

    #[test]
    fn keycap_with_vs16_is_one_glyph_in_the_summed_slot() -> Result<(), Box<dyn Error>> {
        let triple = [0x23u32, 0xFE0Fu32, 0x20E3u32];
        let (len, glyph) = fallback::longest_sequence(&triple).ok_or("no keycap sequence")?;
        assert_eq!(len, 3);
        assert_eq!(fallback::sequence_at(&triple), Some(glyph));
        let outlines = crate::raster::inter_outlines();
        let loaded =
            fallback::load_emoji_glyph(outlines.noto().emoji, glyph).ok_or("no keycap glyph")?;
        let slot = slot_for(Weight::Regular, &triple);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let text: String = triple.iter().copied().filter_map(char::from_u32).collect();
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, &text))?;
        assert_eq!(observed, expected);
        Ok(())
    }

    #[test]
    fn heart_with_vs16_takes_the_emoji_glyph() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        assert!(outlines.has_outline(Weight::Regular, 0x2764));
        assert!(fallback::load_codepoint(outlines.noto().emoji, 0x2764).is_some());
        assert!(fallback::longest_sequence(&[0x2764u32, 0xFE0Fu32]).is_none());
        let pair = [0x2764u32, 0xFE0Fu32];
        let loaded =
            fallback::load_codepoint(outlines.noto().emoji, 0x2764).ok_or("no emoji heart")?;
        let slot = slot_for(Weight::Regular, &pair);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let text: String = pair.iter().copied().filter_map(char::from_u32).collect();
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, &text))?;
        assert_eq!(observed, expected);
        Ok(())
    }

    #[test]
    fn inter_glyph_with_vs16_and_no_emoji_glyph_takes_both_slots() -> Result<(), Box<dyn Error>> {
        let outlines = crate::raster::inter_outlines();
        let cp = 0x41u32;
        assert!(outlines.has_outline(Weight::Regular, cp));
        assert!(fallback::load_codepoint(outlines.noto().emoji, cp).is_none());
        assert!(!fallback::has_presentation(cp));
        assert!(fallback::longest_sequence(&[cp, 0xFE0Fu32]).is_none());
        assert!(
            !crate::r#gen::emojiseq::EMOJI_SEQUENCES
                .iter()
                .any(|row| row.scalars.first() == Some(&cp))
        );
        let font = outlines.font(Weight::Regular);
        let commands = font.glyphs.get(&cp).ok_or("no inter glyph")?;
        let loaded = fallback::LoadedGlyph {
            upem: font.upem,
            advance: advance_units(Weight::Regular, cp),
            commands: commands.clone(),
        };
        let slot = slot_for(Weight::Regular, &[cp, 0xFE0Fu32]);
        let mut expected = Vec::new();
        fallback::place_into(
            &mut expected,
            &loaded,
            SIZE,
            i64::from(BOX_X),
            slot,
            baseline(),
            false,
        )?;
        let text: String = [cp, 0xFE0Fu32]
            .iter()
            .copied()
            .filter_map(char::from_u32)
            .collect();
        let observed = text_commands(&outlines, &plain(TextRole::Body, Align::Start, &text))?;
        assert_eq!(observed, expected);
        Ok(())
    }

    #[test]
    fn noto_glyphs_use_the_requested_noto_bytes() {
        let fresh = noto();
        assert!(!fresh.emoji.is_empty());
        assert!(!fresh.sans_regular.is_empty());
        assert!(!fresh.symbols_regular.is_empty());
        assert!(!fresh.symbols2.is_empty());
        assert!(!fresh.math.is_empty());
        assert!(!fresh.cjk_regular.is_empty());
        assert!(!fresh.coptic.is_empty());
    }
}
