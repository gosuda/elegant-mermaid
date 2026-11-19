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
