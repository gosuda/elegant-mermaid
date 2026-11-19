use super::Style;
use crate::r#gen::cellsymbols::CELL_SYMBOLS;
use crate::r#gen::glyphjoin::{GLYPH_JOIN, Glyph};

/// The character set of a text rendering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Charset {
    /// Unicode box-drawing and symbol glyphs.
    Unicode,
    /// ASCII glyphs only.
    Ascii,
}

/// Cell style code `none`.
pub const STYLE_NONE: u8 = 0;
/// Cell style code `dotted`.
pub const STYLE_DOTTED: u8 = 1;
/// Cell style code `rounded`.
pub const STYLE_ROUNDED: u8 = 2;
/// Cell style code `light`.
pub const STYLE_LIGHT: u8 = 3;
/// Cell style code `heavy:`.
pub const STYLE_HEAVY: u8 = 4;
/// Cell style code `double`.
pub const STYLE_DOUBLE: u8 = 5;

const MAX_STYLE: u8 = STYLE_DOUBLE;

fn charset_code(charset: Charset) -> u8 {
    match charset {
        Charset::Unicode => 0,
        Charset::Ascii => 1,
    }
}

fn lookup(charset: u8, style: u8, mask: u8) -> Option<&'static Glyph> {
    GLYPH_JOIN
        .iter()
        .find(|row| row.charset == charset && row.style == style && row.mask == mask)
}

fn rune_of(row: &Glyph) -> char {
    char::from_u32(row.rune).unwrap_or(' ')
}

/// Returns the glyph of a cell's arms in a character set and a line style.
///
/// The ASCII rows exist for style `none` and style `dotted` only; every other
/// ASCII style reads the `none` rows, so ASCII output ignores style except for
/// `dotted`. Unicode style `none` has only a mask-zero row; absent rows print space.
pub fn glyph(charset: Charset, style: Style, mask: u8) -> char {
    glyph_code(charset, style as u8, mask)
}

fn glyph_code(charset: Charset, style: u8, mask: u8) -> char {
    let arms = mask & 0x0F;
    let requested = style.min(MAX_STYLE);
    let code = charset_code(charset);
    let row = match charset {
        Charset::Ascii => {
            let ascii_style = if requested == STYLE_DOTTED {
                STYLE_DOTTED
            } else {
                STYLE_NONE
            };
            lookup(code, ascii_style, arms)
        }
        Charset::Unicode => lookup(code, requested, arms),
    };
    row.map_or(' ', rune_of)
}

/// Returns the code point of a symbol name in a character set.
pub fn symbol(charset: Charset, name: &str) -> Option<u32> {
    let row = CELL_SYMBOLS.iter().find(|row| row.name == name)?;
    match charset {
        Charset::Unicode => Some(row.unicode),
        Charset::Ascii => Some(row.ascii),
    }
}

/// Returns the braille glyph of a dot pattern.
pub fn braille(dots: u8, charset: Charset) -> char {
    if dots == 0 {
        return ' ';
    }
    match charset {
        Charset::Unicode => char::from_u32(0x2800 + u32::from(dots)).unwrap_or(' '),
        Charset::Ascii => '#',
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Charset, STYLE_DOTTED, STYLE_DOUBLE, STYLE_HEAVY, STYLE_LIGHT, STYLE_ROUNDED,
        glyph_code as glyph, symbol,
    };
    use crate::r#gen::glyphjoin::GLYPH_JOIN;

    const LIGHT: [char; 16] = [
        ' ', '╵', '╶', '└', '╷', '│', '┌', '├', '╴', '┘', '─', '┴', '┐', '┤', '┬', '┼',
    ];
    const HEAVY: [char; 16] = [
        ' ', '╹', '╺', '┗', '╻', '┃', '┏', '┣', '╸', '┛', '━', '┻', '┓', '┫', '┳', '╋',
    ];
    const DOUBLE: [char; 16] = [
        ' ', '╵', '╶', '╚', '╷', '║', '╔', '╠', '╴', '╝', '═', '╩', '╗', '╣', '╦', '╬',
    ];
    const ROUNDED: [char; 16] = [
        ' ', '╵', '╶', '╰', '╷', '│', '╭', '├', '╴', '╯', '─', '┴', '╮', '┤', '┬', '┼',
    ];
    const DOTTED: [char; 16] = [
        ' ', '╵', '╶', '└', '╷', '┆', '┌', '├', '╴', '┘', '┄', '┴', '┐', '┤', '┬', '┼',
    ];
    const ASCII: [char; 16] = [
        ' ', '|', '-', '+', '|', '|', '+', '+', '-', '+', '-', '+', '+', '+', '+', '+',
    ];
    const ASCII_DOTTED: [char; 16] = [
        ' ', ':', '.', '+', ':', ':', '+', '+', '.', '+', '.', '+', '+', '+', '+', '+',
    ];

    #[test]
    fn unicode_glyphs_match_the_spec_table_for_all_masks() {
        for mask in 0..16u8 {
            let index = usize::from(mask);
            assert_eq!(
                glyph(Charset::Unicode, STYLE_LIGHT, mask),
                LIGHT[index],
                "light {mask}"
            );
            assert_eq!(
                glyph(Charset::Unicode, STYLE_HEAVY, mask),
                HEAVY[index],
                "heavy {mask}"
            );
            assert_eq!(
                glyph(Charset::Unicode, STYLE_DOUBLE, mask),
                DOUBLE[index],
                "double {mask}"
            );
            assert_eq!(
                glyph(Charset::Unicode, STYLE_ROUNDED, mask),
                ROUNDED[index],
                "rounded {mask}"
            );
            assert_eq!(
                glyph(Charset::Unicode, STYLE_DOTTED, mask),
                DOTTED[index],
                "dotted {mask}"
            );
        }
    }

    #[test]
    fn ascii_glyphs_match_both_row_sets() {
        for mask in 0..16u8 {
            let index = usize::from(mask);
            assert_eq!(
                glyph(Charset::Ascii, STYLE_LIGHT, mask),
                ASCII[index],
                "plain {mask}"
            );
            assert_eq!(
                glyph(Charset::Ascii, STYLE_HEAVY, mask),
                ASCII[index],
                "plain {mask}"
            );
            assert_eq!(
                glyph(Charset::Ascii, STYLE_DOUBLE, mask),
                ASCII[index],
                "plain {mask}"
            );
            assert_eq!(
                glyph(Charset::Ascii, STYLE_ROUNDED, mask),
                ASCII[index],
                "plain {mask}"
            );
            assert_eq!(
                glyph(Charset::Ascii, STYLE_DOTTED, mask),
                ASCII_DOTTED[index],
                "dotted {mask}"
            );
        }
    }

    #[test]
    fn mask_zero_is_a_space_in_every_style_and_charset() {
        for style in 0..=STYLE_DOUBLE {
            assert_eq!(glyph(Charset::Unicode, style, 0), ' ');
            assert_eq!(glyph(Charset::Ascii, style, 0), ' ');
        }
    }

    #[test]
    fn unicode_style_none_with_arms_has_no_glyph() {
        for mask in 1..16u8 {
            assert_eq!(glyph(Charset::Unicode, 0, mask), ' ');
        }
    }

    #[test]
    fn high_bits_of_a_mask_are_ignored() {
        assert_eq!(glyph(Charset::Unicode, STYLE_LIGHT, 0xF5), '│');
        assert_eq!(glyph(Charset::Unicode, STYLE_LIGHT, 0xA3), '└');
    }

    #[test]
    fn generated_table_has_the_spec_row_counts() {
        let unicode_dotted = GLYPH_JOIN
            .iter()
            .filter(|row| row.charset == 0 && row.style == 0)
            .count();
        assert_eq!(unicode_dotted, 1);
        for style in 1..=STYLE_DOUBLE {
            let count = GLYPH_JOIN
                .iter()
                .filter(|row| row.charset == 0 && row.style == style)
                .count();
            assert_eq!(count, 16, "unicode style {style}");
        }
        for style in [0u8, STYLE_DOTTED] {
            let count = GLYPH_JOIN
                .iter()
                .filter(|row| row.charset == 1 && row.style == style)
                .count();
            assert_eq!(count, 16, "ascii style {style}");
        }
        assert_eq!(GLYPH_JOIN.len(), 1 + 5 * 16 + 2 * 16);
    }

    #[test]
    fn generated_table_is_sorted_and_unique() {
        for pair in GLYPH_JOIN.windows(2) {
            let left = (pair[0].charset, pair[0].style, pair[0].mask);
            let right = (pair[1].charset, pair[1].style, pair[1].mask);
            assert!(left < right, "{left:?} then {right:?}");
        }
    }

    #[test]
    fn the_dotted_rows_carry_the_dotted_glyphs() {
        assert_eq!(glyph(Charset::Unicode, STYLE_DOTTED, 5), '┆');
        assert_eq!(glyph(Charset::Unicode, STYLE_DOTTED, 10), '┄');
        assert_eq!(glyph(Charset::Unicode, STYLE_DOTTED, 0), ' ');
        assert_eq!(glyph(Charset::Unicode, STYLE_DOTTED, 5) as u32, 0x2506);
        assert_eq!(glyph(Charset::Unicode, STYLE_DOTTED, 10) as u32, 0x2504);
    }

    #[test]
    fn double_style_stubs_are_light() {
        for mask in [1u8, 2, 4, 8] {
            assert_eq!(
                glyph(Charset::Unicode, STYLE_DOUBLE, mask),
                glyph(Charset::Unicode, STYLE_LIGHT, mask)
            );
        }
    }

    #[test]
    fn symbols_read_the_generated_table() {
        assert_eq!(symbol(Charset::Unicode, "disc"), Some(0x25CF));
        assert_eq!(symbol(Charset::Ascii, "disc"), Some(0x2A));
        assert_eq!(symbol(Charset::Unicode, "bullseye"), Some(0x25C9));
        assert_eq!(symbol(Charset::Ascii, "bullseye"), Some(0x40));
        assert_eq!(symbol(Charset::Unicode, "box-hollow"), Some(0x25A1));
        assert_eq!(symbol(Charset::Ascii, "box-hollow"), Some(0x6F));
        assert_eq!(symbol(Charset::Unicode, "unknown"), Some(0x3F));
        assert_eq!(symbol(Charset::Ascii, "no-such-symbol"), None);
    }

    #[test]
    fn every_symbol_row_has_both_columns() {
        for name in [
            "disc",
            "ring",
            "bullseye",
            "diamond",
            "diamond-hollow",
            "box-hollow",
            "cloud",
            "database",
            "disk",
            "internet",
            "server",
            "unknown",
        ] {
            assert!(symbol(Charset::Unicode, name).is_some(), "{name}");
            assert!(symbol(Charset::Ascii, name).is_some(), "{name}");
        }
    }

    #[test]
    fn braille_glyphs_round_trip_all_values() {
        for value in 1u8..=255 {
            let ch = super::braille(value, Charset::Unicode);
            assert_eq!(u32::from(ch), 0x2800 + u32::from(value), "value {value}");
            assert_eq!(super::braille(value, Charset::Ascii), '#');
        }
        assert_eq!(super::braille(0, Charset::Unicode), ' ');
        assert_eq!(super::braille(0, Charset::Ascii), ' ');
        assert_eq!(super::braille(0xFF, Charset::Unicode), '⣿');
    }
}
