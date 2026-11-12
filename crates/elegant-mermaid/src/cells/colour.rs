use crate::r#gen::seriestext::SERIES_TEXT;
use crate::r#gen::strokeok::STROKE_OK;
use crate::r#gen::styles::STYLES;
use crate::r#gen::themes::THEMES;

const DEFAULT_FG: &str = "\u{1b}[39m";

/// The closed list of colour tokens, in rank order, rank 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token {
    /// The theme background.
    Bg,
    /// The theme foreground; the terminal default.
    Fg,
    /// The line colour.
    Line,
    /// The accent colour.
    Accent,
    /// The muted colour.
    Muted,
    /// The surface colour.
    Surface,
    /// The border colour.
    Border,
    /// Series colour `0` to `11`.
    Series(u8),
    /// The error colour.
    Error,
    /// The warning colour.
    Warning,
    /// The success colour.
    Success,
}

impl Token {
    /// Returns the rank of the token, from 0 for `Bg` to 21 for `Success`.
    pub fn rank(self) -> u8 {
        match self {
            Token::Bg => 0,
            Token::Fg => 1,
            Token::Line => 2,
            Token::Accent => 3,
            Token::Muted => 4,
            Token::Surface => 5,
            Token::Border => 6,
            Token::Series(index) => 7 + index.min(11),
            Token::Error => 19,
            Token::Warning => 20,
            Token::Success => 21,
        }
    }

    /// Returns the token name of the theme table.
    pub fn name(self) -> &'static str {
        match self {
            Token::Bg => "bg",
            Token::Fg => "fg",
            Token::Line => "line",
            Token::Accent => "accent",
            Token::Muted => "muted",
            Token::Surface => "surface",
            Token::Border => "border",
            Token::Error => "error",
            Token::Warning => "warning",
            Token::Success => "success",
            Token::Series(0) => "series0",
            Token::Series(1) => "series1",
            Token::Series(2) => "series2",
            Token::Series(3) => "series3",
            Token::Series(4) => "series4",
            Token::Series(5) => "series5",
            Token::Series(6) => "series6",
            Token::Series(7) => "series7",
            Token::Series(8) => "series8",
            Token::Series(9) => "series9",
            Token::Series(10) => "series10",
            Token::Series(_) => "series11",
        }
    }
}

/// A colour mode of the text back end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColorMode {
    /// No escape sequences.
    None,
    /// The nearest of the 16 xterm default colours.
    Ansi16,
    /// The tmux 256-colour cube and grey ramp.
    Ansi256,
    /// 24-bit colour.
    Truecolor,
}

/// An sRGB colour with 8-bit channels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rgb {
    /// The red channel.
    pub r: u8,
    /// The green channel.
    pub g: u8,
    /// The blue channel.
    pub b: u8,
}

/// One printed character and the colour token of its cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Painted {
    /// The printed character.
    pub ch: char,
    /// The colour token of the cell.
    pub token: Token,
}

/// Parses a `#rrggbb` colour.
pub fn hex(text: &str) -> Option<Rgb> {
    let digits = text.strip_prefix('#')?;
    if digits.len() != 6 {
        return None;
    }
    let value = u32::from_str_radix(digits, 16).ok()?;
    Some(Rgb {
        r: u8::try_from((value >> 16) & 0xFF).ok()?,
        g: u8::try_from((value >> 8) & 0xFF).ok()?,
        b: u8::try_from(value & 0xFF).ok()?,
    })
}

/// Returns the colour that a theme gives a token.
pub fn theme_rgb(theme: &str, token: Token) -> Option<Rgb> {
    let entry = THEMES.iter().find(|candidate| candidate.name == theme)?;
    let key = token.name();
    let row = entry
        .tokens
        .iter()
        .find(|candidate| candidate.token == key)?;
    hex(row.value)
}

/// Replaces a status or series token by `line` when its theme stroke fails
/// the 3:1 contrast gate.
pub fn stroke_token(theme: &str, token: Token) -> Token {
    let key = token.name();
    let row = STROKE_OK
        .iter()
        .find(|candidate| candidate.theme == theme && candidate.token == key);
    match row {
        Some(entry) if entry.ok == 0 => Token::Line,
        _ => token,
    }
}

/// Returns the colour token of a text style, resolving a series fill through
/// the series text table. A `plate` choice gives `fg`.
pub fn text_token(theme: &str, style: &str, series: u8) -> Token {
    let row = STYLES
        .iter()
        .find(|candidate| candidate.class == 1 && candidate.name == style);
    match row.map(|candidate| candidate.fill) {
        Some("muted") => Token::Muted,
        Some("bg") => Token::Bg,
        Some("on-series") => match series_choice(theme, series) {
            1 => Token::Bg,
            _ => Token::Fg,
        },
        _ => Token::Fg,
    }
}

fn series_choice(theme: &str, series: u8) -> u8 {
    let index = series.min(11);
    SERIES_TEXT
        .iter()
        .find(|row| row.theme == theme && row.series == index)
        .map(|row| row.choice)
        .unwrap_or(0)
}

fn cube_level(index: u8) -> u8 {
    match index {
        0 => 0,
        1 => 95,
        2 => 135,
        3 => 175,
        4 => 215,
        _ => 255,
    }
}

fn cube_index(channel: u8) -> u8 {
    if channel < 48 {
        0
    } else if channel < 114 {
        1
    } else {
        u8::try_from((i32::from(channel) - 35) / 40)
            .unwrap_or(5)
            .min(5)
    }
}

fn squared_distance(a: Rgb, b: (i32, i32, i32)) -> i32 {
    let dr = i32::from(a.r) - b.0;
    let dg = i32::from(a.g) - b.1;
    let db = i32::from(a.b) - b.2;
    dr * dr + dg * dg + db * db
}

/// Returns the tmux 256-colour index of a colour.
pub fn xterm_256(colour: Rgb) -> u8 {
    let qr = cube_index(colour.r);
    let qg = cube_index(colour.g);
    let qb = cube_index(colour.b);
    let cube = 16 + 36 * qr + 6 * qg + qb;
    if colour.r == cube_level(qr) && colour.g == cube_level(qg) && colour.b == cube_level(qb) {
        return cube;
    }
    let average = (i32::from(colour.r) + i32::from(colour.g) + i32::from(colour.b)) / 3;
    let grey_index = if average > 238 {
        23
    } else {
        ((average - 3).max(0) / 10).min(23)
    };
    let grey = 8 + 10 * grey_index;
    let grey_distance = squared_distance(colour, (grey, grey, grey));
    let cube_distance = squared_distance(
        colour,
        (
            i32::from(cube_level(qr)),
            i32::from(cube_level(qg)),
            i32::from(cube_level(qb)),
        ),
    );
    if grey_distance < cube_distance {
        u8::try_from(232 + grey_index).unwrap_or(255)
    } else {
        cube
    }
}

const XTERM_16: [(i32, i32, i32); 16] = [
    (0, 0, 0),
    (205, 0, 0),
    (0, 205, 0),
    (205, 205, 0),
    (0, 0, 238),
    (205, 0, 205),
    (0, 205, 205),
    (229, 229, 229),
    (127, 127, 127),
    (255, 0, 0),
    (0, 255, 0),
    (255, 255, 0),
    (92, 92, 255),
    (255, 0, 255),
    (0, 255, 255),
    (255, 255, 255),
];

/// Returns the index of the nearest xterm default colour; the lowest index
/// wins a tie.
pub fn xterm_16(colour: Rgb) -> u8 {
    let mut best = 0usize;
    let mut best_distance = i32::MAX;
    for (index, candidate) in XTERM_16.iter().enumerate() {
        let distance = squared_distance(colour, *candidate);
        if distance < best_distance {
            best = index;
            best_distance = distance;
        }
    }
    u8::try_from(best).unwrap_or(0)
}

/// Returns the SGR sequence that selects a colour. `Fg` and `Bg` both select
/// the terminal default foreground.
pub fn sgr(colour: Rgb, token: Token, mode: ColorMode) -> String {
    if matches!(token, Token::Fg | Token::Bg) {
        return DEFAULT_FG.to_owned();
    }
    match mode {
        ColorMode::None => String::new(),
        ColorMode::Truecolor => {
            format!("\u{1b}[38;2;{};{};{}m", colour.r, colour.g, colour.b)
        }
        ColorMode::Ansi256 => format!("\u{1b}[38;5;{}m", xterm_256(colour)),
        ColorMode::Ansi16 => {
            let index = xterm_16(colour);
            if index < 8 {
                format!("\u{1b}[3{index}m")
            } else {
                format!("\u{1b}[9{}m", index - 8)
            }
        }
    }
}

/// Writes one row of painted characters, then a line feed. The row starts
/// with current token `fg`; a non-space character writes its token when it
/// differs from the current one; the row ends with the default foreground
/// when the current token is not `fg`.
pub fn write_row(out: &mut String, cells: &[Painted], mode: ColorMode, theme: &str) {
    if mode == ColorMode::None {
        for painted in cells {
            out.push(painted.ch);
        }
        out.push('\n');
        return;
    }
    let mut current = Token::Fg;
    for painted in cells {
        let token = normalise(painted.token);
        if painted.ch != ' '
            && token != current
            && let Some(colour) = theme_rgb(theme, token)
        {
            out.push_str(&sgr(colour, token, mode));
            current = token;
        }
        out.push(painted.ch);
    }
    if current != Token::Fg {
        out.push_str(DEFAULT_FG);
    }
    out.push('\n');
}

fn normalise(token: Token) -> Token {
    match token {
        Token::Bg => Token::Fg,
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ColorMode, Painted, Rgb, Token, hex, sgr, stroke_token, text_token, theme_rgb, write_row,
        xterm_16, xterm_256,
    };

    #[test]
    fn ranks_follow_the_token_list() {
        assert_eq!(Token::Bg.rank(), 0);
        assert_eq!(Token::Fg.rank(), 1);
        assert_eq!(Token::Line.rank(), 2);
        assert_eq!(Token::Accent.rank(), 3);
        assert_eq!(Token::Muted.rank(), 4);
        assert_eq!(Token::Surface.rank(), 5);
        assert_eq!(Token::Border.rank(), 6);
        assert_eq!(Token::Series(0).rank(), 7);
        assert_eq!(Token::Series(11).rank(), 18);
        assert_eq!(Token::Error.rank(), 19);
        assert_eq!(Token::Warning.rank(), 20);
        assert_eq!(Token::Success.rank(), 21);
    }

    #[test]
    fn hex_parses_six_digit_colours_only() {
        assert_eq!(
            hex("#8b8d98"),
            Some(Rgb {
                r: 139,
                g: 141,
                b: 152
            })
        );
        assert_eq!(
            hex("#FFFFFF"),
            Some(Rgb {
                r: 255,
                g: 255,
                b: 255
            })
        );
        assert_eq!(hex("#fff"), None);
        assert_eq!(hex("8b8d98"), None);
        assert_eq!(hex("#gggggg"), None);
    }

    #[test]
    fn theme_lookup_reads_the_generated_table() {
        assert_eq!(
            theme_rgb("elegant-light", Token::Border),
            Some(Rgb {
                r: 139,
                g: 141,
                b: 152
            })
        );
        assert_eq!(
            theme_rgb("elegant-dark", Token::Bg),
            Some(Rgb {
                r: 17,
                g: 17,
                b: 19
            })
        );
        assert!(theme_rgb("no-such-theme", Token::Bg).is_none());
    }

    #[test]
    fn worked_256_colour_example_gives_246() {
        let border = Rgb {
            r: 139,
            g: 141,
            b: 152,
        };
        assert_eq!(xterm_256(border), 246);
        assert_eq!(
            sgr(border, Token::Border, ColorMode::Ansi256),
            "\u{1b}[38;5;246m"
        );
    }

    #[test]
    fn cube_colours_take_the_cube_index() {
        assert_eq!(xterm_256(Rgb { r: 0, g: 0, b: 0 }), 16);
        assert_eq!(
            xterm_256(Rgb {
                r: 255,
                g: 255,
                b: 255
            }),
            231
        );
        assert_eq!(
            xterm_256(Rgb {
                r: 135,
                g: 135,
                b: 135
            }),
            102
        );
    }

    #[test]
    fn low_grey_channels_take_the_grey_ramp() {
        assert_eq!(xterm_256(Rgb { r: 8, g: 8, b: 8 }), 232);
        assert_eq!(
            xterm_256(Rgb {
                r: 238,
                g: 238,
                b: 238
            }),
            255
        );
        assert_eq!(
            xterm_256(Rgb {
                r: 48,
                g: 48,
                b: 48
            }),
            236
        );
    }

    #[test]
    fn sixteen_colour_picks_the_nearest_index() {
        assert_eq!(xterm_16(Rgb { r: 0, g: 0, b: 0 }), 0);
        assert_eq!(
            xterm_16(Rgb {
                r: 255,
                g: 255,
                b: 255
            }),
            15
        );
        assert_eq!(xterm_16(Rgb { r: 250, g: 6, b: 5 }), 9);
        assert_eq!(
            xterm_16(Rgb {
                r: 130,
                g: 130,
                b: 130
            }),
            8
        );
        assert_eq!(
            sgr(Rgb { r: 255, g: 0, b: 0 }, Token::Error, ColorMode::Ansi16),
            "\u{1b}[91m"
        );
        assert_eq!(
            sgr(Rgb { r: 205, g: 0, b: 0 }, Token::Error, ColorMode::Ansi16),
            "\u{1b}[31m"
        );
    }

    #[test]
    fn sixteen_colour_ties_go_to_the_lowest_index() {
        let midpoint = Rgb { r: 230, g: 0, b: 0 };
        let to_one = 25 * 25;
        let to_nine = 25 * 25;
        assert_eq!(to_one, to_nine);
        assert_eq!(xterm_16(midpoint), 1);
        assert_eq!(
            sgr(midpoint, Token::Series(1), ColorMode::Ansi16),
            "\u{1b}[31m"
        );
    }

    #[test]
    fn worked_truecolor_example_has_the_exact_bytes() {
        let border = Token::Border;
        let row = [
            Painted {
                ch: '│',
                token: border,
            },
            Painted {
                ch: ' ',
                token: border,
            },
            Painted {
                ch: ' ',
                token: border,
            },
            Painted {
                ch: 'H',
                token: Token::Fg,
            },
            Painted {
                ch: 'i',
                token: Token::Fg,
            },
            Painted {
                ch: ' ',
                token: Token::Fg,
            },
            Painted {
                ch: ' ',
                token: Token::Fg,
            },
            Painted {
                ch: '│',
                token: border,
            },
        ];
        let mut out = String::new();
        write_row(&mut out, &row, ColorMode::Truecolor, "elegant-light");
        assert_eq!(
            out,
            "\u{1b}[38;2;139;141;152m│  \u{1b}[39mHi  \u{1b}[38;2;139;141;152m│\u{1b}[39m\n"
        );
    }

    #[test]
    fn spaces_never_change_the_colour_and_rows_end_at_the_default() {
        let row = [
            Painted {
                ch: ' ',
                token: Token::Error,
            },
            Painted {
                ch: 'a',
                token: Token::Line,
            },
        ];
        let mut out = String::new();
        write_row(&mut out, &row, ColorMode::Ansi256, "elegant-light");
        assert!(out.starts_with(" \u{1b}[38;5;"));
        assert!(out.ends_with("a\u{1b}[39m\n"));
    }

    #[test]
    fn background_counts_as_the_default_foreground() {
        let row = [Painted {
            ch: 'x',
            token: Token::Bg,
        }];
        let mut out = String::new();
        write_row(&mut out, &row, ColorMode::Truecolor, "elegant-light");
        assert_eq!(out, "x\n");
    }

    #[test]
    fn colour_mode_none_writes_no_escape_bytes() {
        let row = [
            Painted {
                ch: 'a',
                token: Token::Error,
            },
            Painted {
                ch: 'b',
                token: Token::Line,
            },
        ];
        let mut out = String::new();
        write_row(&mut out, &row, ColorMode::None, "elegant-light");
        assert_eq!(out, "ab\n");
        assert!(!out.contains('\u{1b}'));
    }

    #[test]
    fn stroke_fallback_replaces_low_contrast_tokens_by_line() {
        assert_eq!(stroke_token("elegant-light", Token::Error), Token::Error);
        assert_eq!(stroke_token("elegant-light", Token::Series(0)), Token::Line);
        assert_eq!(
            stroke_token("elegant-light", Token::Series(1)),
            Token::Series(1)
        );
        assert_eq!(stroke_token("elegant-light", Token::Border), Token::Border);
    }

    #[test]
    fn text_style_tokens_resolve_through_the_styles_table() {
        assert_eq!(text_token("elegant-light", "text", 0), Token::Fg);
        assert_eq!(text_token("elegant-light", "text-muted", 0), Token::Muted);
        assert_eq!(text_token("elegant-light", "text-inverse", 0), Token::Bg);
        assert_eq!(text_token("elegant-light", "text-on-series", 1), Token::Bg);
        assert_eq!(text_token("elegant-light", "no-such-style", 3), Token::Fg);
    }

    #[test]
    fn the_default_foreground_sequence_is_esc_39_m() {
        assert_eq!(super::DEFAULT_FG, "\u{1b}[39m");
        assert_eq!(
            sgr(Rgb { r: 1, g: 2, b: 3 }, Token::Fg, ColorMode::Truecolor),
            "\u{1b}[39m"
        );
        assert_eq!(
            sgr(Rgb { r: 1, g: 2, b: 3 }, Token::Bg, ColorMode::Ansi16),
            "\u{1b}[39m"
        );
    }
}
