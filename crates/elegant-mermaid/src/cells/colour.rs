use crate::r#gen::seriestext::SERIES_TEXT;
use crate::r#gen::strokeok::STROKE_OK;
use crate::r#gen::styles::STYLES;
use crate::r#gen::themes::THEMES;
pub use crate::theme::{Colour as Rgb, Token};

const DEFAULT_FG: &str = "\u{1b}[39m";

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
    let key = token.id();
    let row = entry
        .tokens
        .iter()
        .find(|candidate| candidate.token == key)?;
    hex(row.value)
}

/// Replaces a status or series token by `line` when its theme stroke fails
/// the 3:1 contrast gate.
pub fn stroke_token(theme: &str, token: Token) -> Token {
    let key = token.id();
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
        Some("bg") => Token::Background,
        Some("on-series") => match series_choice(theme, series) {
            1 => Token::Background,
            _ => Token::Foreground,
        },
        _ => Token::Foreground,
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
    if matches!(token, Token::Foreground | Token::Background) {
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
    let mut current = Token::Foreground;
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
    if current != Token::Foreground {
        out.push_str(DEFAULT_FG);
    }
    out.push('\n');
}

fn normalise(token: Token) -> Token {
    match token {
        Token::Background => Token::Foreground,
        other => other,
    }
}

#[cfg(test)]
#[path = "colour_tests.rs"]
mod tests;
