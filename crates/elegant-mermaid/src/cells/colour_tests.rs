use super::{
    ColorMode, Painted, Rgb, Token, hex, sgr, stroke_token, text_token, theme_rgb, write_row,
    xterm_16, xterm_256,
};

#[test]
fn ranks_follow_the_token_list() {
    assert_eq!(Token::Background as u8, 0);
    assert_eq!(Token::Foreground as u8, 1);
    assert_eq!(Token::Line as u8, 2);
    assert_eq!(Token::Accent as u8, 3);
    assert_eq!(Token::Muted as u8, 4);
    assert_eq!(Token::Surface as u8, 5);
    assert_eq!(Token::Border as u8, 6);
    assert_eq!(Token::Series0 as u8, 7);
    assert_eq!(Token::Series11 as u8, 18);
    assert_eq!(Token::Error as u8, 19);
    assert_eq!(Token::Warning as u8, 20);
    assert_eq!(Token::Success as u8, 21);
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
        theme_rgb("elegant-dark", Token::Background),
        Some(Rgb {
            r: 17,
            g: 17,
            b: 19
        })
    );
    assert!(
        theme_rgb("no-such-theme", Token::Background).is_none(),
        "theme lookup reads the generated table: contract theme_rgb(\"no-such-theme\", Token::Background).is_none() failed; observed predicate=false"
    );
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
        sgr(midpoint, Token::Series1, ColorMode::Ansi16),
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
            token: Token::Foreground,
        },
        Painted {
            ch: 'i',
            token: Token::Foreground,
        },
        Painted {
            ch: ' ',
            token: Token::Foreground,
        },
        Painted {
            ch: ' ',
            token: Token::Foreground,
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
    assert!(
        out.starts_with(" \u{1b}[38;5;"),
        "spaces never change the colour and rows end at the default: contract out.starts_with(\" \\u{{1b}}[38;5;\") failed; observed out={:?}",
        out
    );
    assert!(
        out.ends_with("a\u{1b}[39m\n"),
        "spaces never change the colour and rows end at the default: contract out.ends_with(\"a\\u{{1b}}[39m\\n\") failed; observed out={:?}",
        out
    );
}

#[test]
fn background_counts_as_the_default_foreground() {
    let row = [Painted {
        ch: 'x',
        token: Token::Background,
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
    assert!(
        !out.contains('\u{1b}'),
        "colour mode none writes no escape bytes: contract !out.contains('\\u{{1b}}') failed; observed out={:?}",
        out
    );
}

#[test]
fn stroke_fallback_replaces_low_contrast_tokens_by_line() {
    assert_eq!(stroke_token("elegant-light", Token::Error), Token::Error);
    assert_eq!(stroke_token("elegant-light", Token::Series0), Token::Line);
    assert_eq!(
        stroke_token("elegant-light", Token::Series1),
        Token::Series1
    );
    assert_eq!(stroke_token("elegant-light", Token::Border), Token::Border);
}

#[test]
fn text_style_tokens_resolve_through_the_styles_table() {
    assert_eq!(text_token("elegant-light", "text", 0), Token::Foreground);
    assert_eq!(text_token("elegant-light", "text-muted", 0), Token::Muted);
    assert_eq!(
        text_token("elegant-light", "text-inverse", 0),
        Token::Background
    );
    assert_eq!(
        text_token("elegant-light", "text-on-series", 1),
        Token::Background
    );
    assert_eq!(
        text_token("elegant-light", "no-such-style", 3),
        Token::Foreground
    );
}

#[test]
fn the_default_foreground_sequence_is_esc_39_m() {
    assert_eq!(super::DEFAULT_FG, "\u{1b}[39m");
    assert_eq!(
        sgr(
            Rgb { r: 1, g: 2, b: 3 },
            Token::Foreground,
            ColorMode::Truecolor
        ),
        "\u{1b}[39m"
    );
    assert_eq!(
        sgr(
            Rgb { r: 1, g: 2, b: 3 },
            Token::Background,
            ColorMode::Ansi16
        ),
        "\u{1b}[39m"
    );
}
