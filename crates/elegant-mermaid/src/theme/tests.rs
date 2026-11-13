#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
use super::*;
fn c(hex: &str) -> Colour {
    Colour::parse_hex(hex).unwrap()
}
fn y(c: Colour) -> f64 {
    let linear = |v: u8| {
        let u = f64::from(v) / 255.0;
        if u <= 0.04045 {
            u / 12.92
        } else {
            ((u + 0.055) / 1.055).powf(2.4)
        }
    };
    0.2126 * linear(c.r) + 0.7152 * linear(c.g) + 0.0722 * linear(c.b)
}
fn ratio(a: Colour, b: Colour) -> f64 {
    let a = y(a);
    let b = y(b);
    (a.max(b) + 0.05) / (a.min(b) + 0.05)
}
#[test]
fn theme_colour_arithmetic() {
    let cases = [
        ("#000000", 0, 0, 0),
        ("#ffffff", 0, 0, 100),
        ("#808080", 0, 0, 50),
        ("#ff0000", 0, 100, 50),
        ("#00ff00", 120, 100, 50),
        ("#0000ff", 240, 100, 50),
        ("#ffff00", 60, 100, 50),
        ("#00ffff", 180, 100, 50),
        ("#ff00ff", 300, 100, 50),
        ("#404040", 0, 0, 25),
        ("#bfbfbf", 0, 0, 75),
        ("#8b8d98", 231, 6, 57),
    ];
    for (hex, h, s, l) in cases {
        assert_eq!(c(hex).to_hsl(), Hsl { h, s, l });
        assert_eq!(invert(invert(c(hex))), c(hex));
    }
    assert_eq!(c("#aBc").hex(), "#aabbcc");
    for bad in ["", "fff", "#12", "#1234", "#ggg", "#12345z"] {
        assert!(
            Colour::parse_hex(bad).is_err(),
            "invalid hex {bad:?} parsed as {:?}",
            Colour::parse_hex(bad)
        );
    }
    let blue = c("#3366cc");
    assert_eq!(darken(blue, 10).hex(), "#2952a3");
    assert_eq!(lighten(blue, 10).hex(), "#5c85d6");
    assert_eq!(
        adjust(
            blue,
            Delta {
                h: -200,
                s: 5,
                l: -3
            }
        )
        .hex(),
        "#c65e2a"
    );
    assert_eq!(invert(c("#123456")).hex(), "#edcba9");
    assert_eq!(mk_border_dark(blue).hex(), "#8593ae");
    assert_eq!(mk_border_light(blue).hex(), "#52607b");
    assert!(
        is_dark(c("#777777")),
        "#777777 must be dark; luminance={}",
        luminance(c("#777777"))
    );
    assert_eq!(luminance(c("#8b8d98")), 17567);
}
#[test]
fn theme_roundtrip_and_contrast_oracle() {
    let mut state = 1u32;
    let mut worst = 0;
    for _ in 0..2000 {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let bytes = state.to_le_bytes();
        let colour = Colour {
            r: bytes[0],
            g: bytes[1],
            b: bytes[2],
        };
        let back = colour.to_hsl().to_colour();
        worst = worst
            .max(colour.r.abs_diff(back.r))
            .max(colour.g.abs_diff(back.g))
            .max(colour.b.abs_diff(back.b));
        assert!(
            (luminance(colour) as f64 / 65535.0 - y(colour)).abs() < 0.00003,
            "colour {colour:?}: integer luminance={}, oracle={}",
            luminance(colour),
            y(colour)
        );
        for threshold in [30, 45] {
            let r = ratio(colour, invert(colour));
            if (r - f64::from(threshold) / 10.0).abs() > 0.01 {
                assert_eq!(
                    contrast(colour, invert(colour), threshold),
                    r >= f64::from(threshold) / 10.0
                );
            }
        }
    }
    assert_eq!(worst, 4);
}
#[test]
fn theme_built_in_theme_contrast() {
    for name in [
        "elegant-light",
        "elegant-dark",
        "github-light",
        "github-dark",
        "catppuccin-latte",
        "catppuccin-mocha",
        "nord",
        "solarized-light",
        "solarized-dark",
    ] {
        let th = resolve(name).unwrap();
        for (token, threshold) in [
            (Token::Foreground, 45),
            (Token::Muted, 45),
            (Token::Line, 30),
            (Token::Border, 30),
            (Token::Accent, 30),
        ] {
            for surface in [Token::Background, Token::Surface] {
                let a = th.colour(token);
                let b = th.colour(surface);
                assert!(contrast(a, b, threshold), "{name} {token:?}");
                assert!(
                    ratio(a, b) >= f64::from(threshold) / 10.0,
                    "theme {name} {token:?} on {surface:?}: colours {a:?}/{b:?}, ratio={}, threshold={threshold}",
                    ratio(a, b)
                );
            }
        }
    }
}
#[test]
fn theme_generated_choices() {
    for row in crate::r#gen::strokeok::STROKE_OK {
        let th = resolve(row.theme).unwrap();
        let token = Token::ALL
            .into_iter()
            .find(|t| t.id() == row.token)
            .unwrap();
        assert_eq!(
            th.stroke(token),
            if row.ok == 0 { Token::Line } else { token }
        );
    }
    for row in crate::r#gen::seriestext::SERIES_TEXT {
        let th = resolve(row.theme).unwrap();
        let fill = th.colour(Token::ALL[7 + usize::from(row.series)]);
        let fg = ratio(fill, th.colour(Token::Foreground));
        let bg = ratio(fill, th.colour(Token::Background));
        let choice = if fg >= 4.5 && fg >= bg {
            TextChoice::Foreground
        } else if bg >= 4.5 && bg > fg {
            TextChoice::Background
        } else {
            TextChoice::Plate
        };
        assert_eq!(th.series_text(row.series), choice);
        assert_eq!(th.series_text(row.series + 12), choice);
    }
    assert!(
        matches!(resolve("missing"), Err(ThemeError::Unknown(_))),
        "missing theme must return Unknown; observed {:?}",
        resolve("missing").err()
    );
    assert_eq!(resolve("").unwrap().name(), "elegant-light");
}

#[test]
fn theme_tabulated_contrast_ratios() {
    for (name, values) in [
        (
            "elegant-light",
            [15.98, 15.58, 5.79, 5.64, 3.69, 3.59, 3.21, 3.13, 3.18, 3.10],
        ),
        (
            "elegant-dark",
            [16.24, 15.15, 9.05, 8.44, 4.44, 4.14, 3.68, 3.43, 5.77, 5.38],
        ),
    ] {
        let theme = resolve(name).unwrap();
        for (i, token) in [
            Token::Foreground,
            Token::Muted,
            Token::Line,
            Token::Border,
            Token::Accent,
        ]
        .into_iter()
        .enumerate()
        {
            for (j, surface) in [Token::Background, Token::Surface].into_iter().enumerate() {
                assert_eq!(
                    (ratio(theme.colour(token), theme.colour(surface)) * 100.0).floor() / 100.0,
                    values[2 * i + j]
                );
            }
        }
    }
}

#[test]
fn theme_hsl_float_oracle() {
    let mut state = 1u32;
    for _ in 0..2000 {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let bytes = state.to_le_bytes();
        let colour = Colour {
            r: bytes[0],
            g: bytes[1],
            b: bytes[2],
        };
        let [r, g, b] = [colour.r, colour.g, colour.b].map(|v| f64::from(v) / 255.0);
        let hi = r.max(g).max(b);
        let lo = r.min(g).min(b);
        let d = hi - lo;
        let l = (hi + lo) / 2.0;
        let hsl = colour.to_hsl();
        assert!(
            (f64::from(hsl.l) - 100.0 * l).abs() <= 0.500001,
            "colour {colour:?}: HSL {hsl:?}, oracle lightness={}",
            100.0 * l
        );
        if d == 0.0 {
            assert_eq!(hsl.s, 0);
            continue;
        }
        let s = d / (1.0 - (2.0 * l - 1.0).abs());
        let h = if hi == r {
            60.0 * ((g - b) / d).rem_euclid(6.0)
        } else if hi == g {
            60.0 * ((b - r) / d + 2.0)
        } else {
            60.0 * ((r - g) / d + 4.0)
        };
        let error = (f64::from(hsl.h) - h).abs();
        assert!(
            error.min(360.0 - error) <= 0.500001,
            "colour {colour:?}: HSL {hsl:?}, oracle hue={h}, circular error={error}"
        );
        assert!(
            (f64::from(hsl.s) - 100.0 * s).abs() <= 0.500001,
            "colour {colour:?}: HSL {hsl:?}, oracle saturation={}",
            100.0 * s
        );
    }
}

#[test]
fn theme_hsl_to_rgb_float_oracle() {
    for h in 0..360 {
        for s in [0, 6, 25, 50, 75, 100] {
            for l in [0, 25, 50, 57, 75, 100] {
                let hsl = Hsl { h, s, l };
                let light = f64::from(l) / 100.0;
                let chroma = (1.0 - (2.0 * light - 1.0).abs()) * f64::from(s) / 100.0;
                let x = chroma * (1.0 - ((f64::from(h) / 60.0) % 2.0 - 1.0).abs());
                let parts = [
                    (chroma, x, 0.0),
                    (x, chroma, 0.0),
                    (0.0, chroma, x),
                    (0.0, x, chroma),
                    (x, 0.0, chroma),
                    (chroma, 0.0, x),
                ];
                let (r, g, b) = parts[usize::try_from(h / 60).unwrap()];
                let expected = [r, g, b].map(|v| (v + light - chroma / 2.0) * 255.0);
                let actual = hsl.to_colour();
                for (got, want) in [actual.r, actual.g, actual.b].into_iter().zip(expected) {
                    assert!(
                        (f64::from(got) - want).abs() <= 2.0,
                        "HSL {hsl:?}: RGB {actual:?}, observed channel={got}, oracle={want}"
                    );
                }
            }
        }
    }
}

#[test]
fn theme_specified_fallbacks() {
    for (name, indices, statuses) in [
        (
            "catppuccin-latte",
            &[0, 2, 3, 4, 6, 7, 8, 10][..],
            &[Token::Warning, Token::Success][..],
        ),
        ("nord", &[1, 3, 5, 9, 11][..], &[Token::Error][..]),
        (
            "solarized-light",
            &[0, 2, 4, 6, 7, 8, 10][..],
            &[Token::Success][..],
        ),
        (
            "solarized-dark",
            &[1, 5, 9, 11][..],
            &[Token::Error, Token::Warning][..],
        ),
        ("elegant-light", &[0, 2, 4, 6, 7, 8, 10][..], &[][..]),
        ("github-light", &[0, 2, 4, 6, 7, 8, 10][..], &[][..]),
        ("elegant-dark", &[9][..], &[][..]),
        ("github-dark", &[9][..], &[][..]),
        ("catppuccin-mocha", &[9][..], &[][..]),
    ] {
        let theme = resolve(name).unwrap();
        for index in indices {
            assert_eq!(theme.stroke(Token::ALL[7 + index]), Token::Line);
        }
        for token in statuses {
            assert_eq!(theme.stroke(*token), Token::Line);
        }
    }
}
