fn floor_div(a: i64, b: i64) -> i64 {
    a.div_euclid(b)
}
fn floor_mod(a: i64, b: i64) -> i64 {
    a.rem_euclid(b)
}
const MAX_CHANNEL: i64 = 255;

const FULL_TURN: i64 = 360;

const MAX_PERCENT: i64 = 100;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Colour {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

impl Colour {
    pub fn parse_hex(text: &str) -> Result<Colour, ColourError> {
        match text.as_bytes() {
            [b'#', r, g, b] => Ok(Colour {
                r: nibble(*r)?.saturating_mul(17),
                g: nibble(*g)?.saturating_mul(17),
                b: nibble(*b)?.saturating_mul(17),
            }),
            [b'#', r_hi, r_lo, g_hi, g_lo, b_hi, b_lo] => Ok(Colour {
                r: byte(*r_hi, *r_lo)?,
                g: byte(*g_hi, *g_lo)?,
                b: byte(*b_hi, *b_lo)?,
            }),
            _ => Err(ColourError::Invalid {
                text: text.to_owned(),
            }),
        }
    }

    pub fn hex(self) -> String {
        format!("#{:02x}{:02x}{:02x}", self.r, self.g, self.b)
    }

    pub fn to_hsl(self) -> Hsl {
        let r = i64::from(self.r);
        let g = i64::from(self.g);
        let b = i64::from(self.b);
        let high = r.max(g).max(b);
        let low = r.min(g).min(b);
        let delta = high - low;
        let sum = high + low;
        let l = floor_div(MAX_PERCENT * sum + MAX_CHANNEL, 2 * MAX_CHANNEL);
        if delta == 0 {
            return Hsl {
                h: 0,
                s: 0,
                l: narrow(l),
            };
        }
        let scale = MAX_CHANNEL - (sum - MAX_CHANNEL).abs();
        let s = floor_div(200 * delta + scale, 2 * scale);
        let turn = if high == r {
            60 * (g - b)
        } else if high == g {
            60 * (b - r) + 120 * delta
        } else {
            60 * (r - g) + 240 * delta
        };
        let h = floor_mod(floor_div(2 * turn + delta, 2 * delta), FULL_TURN);
        Hsl {
            h: narrow(h),
            s: narrow(s),
            l: narrow(l),
        }
    }

    pub fn is_dark(self) -> bool {
        super::contrast::is_dark(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Hsl {
    pub h: i32,
    pub s: i32,
    pub l: i32,
}

impl Hsl {
    pub fn to_colour(self) -> Colour {
        let h = floor_mod(i64::from(self.h), FULL_TURN);
        let s = i64::from(self.s).clamp(0, MAX_PERCENT);
        let l = i64::from(self.l).clamp(0, MAX_PERCENT);
        let chroma = floor_div(
            (MAX_PERCENT - (2 * l - MAX_PERCENT).abs()) * s * MAX_CHANNEL + 5000,
            10_000,
        );
        let phase = floor_mod(h, 120);
        let second = floor_div(chroma * (60 - (phase - 60).abs()) + 30, 60);
        let base = floor_div(MAX_CHANNEL * l + 50, MAX_PERCENT) - floor_div(chroma, 2);
        let (r, g, b) = sector(floor_div(h, 60), chroma, second);
        Colour {
            r: channel(r + base),
            g: channel(g + base),
            b: channel(b + base),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Delta {
    pub h: i32,
    pub s: i32,
    pub l: i32,
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ColourError {
    #[error("invalid colour {text}")]
    Invalid { text: String },
}

pub fn adjust(colour: Colour, delta: Delta) -> Colour {
    let hsl = colour.to_hsl();
    Hsl {
        h: narrow(floor_mod(i64::from(hsl.h) + i64::from(delta.h), FULL_TURN)),
        s: hsl.s.saturating_add(delta.s),
        l: hsl.l.saturating_add(delta.l),
    }
    .to_colour()
}

pub fn darken(colour: Colour, amount: i32) -> Colour {
    adjust(
        colour,
        Delta {
            h: 0,
            s: 0,
            l: amount.saturating_neg(),
        },
    )
}

pub fn lighten(colour: Colour, amount: i32) -> Colour {
    adjust(
        colour,
        Delta {
            h: 0,
            s: 0,
            l: amount,
        },
    )
}

pub fn invert(colour: Colour) -> Colour {
    Colour {
        r: 255 - colour.r,
        g: 255 - colour.g,
        b: 255 - colour.b,
    }
}

pub fn mk_border_dark(colour: Colour) -> Colour {
    adjust(
        colour,
        Delta {
            h: 0,
            s: -40,
            l: 10,
        },
    )
}
pub fn mk_border_light(colour: Colour) -> Colour {
    adjust(
        colour,
        Delta {
            h: 0,
            s: -40,
            l: -10,
        },
    )
}

fn sector(index: i64, chroma: i64, second: i64) -> (i64, i64, i64) {
    match index {
        0 => (chroma, second, 0),
        1 => (second, chroma, 0),
        2 => (0, chroma, second),
        3 => (0, second, chroma),
        4 => (second, 0, chroma),
        _ => (chroma, 0, second),
    }
}

fn channel(value: i64) -> u8 {
    u8::try_from(value.clamp(0, MAX_CHANNEL)).unwrap_or(0)
}

fn narrow(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(if value < 0 { i32::MIN } else { i32::MAX })
}

fn nibble(byte: u8) -> Result<u8, ColourError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(ColourError::Invalid {
            text: String::from_utf8_lossy(&[b'#', byte]).into_owned(),
        }),
    }
}

fn byte(high: u8, low: u8) -> Result<u8, ColourError> {
    let hi = nibble(high)?;
    let lo = nibble(low)?;
    Ok(hi.saturating_mul(16).saturating_add(lo))
}
