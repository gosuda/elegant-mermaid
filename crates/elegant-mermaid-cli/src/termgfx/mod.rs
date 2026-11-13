pub mod iterm;
pub mod kitty;
pub mod probe;
pub mod sixel;

pub const ESC: u8 = 0x1B;
pub const BEL: u8 = 0x07;
pub const ST: [u8; 2] = [ESC, b'\\'];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Cells,
    Kitty,
    Iterm,
    Sixel,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Self::Cells => "cells",
            Self::Kitty => "kitty",
            Self::Iterm => "iterm",
            Self::Sixel => "sixel",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum GfxError {
    #[error("buffer does not match its dimensions")]
    Buffer,
}

pub(crate) fn write_decimal(out: &mut Vec<u8>, value: u32) {
    let mut digits = [b'0'; 10];
    let mut cursor = digits.len();
    let mut rest = value;
    loop {
        cursor -= 1;
        digits[cursor] = b'0' + u8::try_from(rest % 10).unwrap_or(0);
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    out.extend_from_slice(&digits[cursor..]);
}

#[cfg(test)]
mod tests {
    use super::write_decimal;

    #[test]
    fn decimals_are_minimal_with_no_leading_zero() {
        for (value, want) in [
            (0u32, "0"),
            (1, "1"),
            (9, "9"),
            (10, "10"),
            (99, "99"),
            (100, "100"),
            (4096, "4096"),
            (u32::MAX, "4294967295"),
        ] {
            let mut out = Vec::new();
            write_decimal(&mut out, value);
            assert_eq!(String::from_utf8_lossy(&out), want);
        }
    }
}
