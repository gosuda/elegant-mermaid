//! Text measurement: string widths, grapheme clusters, and wrapping.
//!
//! The vector profile measures in units of 1/64 px from the Inter advance
//! tables; the cell profile counts character cells from the Unicode width
//! tables. Both use integer arithmetic only. A measurement whose value leaves
//! the int32 range reports the kernel overflow error.

mod cell;
mod label;
mod segment;
mod width;
mod wrap;

#[cfg(test)]
mod conformance;

pub use cell::{cell_width, cluster_width};
pub use label::{StyledLine, StyledRun, styled_lines, styled_width};
pub use segment::{Cluster, segment};
pub use width::{
    Metric, Role, Weight, advance_sum, advance_units, apply_font_family_factor, upem, vector_width,
};
pub use wrap::{Line, default_wrap_width, wrap, wrap_target};

use crate::geom::{GeomError, floor_div, floor_mod};

pub(crate) fn narrow_i32(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

/// Rounds `a / b` up, for `b > 0`.
pub fn ceil_div(a: i64, b: i64) -> i64 {
    if b <= 0 {
        return 0;
    }
    let quotient = floor_div(a, b);
    if floor_mod(a, b) == 0 {
        quotient
    } else {
        quotient.saturating_add(1)
    }
}

/// Rounds `a / b` half up, for `b > 0`.
pub fn round_half_up(a: i64, b: i64) -> i64 {
    if b <= 0 {
        return 0;
    }
    let numerator = 2 * i128::from(a) + i128::from(b);
    let denominator = 2 * i128::from(b);
    narrow_i128(numerator.div_euclid(denominator))
}

fn narrow_i128(value: i128) -> i64 {
    match i64::try_from(value) {
        Ok(narrow) => narrow,
        Err(_) if value < 0 => i64::MIN,
        Err(_) => i64::MAX,
    }
}

#[cfg(test)]
mod tests {
    use super::{ceil_div, round_half_up};
    use crate::geom::floor_div;

    fn ceil_oracle(a: i128, b: i128) -> i128 {
        let quotient = a.div_euclid(b);
        if a.rem_euclid(b) == 0 {
            quotient
        } else {
            quotient + 1
        }
    }

    #[test]
    fn ceil_div_matches_hand_values() {
        assert_eq!(ceil_div(0, 4), 0);
        assert_eq!(ceil_div(1, 4), 1);
        assert_eq!(ceil_div(4, 4), 1);
        assert_eq!(ceil_div(5, 4), 2);
        assert_eq!(ceil_div(-1, 4), 0);
        assert_eq!(ceil_div(-4, 4), -1);
        assert_eq!(ceil_div(-5, 4), -1);
        assert_eq!(ceil_div(7, 0), 0);
    }

    #[test]
    fn ceil_div_matches_floor_definition() {
        for a in -200i64..200 {
            for b in 1i64..17 {
                let direct = ceil_div(a, b);
                let via_floor = floor_div(a + b - 1, b);
                assert_eq!(direct, via_floor, "a={a} b={b}");
                assert_eq!(
                    i128::from(direct),
                    ceil_oracle(i128::from(a), i128::from(b))
                );
            }
        }
    }

    #[test]
    fn round_half_up_matches_hand_values() {
        assert_eq!(round_half_up(0, 3), 0);
        assert_eq!(round_half_up(1, 3), 0);
        assert_eq!(round_half_up(2, 3), 1);
        assert_eq!(round_half_up(4, 3), 1);
        assert_eq!(round_half_up(5, 3), 2);
        assert_eq!(round_half_up(-1, 3), 0);
        assert_eq!(round_half_up(-2, 3), -1);
    }
}
