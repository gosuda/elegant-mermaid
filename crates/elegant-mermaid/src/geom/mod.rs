mod eval;
mod rect;
mod segment;
mod trig;

pub use eval::{CaseError, eval};
pub use rect::{compact, contains, inflate, intersects, isqrt, place_after, translate, union};
pub use segment::{count_inversions, is_orthogonal, polyline_hits_rect, segments_cross};
pub use trig::{cos_q15, sin_q15};

pub const I32_MIN: i64 = -2_147_483_648;
pub const I32_MAX: i64 = 2_147_483_647;
pub const COORD_LIMIT: i64 = 536_870_912;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size {
    pub w: i32,
    pub h: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rect {
    pub x: i32,
    pub y: i32,
    pub w: i32,
    pub h: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Axis {
    X,
    Y,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Segment {
    pub a: Point,
    pub b: Point,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum GeomError {
    #[error("overflow")]
    Overflow,
    #[error("domain")]
    Domain,
}

pub fn floor_div(a: i64, b: i64) -> i64 {
    if b == 0 {
        return 0;
    }
    narrow_i64(floor_quotient(i128::from(a), i128::from(b)))
}

pub fn floor_mod(a: i64, b: i64) -> i64 {
    if b == 0 {
        return 0;
    }
    let x = i128::from(a);
    let y = i128::from(b);
    narrow_i64(x - floor_quotient(x, y) * y)
}

fn floor_quotient(x: i128, y: i128) -> i128 {
    let magnitude = y.abs();
    let quotient = x.div_euclid(magnitude);
    let remainder = x.rem_euclid(magnitude);
    match (y > 0, remainder == 0) {
        (true, _) => quotient,
        (false, true) => -quotient,
        (false, false) => -quotient - 1,
    }
}

fn narrow_i64(value: i128) -> i64 {
    match i64::try_from(value) {
        Ok(wide) => wide,
        Err(_) => {
            if value < 0 {
                i64::MIN
            } else {
                i64::MAX
            }
        }
    }
}

pub(crate) fn checked_i32(value: i64) -> Result<i32, GeomError> {
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}

pub(crate) fn rect_is_valid(r: &Rect) -> bool {
    let x = i64::from(r.x);
    let y = i64::from(r.y);
    let w = i64::from(r.w);
    let h = i64::from(r.h);
    w >= 0 && h >= 0 && x + w >= I32_MIN && x + w <= I32_MAX && y + h >= I32_MIN && y + h <= I32_MAX
}

pub(crate) fn rect_from(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    let rect = Rect {
        x: checked_i32(x)?,
        y: checked_i32(y)?,
        w: checked_i32(w)?,
        h: checked_i32(h)?,
    };
    if rect_is_valid(&rect) {
        Ok(rect)
    } else {
        Err(GeomError::Overflow)
    }
}

#[cfg(test)]
pub(crate) mod testing {
    pub(crate) struct Xorshift32 {
        state: u32,
    }

    impl Xorshift32 {
        pub(crate) fn new(case: usize) -> Self {
            let seed = match u32::try_from(case) {
                Ok(value) => value.wrapping_add(1),
                Err(_) => u32::MAX,
            };
            Xorshift32 {
                state: if seed == 0 { 1 } else { seed },
            }
        }

        pub(crate) fn next_u32(&mut self) -> u32 {
            let mut x = self.state;
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            self.state = x;
            x
        }

        pub(crate) fn i32_in(&mut self, lo: i32, hi: i32) -> i32 {
            let low = i64::from(lo);
            let span = i64::from(hi) - low + 1;
            let width = u64::try_from(span).unwrap_or(1).max(1);
            let offset = i64::try_from(u64::from(self.next_u32()) % width).unwrap_or(0);
            i32::try_from(low + offset).unwrap_or(lo)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testing::Xorshift32;
    use super::{
        Axis, COORD_LIMIT, Point, Rect, Size, floor_div, floor_mod, rect_from, rect_is_valid,
    };

    fn truncation_quotient(x: i128, y: i128) -> i128 {
        x / y
    }

    fn floor_quotient_oracle(x: i128, y: i128) -> i128 {
        let mut quotient = truncation_quotient(x, y);
        if x % y != 0 && (x < 0) != (y < 0) {
            quotient -= 1;
        }
        quotient
    }

    #[test]
    fn xorshift_stream_is_deterministic() {
        let mut first = Xorshift32::new(0);
        let mut second = Xorshift32::new(0);
        for _ in 0..64 {
            assert_eq!(first.next_u32(), second.next_u32());
        }
        let mut third = Xorshift32::new(7);
        assert_ne!(third.next_u32(), Xorshift32::new(8).next_u32());
    }

    #[test]
    fn floor_helpers_match_truncation_adjustment() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let dividend = rng.i32_in(i32::MIN, i32::MAX);
            let divisor = rng.i32_in(-4096, 4096);
            if divisor == 0 {
                continue;
            }
            let quotient = floor_div(i64::from(dividend), i64::from(divisor));
            let remainder = floor_mod(i64::from(dividend), i64::from(divisor));
            let x = i128::from(dividend);
            let y = i128::from(divisor);
            assert_eq!(i128::from(quotient), floor_quotient_oracle(x, y));
            assert_eq!(i128::from(remainder), x - i128::from(quotient) * y);
            assert!(
                i128::from(remainder).abs() < y.abs(),
                "floor remainder magnitude must be below divisor magnitude: dividend={dividend}, divisor={divisor}, remainder={remainder}"
            );
            if y > 0 {
                assert!(
                    remainder >= 0 && i128::from(remainder) < y,
                    "positive divisor requires remainder in [0, divisor): divisor={divisor}, remainder={remainder}"
                );
            }
        }
    }

    #[test]
    fn floor_helpers_cover_hand_values() {
        assert_eq!(floor_div(7, 3), 2);
        assert_eq!(floor_div(-7, 3), -3);
        assert_eq!(floor_div(7, -3), -3);
        assert_eq!(floor_div(-7, -3), 2);
        assert_eq!(floor_div(6, -3), -2);
        assert_eq!(floor_div(-6, 3), -2);
        assert_eq!(floor_mod(7, 3), 1);
        assert_eq!(floor_mod(-7, 3), 2);
        assert_eq!(floor_mod(7, -3), -2);
        assert_eq!(floor_mod(-7, -3), -1);
        assert_eq!(floor_mod(-65536, 65536), 0);
        assert_eq!(floor_mod(-1, 65536), 65535);
        assert_eq!(floor_div(0, 5), 0);
    }

    #[test]
    fn rect_validity_matches_definition() {
        let valid = Rect {
            x: 0,
            y: 0,
            w: 10,
            h: 10,
        };
        assert!(
            rect_is_valid(&valid),
            "nonnegative rectangle with representable edges must be valid: {valid:?}"
        );
        assert!(
            rect_is_valid(&Rect {
                x: i32::MIN,
                y: i32::MIN,
                w: 0,
                h: 0,
            }),
            "zero-size rectangle at i32::MIN must be valid: x=y=i32::MIN, w=h=0"
        );
        assert!(
            !rect_is_valid(&Rect {
                x: 0,
                y: 0,
                w: -1,
                h: 0,
            }),
            "negative width must be invalid: x=y=h=0, w=-1"
        );
        assert!(
            !rect_is_valid(&Rect {
                x: 0,
                y: 0,
                w: 0,
                h: -1,
            }),
            "negative height must be invalid: x=y=w=0, h=-1"
        );
        assert!(
            !rect_is_valid(&Rect {
                x: i32::MAX,
                y: 0,
                w: 1,
                h: 0,
            }),
            "right edge beyond i32::MAX must be invalid: x=i32::MAX, w=1, y=h=0"
        );
    }

    #[test]
    fn rect_from_reports_overflow() {
        assert_eq!(
            rect_from(0, 0, 10, 10),
            Ok(Rect {
                x: 0,
                y: 0,
                w: 10,
                h: 10
            })
        );
        assert_eq!(
            rect_from(i64::from(i32::MAX), 0, 1, 0),
            Err(super::GeomError::Overflow)
        );
        assert_eq!(rect_from(0, 0, -1, 0), Err(super::GeomError::Overflow));
    }

    #[test]
    fn coordinate_limit_is_two_to_the_twenty_nine() {
        assert_eq!(COORD_LIMIT, 1 << 29);
        assert_eq!(i64::from(Point { x: 1, y: -1 }.x), 1);
        assert_eq!(Size { w: 3, h: 4 }.h, 4);
        assert_ne!(Axis::X, Axis::Y);
    }
}
