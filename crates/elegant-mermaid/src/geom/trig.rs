use super::{floor_div, floor_mod};

pub fn sin_q15(a: i32) -> i32 {
    let angle = floor_mod(i64::from(a), 65_536);
    let quadrant = floor_div(angle, 16_384);
    let unit = angle - 16_384 * quadrant;
    match quadrant {
        0 => interpolate(unit),
        1 => interpolate(16_384 - unit),
        2 => -interpolate(unit),
        _ => -interpolate(16_384 - unit),
    }
}

pub fn cos_q15(a: i32) -> i32 {
    sin_q15(wrap_angle(i64::from(a) + 16_384))
}

fn wrap_angle(angle: i64) -> i32 {
    let reduced = floor_mod(angle, 65_536);
    i32::try_from(reduced).unwrap_or(0)
}

fn interpolate(k: i64) -> i32 {
    let index = floor_div(k, 16);
    let fraction = k - 16 * index;
    let low = table(index);
    if fraction == 0 {
        return low;
    }
    let high = table(index + 1);
    let rise = (i64::from(high) - i64::from(low)) * fraction + 8;
    let delta = floor_div(rise, 16);
    i32::try_from(i64::from(low) + delta).unwrap_or(low)
}

fn table(index: i64) -> i32 {
    usize::try_from(index)
        .ok()
        .and_then(|i| crate::r#gen::sine::SINE_TABLE.get(i).copied())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::super::testing::Xorshift32;
    use super::{cos_q15, sin_q15};
    use crate::r#gen::sine::SINE_TABLE;

    fn table_sine(index: usize) -> i32 {
        SINE_TABLE[index]
    }

    fn sine_oracle(angle: i64) -> i32 {
        let r = angle.rem_euclid(65536);
        let q = r / 16384;
        let u = r % 16384;
        let k = if q % 2 == 0 { u } else { 16384 - u };
        let i = usize::try_from(k / 16).unwrap_or(0);
        let f = k % 16;
        let low = i64::from(SINE_TABLE[i]);
        let value = if f == 0 {
            low
        } else {
            low + ((i64::from(SINE_TABLE[i + 1]) - low) * f + 8) / 16
        };
        i32::try_from(if q < 2 { value } else { -value }).unwrap_or(0)
    }

    #[test]
    fn trig_matches_direct_specification() {
        for angle in [i32::MIN, -1, 0, 1, i32::MAX] {
            assert_eq!(sin_q15(angle), sine_oracle(i64::from(angle)));
            assert_eq!(cos_q15(angle), sine_oracle(i64::from(angle) + 16384));
        }
        for case in 0..2000 {
            let mut rng = Xorshift32::new(case);
            let angle = rng.i32_in(i32::MIN, i32::MAX);
            assert_eq!(sin_q15(angle), sine_oracle(i64::from(angle)));
            assert_eq!(cos_q15(angle), sine_oracle(i64::from(angle) + 16384));
        }
    }

    #[test]
    fn quarter_turn_values() {
        assert_eq!(sin_q15(0), 0);
        assert_eq!(sin_q15(16_384), 32_768);
        assert_eq!(sin_q15(32_768), 0);
        assert_eq!(sin_q15(49_152), -32_768);
        assert_eq!(sin_q15(-16_384), -32_768);
        assert_eq!(sin_q15(65_536), 0);
        assert_eq!(sin_q15(-65_536), 0);
        assert_eq!(sin_q15(i32::MIN), sin_q15(-1_073_741_824));
        assert_eq!(sin_q15(-49_152), 32_768);
    }

    #[test]
    fn table_entries_are_sampled_at_multiples_of_sixteen() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let index = usize::try_from(rng.i32_in(0, 1022)).unwrap_or(0);
            let angle = i32::try_from(index).unwrap_or(0) * 16;
            assert_eq!(sin_q15(angle), table_sine(index), "case {case}");
        }
    }

    #[test]
    fn periodicity_and_odd_symmetry() {
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let angle = rng.i32_in(-200_000, 200_000);
            let base = sin_q15(angle);
            assert_eq!(sin_q15(angle.wrapping_add(65_536)), base, "case {case}");
            assert_eq!(sin_q15(angle.wrapping_sub(131_072)), base, "case {case}");
            let mirrored = angle.wrapping_neg();
            let quarter_turn = floor_mod_for_test(i64::from(mirrored), 65_536);
            if quarter_turn != 0 && quarter_turn != 32_768 {
                assert_eq!(sin_q15(mirrored), -base, "case {case}");
            }
        }
    }

    fn floor_mod_for_test(a: i64, m: i64) -> i64 {
        let remainder = a % m;
        if remainder < 0 {
            remainder + m
        } else {
            remainder
        }
    }

    #[test]
    fn result_stays_in_range_and_is_monotone_on_the_first_quadrant() {
        let mut previous = sin_q15(0);
        let mut angle = 16;
        while angle <= 16_384 {
            let value = sin_q15(angle);
            assert!(
                value >= previous,
                "first-quadrant sine must be monotone: angle={angle}, previous={previous}, value={value}"
            );
            assert!(
                (-32_768..=32_768).contains(&value),
                "Q15 sine must stay in [-32768, 32768]: angle={angle}, value={value}"
            );
            previous = value;
            angle += 16;
        }
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let angle = rng.i32_in(-200_000, 200_000);
            let value = sin_q15(angle);
            assert!(
                (-32_768..=32_768).contains(&value),
                "Q15 sine must stay in [-32768, 32768]: angle={angle}, value={value}"
            );
        }
    }

    #[test]
    fn cosine_is_shifted_sine() {
        assert_eq!(cos_q15(0), 32_768);
        assert_eq!(cos_q15(16_384), 0);
        assert_eq!(cos_q15(-16_384), 0);
        assert_eq!(cos_q15(8_192), sin_q15(24_576));
        for case in 0..2000usize {
            let mut rng = Xorshift32::new(case);
            let angle = rng.i32_in(-200_000, 200_000);
            let shifted = i32::try_from(i64::from(angle) + 16_384).unwrap_or(0);
            assert_eq!(cos_q15(angle), sin_q15(shifted), "case {case}");
        }
    }
}
