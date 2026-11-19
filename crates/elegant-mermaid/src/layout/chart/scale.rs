//! Integer scales of the chart family: linear maps, band positions, the d3 tick rule,
//! and number formatting. Every value is an `i64` in thousandths or in profile units.

use crate::geom::{GeomError, floor_div};

use super::super::layered::LayoutError;

const TICK_COUNT: u64 = 10;
const TICK_CAP: usize = 64;
const SCAN_CAP: u32 = 40;
const SCALE: i64 = 1000;
const STEP_MULTIPLES: [(u64, u64); 3] = [(50, 10), (10, 5), (2, 2)];

#[derive(Debug, Clone, Copy)]
pub struct Linear {
    pub d0: i64,
    pub d1: i64,
    pub r0: i64,
    pub r1: i64,
}

impl Linear {
    pub fn map(self, value: i64) -> i64 {
        if self.d1 == self.d0 {
            return floor_div(self.r0 + self.r1, 2);
        }
        self.r0 + floor_div((value - self.d0) * (self.r1 - self.r0), self.d1 - self.d0)
    }
}

pub fn band_position(index: usize, count: usize, r0: i64, r1: i64) -> i64 {
    let span = r1 - r0;
    if count < 2 {
        return r0 + floor_div(span, 2);
    }
    let numerator = i64::try_from(index).unwrap_or(i64::MAX) * span;
    r0 + floor_div(numerator, i64::try_from(count - 1).unwrap_or(i64::MAX))
}

pub fn clamp(value: i64, a: i64, b: i64) -> i64 {
    value.min(a.max(b)).max(a.min(b))
}

fn power_of_ten(exponent: u32) -> u64 {
    10u64.saturating_pow(exponent)
}

fn at_least(d2: u64, s2: u64, factor: u64) -> bool {
    u128::from(d2) >= u128::from(s2) * u128::from(factor)
}

fn tick_step(d: u64) -> i64 {
    if d < TICK_COUNT {
        return 1;
    }
    let mut p = 1u64;
    for exponent in 0..SCAN_CAP / 2 {
        if power_of_ten(exponent).saturating_mul(TICK_COUNT) > d {
            break;
        }
        p = power_of_ten(exponent);
    }
    let s2 = TICK_COUNT * TICK_COUNT * p * p;
    let d2 = d * d;
    let step = STEP_MULTIPLES
        .iter()
        .find(|(threshold, _)| at_least(d2, s2, *threshold))
        .map_or(p, |(_, multiple)| multiple * p);
    i64::try_from(step).unwrap_or(i64::MAX)
}

pub struct Ticks {
    pub values: Vec<i64>,
    pub capped: bool,
}

pub fn ticks(lo: i64, hi: i64) -> Result<Ticks, LayoutError> {
    let span = (hi - lo).abs();
    if span > i64::from(i32::MAX) {
        return Err(GeomError::Overflow);
    }
    if span == 0 {
        return Ok(Ticks {
            values: vec![lo],
            capped: false,
        });
    }
    let step = tick_step(span.unsigned_abs());
    let (first, last) = (lo.min(hi), lo.max(hi));
    let mut values = Vec::new();
    let mut capped = false;
    let mut at = -floor_div(-first, step) * step;
    while at <= last {
        if values.len() == TICK_CAP {
            capped = true;
            break;
        }
        values.push(at);
        at += step;
    }
    if lo > hi {
        values.reverse();
    }
    Ok(Ticks { values, capped })
}

pub fn format_number(thousandths: i64) -> String {
    let sign = if thousandths < 0 { "-" } else { "" };
    let magnitude = thousandths.abs();
    let whole = magnitude / SCALE;
    let fraction = magnitude % SCALE;
    if fraction == 0 {
        return format!("{sign}{whole}");
    }
    let digits = format!("{:03}", fraction);
    format!("{sign}{whole}.{}", digits.trim_end_matches('0'))
}
