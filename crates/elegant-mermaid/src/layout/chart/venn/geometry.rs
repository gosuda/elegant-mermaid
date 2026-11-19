//! The venn circle geometry: radii from sizes, the two-set distance by bisection over the
//! pi-free lens area, and the fixed centres of one, two, and three sets
//! (`spec/layout/charts.md`). Areas are signed 128-bit integers.

use crate::geom::{GeomError, cos_q15, floor_div, isqrt, sin_q15};

use super::super::LayoutError;
use super::super::scale::clamp;

const HALF_TURN: i64 = 32768;
const Q15: i64 = 32768;
const LENS_TURN: i64 = 131_072;
const LENS_SINE: i64 = 20861;
const AREA_SHIFT: u32 = 32;

#[derive(Debug, Clone, Copy)]
pub(super) struct Steps {
    pub acos: usize,
    pub bisect: usize,
    pub sqrt3_half: i64,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Circle {
    pub x: i64,
    pub y: i64,
    pub r: i64,
}

fn product(a: i64, b: i64) -> i128 {
    i128::from(a) * i128::from(b)
}

pub(super) fn largest(sizes: &[i64]) -> i64 {
    sizes.iter().fold(1, |acc, size| acc.max(*size))
}

pub(super) fn radii(sizes: &[i64], largest: i64, radius: i64) -> Result<Vec<i64>, LayoutError> {
    sizes
        .iter()
        .map(|size| {
            let scaled = product(radius, radius) * i128::from((*size).max(0));
            let quotient = scaled / i128::from(largest);
            isqrt(i64::try_from(quotient).map_err(|_| GeomError::Overflow)?)
        })
        .collect()
}

fn arccos(x: i64, steps: usize) -> i64 {
    let (mut lo, mut hi) = (0i64, HALF_TURN);
    for _ in 0..steps {
        let mid = floor_div(lo + hi + 1, 2);
        let angle = i32::try_from(mid).unwrap_or(i32::MAX);
        if i64::from(cos_q15(angle)) >= x {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

fn half_chord(d: i64, own: i64, other: i64, steps: usize) -> i64 {
    let x = floor_div((d * d + own * own - other * other) * Q15, 2 * d * own);
    arccos(clamp(x, -Q15, Q15), steps)
}

fn lens_area(d: i64, r1: i64, r2: i64, steps: usize) -> i128 {
    let mut area = 0i128;
    for (own, other) in [(r1, r2), (r2, r1)] {
        let u = half_chord(d, own, other, steps);
        let angle = i32::try_from(2 * u).unwrap_or(i32::MAX);
        let turn = LENS_TURN * u - LENS_SINE * i64::from(sin_q15(angle));
        area += product(own * own, turn);
    }
    area
}

pub(super) fn distance(r1: i64, r2: i64, target: i128, steps: Steps) -> i64 {
    let (mut lo, mut hi) = ((r1 - r2).abs(), r1 + r2);
    let smaller = r1.min(r2);
    let contained = product(smaller, smaller);
    if contained <= target {
        return lo;
    }
    if target == 0 {
        return hi;
    }
    let want = target << AREA_SHIFT;
    for _ in 0..steps.bisect {
        let mid = floor_div(lo + hi, 2);
        if overlap_greater(mid, (r1, r2), contained, want, steps.acos) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    floor_div(lo + hi, 2)
}

fn overlap_greater(d: i64, radii: (i64, i64), contained: i128, want: i128, acos: usize) -> bool {
    if d == 0 {
        return contained << AREA_SHIFT > want;
    }
    lens_area(d, radii.0, radii.1, acos) > want
}

pub(super) fn target(overlap: i64, largest: i64, radius: i64) -> i128 {
    product(radius, radius) * i128::from(overlap.max(0)) / i128::from(largest.max(1))
}

pub(super) fn centres(radii: &[i64], radius: i64, distance: i64, steps: Steps) -> Vec<Circle> {
    let mut out: Vec<Circle> = radii
        .iter()
        .map(|r| Circle {
            r: *r,
            ..Circle::default()
        })
        .collect();
    let middle = 2 * radius;
    match out.as_mut_slice() {
        [only] => (only.x, only.y) = (middle, middle),
        [first, second] => {
            first.x = middle - floor_div(distance, 2);
            first.y = middle;
            second.x = first.x + distance;
            second.y = middle;
        }
        [first, second, third, ..] => {
            let dx = floor_div(radius * steps.sqrt3_half, Q15);
            let low = middle + floor_div(radius, 2);
            (first.x, first.y) = (middle, radius);
            (second.x, second.y) = (middle + dx, low);
            (third.x, third.y) = (middle - dx, low);
        }
        [] => {}
    }
    out
}
