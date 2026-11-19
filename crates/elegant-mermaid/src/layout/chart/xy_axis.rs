//! One axis of the xychart plan: its domain, ticks, labels, space, and positions.

use std::collections::BTreeMap;

use crate::geom::{GeomError, floor_div};
use crate::model::chart::{Point, Xy};

use super::scale::{self, Linear};
use super::xy_spec::LabelKind;
use super::{Area, LayoutError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum Position {
    #[default]
    Bottom,
    Left,
    Top,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct BandSpace {
    pub w: i64,
    pub h: i64,
    pub line: i64,
    pub tick: i64,
    pub title: i64,
    pub show_label: bool,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Axis {
    pub position: Position,
    pub band: bool,
    pub distinct: Vec<usize>,
    pub n: usize,
    pub lo: i64,
    pub hi: i64,
    pub ticks: Vec<i64>,
    pub labels: Vec<String>,
    pub show_labels: bool,
    pub font_size: i32,
    pub outer: i64,
    pub r0: i64,
    pub r1: i64,
    pub space: BandSpace,
    pub area: Area,
    pub label_w: i64,
    pub label_h: i64,
    pub tick_kind: LabelKind,
    pub title_kind: LabelKind,
}

impl Axis {
    pub(crate) fn count(&self) -> usize {
        self.labels.len()
    }

    pub(crate) fn inner_range(&self) -> (i64, i64) {
        (self.r0 + self.outer, self.r1 - self.outer)
    }

    pub(crate) fn tick_distance(&self) -> i64 {
        if self.count() == 0 {
            return 0;
        }
        let (lo, hi) = self.inner_range();
        floor_div(
            (hi - lo).abs(),
            i64::try_from(self.count()).unwrap_or(i64::MAX),
        )
    }

    pub(crate) fn raise_outer_for_bars(&mut self, ratio: i64) {
        let distance = self.tick_distance();
        if ratio * distance > 2000 * self.outer {
            self.outer = floor_div(ratio * distance, 2000);
        }
    }

    fn band_index(&self, slot: Option<usize>) -> Option<usize> {
        self.distinct.get(slot?).copied()
    }

    fn linear(&self) -> Linear {
        let (lo, hi) = self.inner_range();
        let (d0, d1) = if self.position == Position::Left {
            (self.hi, self.lo)
        } else {
            (self.lo, self.hi)
        };
        Linear {
            d0,
            d1,
            r0: lo,
            r1: hi,
        }
    }

    fn clamp_position(&self, value: i64, edge: i64) -> i64 {
        scale::clamp(value, self.r0, self.r1 - edge)
    }

    fn band_position(&self, slot: Option<usize>, edge: i64) -> i64 {
        let (lo, hi) = self.inner_range();
        match self.band_index(slot) {
            Some(index) => self.clamp_position(scale::band_position(index, self.n, lo, hi), edge),
            None => self.clamp_position(lo, edge),
        }
    }

    pub(crate) fn value_position(&self, value: i64, edge: i64) -> i64 {
        let clamped = scale::clamp(value, self.lo, self.hi);
        self.clamp_position(self.linear().map(clamped), edge)
    }

    pub(crate) fn point_position(&self, point: &Point, edge: i64) -> i64 {
        if self.band {
            return self.band_position(point.slot, edge);
        }
        if !point.has_x {
            return self.clamp_position(self.r0 + self.outer, edge);
        }
        self.value_position(point.x, edge)
    }

    pub(crate) fn tick_position(&self, k: usize, edge: i64) -> i64 {
        if self.band {
            self.band_position(Some(k), edge)
        } else {
            self.value_position(self.ticks[k], edge)
        }
    }
}

fn distinct_index(categories: &[String]) -> (Vec<usize>, usize) {
    let mut first: BTreeMap<&str, usize> = BTreeMap::new();
    let mut out = Vec::with_capacity(categories.len());
    for name in categories {
        let next = first.len();
        out.push(*first.entry(name.as_str()).or_insert(next));
    }
    (out, first.len())
}

pub(crate) fn check_magnitude(values: &[i64]) -> Result<(), LayoutError> {
    let limit = i64::from(i32::MAX);
    if values.iter().any(|v| v.abs() > limit) {
        return Err(GeomError::Overflow);
    }
    Ok(())
}

fn linear_axis(lo: i64, hi: i64) -> Result<(Axis, bool), LayoutError> {
    check_magnitude(&[lo, hi])?;
    let ticks = scale::ticks(lo, hi)?;
    let labels = ticks
        .values
        .iter()
        .map(|t| scale::format_number(*t))
        .collect();
    let axis = Axis {
        lo,
        hi,
        ticks: ticks.values,
        labels,
        ..Axis::default()
    };
    Ok((axis, ticks.capped))
}

pub(crate) fn new_axes(xy: &Xy) -> Result<(Axis, Axis, bool), LayoutError> {
    let (y, capped) = linear_axis(xy.y_axis.min, xy.y_axis.max)?;
    if xy.x_axis.band {
        let categories = &xy.x_axis.categories;
        let (distinct, n) = distinct_index(categories);
        let x = Axis {
            band: true,
            distinct,
            n,
            labels: categories.clone(),
            ..Axis::default()
        };
        return Ok((x, y, capped));
    }
    let (x, x_capped) = linear_axis(xy.x_axis.min, xy.x_axis.max)?;
    Ok((x, y, capped || x_capped))
}
