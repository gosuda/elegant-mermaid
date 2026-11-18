//! The gantt time axis: the d3-time automatic interval table, explicit `tickInterval`
//! rules, and tick generation on field multiples (`spec/layout/charts.md`, gantt).

use crate::civil;
use crate::geom::{floor_div, floor_mod};
use crate::measure;

use super::gantt::{DEFAULT_FORMAT, GanttPlan};

const AUTO_TICK_COUNT: i64 = 10;
const ISO_SUNDAY: i64 = 7;
const ISO_THURSDAY: i64 = 4;
const SECONDS_MIN: i64 = 60;
const SECONDS_HOUR: i64 = 3600;
const DAYS_PER_WEEK: i64 = 7;
const MONTHS_IN_YEAR: i64 = 12;
const HOURS_PER_DAY: i64 = 24;
const MILLIS_PER_UNIT: i64 = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TickUnit {
    Second,
    Minute,
    Hour,
    Day,
    Week,
    Month,
    Year,
}

#[derive(Debug, Clone, Copy)]
struct TickRule {
    unit: TickUnit,
    every: i64,
}

const fn rule(unit: TickUnit, every: i64) -> TickRule {
    TickRule { unit, every }
}

const AUTO_TICK_TABLE: [(i64, TickRule); 18] = [
    (1, rule(TickUnit::Second, 1)),
    (5, rule(TickUnit::Second, 5)),
    (15, rule(TickUnit::Second, 15)),
    (30, rule(TickUnit::Second, 30)),
    (60, rule(TickUnit::Minute, 1)),
    (300, rule(TickUnit::Minute, 5)),
    (900, rule(TickUnit::Minute, 15)),
    (1800, rule(TickUnit::Minute, 30)),
    (3600, rule(TickUnit::Hour, 1)),
    (10_800, rule(TickUnit::Hour, 3)),
    (21_600, rule(TickUnit::Hour, 6)),
    (43_200, rule(TickUnit::Hour, 12)),
    (86_400, rule(TickUnit::Day, 1)),
    (172_800, rule(TickUnit::Day, 2)),
    (604_800, rule(TickUnit::Week, 1)),
    (2_592_000, rule(TickUnit::Month, 1)),
    (7_776_000, rule(TickUnit::Month, 3)),
    (31_536_000, rule(TickUnit::Year, 1)),
];

const EXPLICIT_UNITS: [(&str, TickUnit, i64); 6] = [
    ("second", TickUnit::Second, 1000),
    ("minute", TickUnit::Minute, 60_000),
    ("hour", TickUnit::Hour, 3_600_000),
    ("day", TickUnit::Day, 86_400_000),
    ("week", TickUnit::Week, 604_800_000),
    ("month", TickUnit::Month, 2_628_000_000),
];

fn auto_tick_rule(span: i64) -> TickRule {
    let last = AUTO_TICK_TABLE.len() - 1;
    let i = AUTO_TICK_TABLE
        .iter()
        .position(|(seconds, _)| seconds * AUTO_TICK_COUNT > span)
        .unwrap_or(AUTO_TICK_TABLE.len());
    if i == 0 {
        return AUTO_TICK_TABLE[0].1;
    }
    if i > last {
        return AUTO_TICK_TABLE[last].1;
    }
    let squared = i128::from(span) * i128::from(span);
    let product = i128::from(AUTO_TICK_COUNT * AUTO_TICK_COUNT)
        * i128::from(AUTO_TICK_TABLE[i - 1].0)
        * i128::from(AUTO_TICK_TABLE[i].0);
    if squared < product {
        AUTO_TICK_TABLE[i - 1].1
    } else {
        AUTO_TICK_TABLE[i].1
    }
}

struct TickSink {
    out: Vec<i64>,
    lo: i64,
    hi: i64,
    limit: usize,
    capped: bool,
}

impl TickSink {
    fn add(&mut self, t: i64) -> bool {
        if t > self.hi {
            return false;
        }
        if t < self.lo {
            return true;
        }
        if self.out.len() == self.limit {
            self.capped = true;
            return false;
        }
        self.out.push(t);
        true
    }

    fn fields(&mut self, block_seconds: i64, block_width: i64, step: i64, unit_seconds: i64) {
        let mut start = floor_div(self.lo, block_seconds) * block_seconds;
        loop {
            let mut j = 0;
            while j < block_width {
                if !self.add(start + j * unit_seconds) {
                    return;
                }
                j += step;
            }
            start += block_seconds;
        }
    }

    fn days(&mut self, step: i64) {
        let f = civil::split(self.lo);
        let (mut y, mut m) = (f.year, f.month);
        loop {
            let mut d = 1;
            while d <= civil::days_in_month(y, m) {
                if !self.add(civil::days_from_civil(y, m, d) * civil::SECONDS_PER_DAY) {
                    return;
                }
                d += step;
            }
            (y, m) = if m == MONTHS_IN_YEAR {
                (y + 1, 1)
            } else {
                (y, m + 1)
            };
        }
    }

    fn weeks(&mut self, step: i64, weekday: i64) {
        let shift = floor_mod(ISO_THURSDAY - weekday, DAYS_PER_WEEK);
        let days = measure::ceil_div(self.lo, civil::SECONDS_PER_DAY);
        let mut count =
            measure::ceil_div(measure::ceil_div(days + shift, DAYS_PER_WEEK), step) * step;
        loop {
            if !self.add((count * DAYS_PER_WEEK - shift) * civil::SECONDS_PER_DAY) {
                return;
            }
            count += step;
        }
    }

    fn months(&mut self, step: i64) {
        let mut y = civil::split(self.lo).year;
        loop {
            let mut m = 0;
            while m < MONTHS_IN_YEAR {
                if !self.add(civil::days_from_civil(y, m + 1, 1) * civil::SECONDS_PER_DAY) {
                    return;
                }
                m += step;
            }
            y += 1;
        }
    }

    fn years(&mut self) {
        let mut y = civil::split(self.lo).year;
        loop {
            if !self.add(civil::days_from_civil(y, 1, 1) * civil::SECONDS_PER_DAY) {
                return;
            }
            y += 1;
        }
    }

    fn run(&mut self, rule: TickRule, weekday: i64) {
        match rule.unit {
            TickUnit::Second => self.fields(SECONDS_MIN, SECONDS_MIN, rule.every, 1),
            TickUnit::Minute => self.fields(SECONDS_HOUR, SECONDS_MIN, rule.every, SECONDS_MIN),
            TickUnit::Hour => self.fields(
                civil::SECONDS_PER_DAY,
                HOURS_PER_DAY,
                rule.every,
                SECONDS_HOUR,
            ),
            TickUnit::Day => self.days(rule.every),
            TickUnit::Week => self.weeks(rule.every, weekday),
            TickUnit::Month => self.months(rule.every),
            TickUnit::Year => self.years(),
        }
    }
}

impl GanttPlan<'_> {
    fn tick_rule(&self) -> (TickRule, i64) {
        let g = self.g;
        let span = (self.d1 - self.d0).abs();
        let Some((_, unit, millis)) = EXPLICIT_UNITS
            .iter()
            .find(|(name, _, _)| *name == g.tick_unit)
            .filter(|_| g.tick_every > 0)
        else {
            return (auto_tick_rule(span), ISO_SUNDAY);
        };
        if measure::ceil_div(span * MILLIS_PER_UNIT, g.tick_every * millis) > self.c.estimate_cap {
            return (auto_tick_rule(span), ISO_SUNDAY);
        }
        let weekday = civil::weekday_index(&g.weekday).unwrap_or(ISO_SUNDAY);
        (rule(*unit, g.tick_every), weekday)
    }

    pub(super) fn compute_ticks(&mut self) {
        let (rule, weekday) = self.tick_rule();
        let mut sink = TickSink {
            out: Vec::new(),
            lo: self.d0.min(self.d1),
            hi: self.d0.max(self.d1),
            limit: usize::try_from(self.c.tick_cap).unwrap_or(0),
            capped: false,
        };
        sink.run(rule, weekday);
        self.capped = sink.capped;
        self.ticks = sink.out;
        if self.d1 < self.d0 {
            self.ticks.reverse();
        }
        let format = if self.g.axis_form.is_empty() {
            DEFAULT_FORMAT
        } else {
            self.g.axis_form.as_str()
        };
        self.tick_text = self
            .ticks
            .iter()
            .map(|&t| {
                let (text, unsupported) = civil::format(t, format);
                if unsupported.is_empty() {
                    text
                } else {
                    civil::format(t, DEFAULT_FORMAT).0
                }
            })
            .collect();
    }
}
