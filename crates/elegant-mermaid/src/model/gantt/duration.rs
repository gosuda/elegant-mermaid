//! Task duration literals (`30d`, `1.5h`, `2w`) and their addition to an instant.

use crate::civil;

const FRAC_DIGITS: usize = 15;
const FRAC_SCALE: i64 = 1_000_000_000_000_000;
const WHOLE_SAT: i64 = 100_000_000_000_000_000;
const MAX_DAYS: i64 = 200_000_000;
const MAX_SECONDS: i64 = 10_000_000_000_000;
const MAX_COUNT: i64 = 1_000_000_000;

const DURATION_UNITS: [&str; 8] = ["M", "d", "h", "m", "s", "w", "y", "ms"];

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Decimal {
    whole: i64,
    frac: i64,
}

pub(super) fn valid_seconds(s: i64) -> bool {
    (-civil::MAX_ABS_SECONDS..=civil::MAX_ABS_SECONDS).contains(&s)
}

fn scan_whole(text: &[u8], d: &mut Decimal) -> usize {
    let mut i = 0;
    while let Some(&c) = text.get(i).filter(|c| c.is_ascii_digit()) {
        d.whole = (d.whole * 10 + i64::from(c - b'0')).min(WHOLE_SAT);
        i += 1;
    }
    i
}

fn scan_fraction(text: &[u8], mut i: usize, d: &mut Decimal) -> (usize, bool) {
    if text.get(i) != Some(&b'.') {
        return (i, true);
    }
    i += 1;
    let start = i;
    while let Some(&c) = text.get(i).filter(|c| c.is_ascii_digit()) {
        if i - start < FRAC_DIGITS {
            d.frac = d.frac * 10 + i64::from(c - b'0');
        }
        i += 1;
    }
    for _ in (i - start)..FRAC_DIGITS {
        d.frac *= 10;
    }
    (i, i > start)
}

pub(super) fn parse_duration(text: &str) -> Option<(Decimal, &'static str)> {
    let bytes = text.as_bytes();
    let mut d = Decimal::default();
    let i = scan_whole(bytes, &mut d);
    if i == 0 {
        return None;
    }
    let (i, ok) = scan_fraction(bytes, i, &mut d);
    let unit = text.get(i..)?;
    let unit = DURATION_UNITS
        .iter()
        .find(|candidate| **candidate == unit)?;
    ok.then_some((d, *unit))
}

impl Decimal {
    fn scaled(self, n: i64) -> i64 {
        self.whole * n + (self.frac * n + FRAC_SCALE / 2) / FRAC_SCALE
    }

    fn seconds(self, factor: i64) -> Option<i64> {
        (self.whole <= MAX_SECONDS).then(|| self.whole * factor + self.frac * factor / FRAC_SCALE)
    }
}

fn days_to_seconds(days: i64) -> Option<i64> {
    (days <= MAX_DAYS).then(|| days * civil::SECONDS_PER_DAY)
}

fn year_delta(prev: i64, d: Decimal) -> i64 {
    let year = civil::split(prev).year;
    let mut base = year + d.whole;
    if base < 0 && d.frac > 0 {
        base += 1;
    }
    base - year
}

fn calendar_add(prev: i64, count: i64, months_each: i64) -> Option<i64> {
    if count.abs() > MAX_COUNT {
        return None;
    }
    let end = civil::clamped_month_add(prev, count * months_each);
    valid_seconds(end).then_some(end)
}

pub(super) fn add_duration(prev: i64, d: Decimal, unit: &str) -> Option<i64> {
    let delta = match unit {
        "d" => days_to_seconds(d.scaled(1)),
        "w" => days_to_seconds(d.scaled(7)),
        "h" => d.seconds(3600),
        "m" => d.seconds(60),
        "s" => d.seconds(1),
        "ms" => Some(d.whole / 1000),
        "M" => return calendar_add(prev, d.whole, 1),
        _ => return calendar_add(prev, year_delta(prev, d), 12),
    }?;
    let end = prev + delta;
    valid_seconds(end).then_some(end)
}
