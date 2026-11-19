//! Integer proleptic Gregorian calendar: civil dates, ISO weekdays, ISO weeks, month
//! arithmetic with day clamping, strftime-style formatting, and the gantt exclusion
//! calendar. Dates are naive; the module never reads the clock.

use std::collections::BTreeSet;

pub const SECONDS_PER_DAY: i64 = 86_400;
pub const MAX_ABS_SECONDS: i64 = 8_640_000_000_000;
const MONTHS_PER_YEAR: i64 = 12;
const DAYS_PER_ERA: i64 = 146_097;
const EPOCH_SHIFT_DAYS: i64 = 719_468;
const WEEKDAY_COUNT: usize = 7;

const WEEKDAY_IDS: [&str; WEEKDAY_COUNT + 1] = [
    "",
    "monday",
    "tuesday",
    "wednesday",
    "thursday",
    "friday",
    "saturday",
    "sunday",
];

const MONTH_ABBREV: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];

const WEEKDAY_ABBREV: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];

pub fn floor_div(a: i64, b: i64) -> i64 {
    let q = a / b;
    if a % b != 0 && (a < 0) != (b < 0) {
        q - 1
    } else {
        q
    }
}

pub fn floor_mod(a: i64, b: i64) -> i64 {
    a - floor_div(a, b) * b
}

pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = floor_div(y, 400);
    let yoe = y - era * 400;
    let shifted = if m > 2 { m - 3 } else { m + 9 };
    let doy = (153 * shifted + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * DAYS_PER_ERA + doe - EPOCH_SHIFT_DAYS
}

pub fn civil_from_days(z: i64) -> (i64, i64, i64) {
    let z = z + EPOCH_SHIFT_DAYS;
    let era = floor_div(z, DAYS_PER_ERA);
    let doe = z - era * DAYS_PER_ERA;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp >= 10 { mp - 9 } else { mp + 3 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

pub fn is_leap(y: i64) -> bool {
    floor_mod(y, 4) == 0 && (floor_mod(y, 100) != 0 || floor_mod(y, 400) == 0)
}

pub fn days_in_month(y: i64, m: i64) -> i64 {
    match m {
        2 if is_leap(y) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

pub fn iso_weekday(days: i64) -> i64 {
    floor_mod(days + 3, 7) + 1
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fields {
    pub year: i64,
    pub month: i64,
    pub day: i64,
    pub hour: i64,
    pub minute: i64,
    pub second: i64,
    pub days: i64,
    pub weekday: i64,
    pub second_of_day: i64,
}

pub fn split(seconds: i64) -> Fields {
    let days = floor_div(seconds, SECONDS_PER_DAY);
    let rest = seconds - days * SECONDS_PER_DAY;
    let (year, month, day) = civil_from_days(days);
    Fields {
        year,
        month,
        day,
        hour: rest / 3600,
        minute: rest % 3600 / 60,
        second: rest % 60,
        days,
        weekday: iso_weekday(days),
        second_of_day: rest,
    }
}

pub fn join(y: i64, m: i64, d: i64, hh: i64, mm: i64, ss: i64) -> i64 {
    days_from_civil(y, m, d) * SECONDS_PER_DAY + hh * 3600 + mm * 60 + ss
}

pub fn clamped_month_add(seconds: i64, months: i64) -> i64 {
    let f = split(seconds);
    let index = f.year * MONTHS_PER_YEAR + (f.month - 1) + months;
    let y = floor_div(index, MONTHS_PER_YEAR);
    let m = floor_mod(index, MONTHS_PER_YEAR) + 1;
    join(
        y,
        m,
        f.day.min(days_in_month(y, m)),
        f.hour,
        f.minute,
        f.second,
    )
}

pub fn iso_week(days: i64) -> (i64, i64) {
    let thursday = days + 4 - iso_weekday(days);
    let (y, _, _) = civil_from_days(thursday);
    ((thursday - days_from_civil(y, 1, 1)) / 7 + 1, y)
}

pub fn weekday_index(id: &str) -> Option<i64> {
    (1..=WEEKDAY_COUNT)
        .find(|&i| WEEKDAY_IDS.get(i) == Some(&id))
        .and_then(|i| i64::try_from(i).ok())
}

fn decimal_field(text: &[u8]) -> Option<i64> {
    let mut n = 0_i64;
    for &c in text {
        if !c.is_ascii_digit() {
            return None;
        }
        n = n * 10 + i64::from(c - b'0');
    }
    Some(n)
}

fn valid_date(y: i64, m: i64, d: i64) -> bool {
    (1..=12).contains(&m) && d >= 1 && d <= days_in_month(y, m)
}

fn iso_day_token(token: &str) -> Option<i64> {
    let b = token.as_bytes();
    if b.len() != 10 || b.get(4) != Some(&b'-') || b.get(7) != Some(&b'-') {
        return None;
    }
    let y = decimal_field(b.get(0..4)?)?;
    let m = decimal_field(b.get(5..7)?)?;
    let d = decimal_field(b.get(8..10)?)?;
    valid_date(y, m, d).then(|| days_from_civil(y, m, d))
}

#[derive(Debug, Clone)]
pub struct Calendar {
    weekends: bool,
    weekend_start: i64,
    named: [bool; WEEKDAY_COUNT + 1],
    excluded_days: BTreeSet<i64>,
    included_days: BTreeSet<i64>,
}

impl Calendar {
    pub fn new(excludes: &[String], includes: &[String], weekend: &str) -> Self {
        let mut c = Self {
            weekends: false,
            weekend_start: if weekend == "friday" { 5 } else { 6 },
            named: [false; WEEKDAY_COUNT + 1],
            excluded_days: BTreeSet::new(),
            included_days: BTreeSet::new(),
        };
        for token in excludes {
            if token == "weekends" {
                c.weekends = true;
            }
            if let Some(wd) = weekday_index(token)
                && let Some(slot) = usize::try_from(wd).ok().and_then(|i| c.named.get_mut(i))
            {
                *slot = true;
            }
            if let Some(day) = iso_day_token(token) {
                c.excluded_days.insert(day);
            }
        }
        for token in includes {
            if let Some(day) = iso_day_token(token) {
                c.included_days.insert(day);
            }
        }
        c
    }

    pub fn excluded(&self, day: i64) -> bool {
        if self.included_days.contains(&day) {
            return false;
        }
        let wd = iso_weekday(day);
        if self.weekends && (wd == self.weekend_start || wd == self.weekend_start + 1) {
            return true;
        }
        if usize::try_from(wd)
            .ok()
            .and_then(|i| self.named.get(i))
            .copied()
            .unwrap_or(false)
        {
            return true;
        }
        self.excluded_days.contains(&day)
    }
}

fn pad_signed(n: i64, width: usize) -> String {
    let sign = if n < 0 { "-" } else { "" };
    format!("{sign}{:0>width$}", n.unsigned_abs())
}

fn directive(f: &Fields, code: char) -> Option<String> {
    let index = |n: i64| usize::try_from(n).ok();
    Some(match code {
        'Y' => pad_signed(f.year % 10_000, 4),
        'm' => pad_signed(f.month, 2),
        'd' => pad_signed(f.day, 2),
        'H' => pad_signed(f.hour, 2),
        'M' => pad_signed(f.minute, 2),
        'S' => pad_signed(f.second, 2),
        'a' => (*WEEKDAY_ABBREV.get(index(f.weekday % 7)?)?).into(),
        'b' => (*MONTH_ABBREV.get(index(f.month - 1)?)?).into(),
        '%' => "%".into(),
        _ => return None,
    })
}

pub fn format(seconds: i64, format: &str) -> (String, String) {
    let f = split(seconds);
    let mut out = String::new();
    let mut unsupported = String::new();
    let mut chars = format.chars();
    while let Some(c) = chars.next() {
        if c != '%' {
            out.push(c);
            continue;
        }
        let Some(code) = chars.next() else {
            if unsupported.is_empty() {
                unsupported.push('%');
            }
            out.push('%');
            break;
        };
        match directive(&f, code) {
            Some(piece) => out.push_str(&piece),
            None => {
                if unsupported.is_empty() {
                    unsupported.push('%');
                    unsupported.push(code);
                }
                out.push('%');
                out.push(code);
            }
        }
    }
    (out, unsupported)
}

#[cfg(test)]
#[allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;

    #[test]
    fn civil_round_trip_and_known_dates() {
        assert_eq!(days_from_civil(1970, 1, 1), 0);
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        assert_eq!(civil_from_days(19_723), (2024, 1, 1));
        let mut days = -800_000;
        while days <= 800_000 {
            let (y, m, d) = civil_from_days(days);
            assert_eq!(days_from_civil(y, m, d), days);
            assert!((1..=7).contains(&iso_weekday(days)));
            days += 37;
        }
        assert_eq!(iso_weekday(0), 4);
        assert_eq!(iso_week(19_723), (1, 2024));
        assert_eq!(iso_week(19_722), (52, 2023));
    }

    #[test]
    fn split_join_round_trip() {
        for seconds in [
            0,
            -1,
            86_399,
            86_400,
            -86_400,
            1_705_314_600,
            -62_135_596_800,
            253_402_300_799,
        ] {
            let f = split(seconds);
            assert_eq!(
                join(f.year, f.month, f.day, f.hour, f.minute, f.second),
                seconds
            );
        }
    }

    #[test]
    fn clamped_month_add_clamps_days() {
        let jan31 = join(2024, 1, 31, 10, 20, 30);
        assert_eq!(clamped_month_add(jan31, 1), join(2024, 2, 29, 10, 20, 30));
        assert_eq!(clamped_month_add(jan31, 13), join(2025, 2, 28, 10, 20, 30));
        assert_eq!(clamped_month_add(jan31, 12), join(2025, 1, 31, 10, 20, 30));
        assert_eq!(clamped_month_add(jan31, -1), join(2023, 12, 31, 10, 20, 30));
    }

    #[test]
    fn floor_helpers_round_toward_negative_infinity() {
        assert_eq!(floor_div(-3, 2), -2);
        assert_eq!(floor_mod(-3, 2), 1);
        assert_eq!(floor_div(7, 2), 3);
        assert_eq!(floor_div(7, -2), -4);
    }

    #[test]
    fn format_directives_and_unsupported_codes() {
        let t = join(2014, 1, 5, 7, 8, 9);
        assert_eq!(
            format(t, "%Y-%m-%d %H:%M:%S %a %b %%"),
            ("2014-01-05 07:08:09 Sun Jan %".into(), String::new())
        );
        assert_eq!(format(t, "%L %d"), ("%L 05".into(), "%L".into()));
        assert_eq!(format(t, "x%"), ("x%".into(), "%".into()));
    }

    #[test]
    fn calendar_applies_weekends_names_dates_and_includes() {
        let excludes = ["weekends", "monday", "2014-01-08"].map(String::from);
        let includes = ["2014-01-04".to_owned()];
        let cal = Calendar::new(&excludes, &includes, "saturday");
        let day = |d| days_from_civil(2014, 1, d);
        assert!(!cal.excluded(day(3)));
        assert!(!cal.excluded(day(4)));
        assert!(cal.excluded(day(5)));
        assert!(cal.excluded(day(6)));
        assert!(cal.excluded(day(8)));
        let friday = Calendar::new(&["weekends".to_owned()], &[], "friday");
        assert!(friday.excluded(day(3)));
        assert!(friday.excluded(day(4)));
        assert!(!friday.excluded(day(5)));
    }
}
