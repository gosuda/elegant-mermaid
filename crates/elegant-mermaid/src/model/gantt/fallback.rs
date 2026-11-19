//! Fallback date parsing for start operands that the `dateFormat` does not accept:
//! ISO 8601 dates with optional clock and offset, and `YYYY/M/D`.

use crate::civil;

const FALLBACK_YEAR_LIMIT: i64 = 10_000;

struct Scan<'a> {
    text: &'a [u8],
    at: usize,
}

#[derive(Clone, Copy)]
struct Date {
    year: i64,
    month: i64,
    day: i64,
}

#[derive(Clone, Copy, Default)]
struct Clock {
    hour: i64,
    minute: i64,
    second: i64,
}

impl Scan<'_> {
    fn digits(&mut self, n: usize) -> Option<i64> {
        let part = self.text.get(self.at..self.at + n)?;
        let mut v = 0_i64;
        for &c in part {
            if !c.is_ascii_digit() {
                return None;
            }
            v = v * 10 + i64::from(c - b'0');
        }
        self.at += n;
        Some(v)
    }

    fn accept(&mut self, c: u8) -> bool {
        if self.text.get(self.at) == Some(&c) {
            self.at += 1;
            return true;
        }
        false
    }

    fn done(&self) -> bool {
        self.at == self.text.len()
    }

    fn number(&mut self, limit: usize) -> Option<i64> {
        let mut v = 0_i64;
        let mut n = 0;
        while n < limit
            && let Some(&c) = self.text.get(self.at).filter(|c| c.is_ascii_digit())
        {
            v = v.saturating_mul(10).saturating_add(i64::from(c - b'0'));
            self.at += 1;
            n += 1;
        }
        (n > 0).then_some(v)
    }

    fn year(&mut self) -> Option<i64> {
        let sign = self
            .text
            .get(self.at)
            .copied()
            .filter(|c| matches!(c, b'+' | b'-'));
        let Some(sign) = sign else {
            return self.digits(4);
        };
        self.at += 1;
        let v = self.digits(6)?;
        if sign == b'-' {
            return (v != 0).then_some(-v);
        }
        Some(v)
    }

    fn group(&mut self, sep: u8, into: &mut i64) -> bool {
        if !self.accept(sep) {
            return true;
        }
        match self.digits(2) {
            Some(v) => {
                *into = v;
                true
            }
            None => false,
        }
    }

    fn iso_date(&mut self) -> Option<Date> {
        let mut d = Date {
            year: self.year()?,
            month: 1,
            day: 1,
        };
        (self.group(b'-', &mut d.month) && self.group(b'-', &mut d.day)).then_some(d)
    }

    fn slash_date(&mut self) -> Option<Date> {
        let year = self.digits(4)?;
        self.accept(b'/').then_some(())?;
        let month = self.number(2)?;
        self.accept(b'/').then_some(())?;
        let day = self.number(2)?;
        Some(Date { year, month, day })
    }

    fn fraction(&mut self) -> bool {
        !self.accept(b'.') || self.number(1 << 20).is_some()
    }

    fn seconds(&mut self, clock: &mut Clock) -> bool {
        if !self.accept(b':') {
            return true;
        }
        match self.digits(2) {
            Some(v) => {
                clock.second = v;
                self.fraction()
            }
            None => false,
        }
    }

    fn clock(&mut self) -> Option<Clock> {
        let mut clock = Clock {
            hour: self.digits(2)?,
            ..Clock::default()
        };
        self.accept(b':').then_some(())?;
        clock.minute = self.digits(2)?;
        self.seconds(&mut clock).then_some(clock)
    }

    fn offset(&mut self) -> bool {
        if self.accept(b'Z') {
            return true;
        }
        if !matches!(self.text.get(self.at), Some(b'+' | b'-')) {
            return true;
        }
        self.at += 1;
        if self.digits(2).is_none() {
            return false;
        }
        self.accept(b':');
        self.at >= self.text.len() || self.digits(2).is_some()
    }
}

fn valid_clock(c: Clock) -> bool {
    if c.hour == 24 {
        return c.minute == 0 && c.second == 0;
    }
    c.hour < 24 && c.minute < 60 && c.second < 60
}

fn valid_date(d: Date) -> bool {
    (1..=12).contains(&d.month)
        && d.day >= 1
        && d.day <= civil::days_in_month(d.year, d.month)
        && d.year.abs() <= FALLBACK_YEAR_LIMIT
}

pub(super) fn fallback_seconds(text: &str) -> Option<i64> {
    let mut scan = Scan {
        text: text.as_bytes(),
        at: 0,
    };
    let date = match scan.iso_date() {
        Some(d) => d,
        None => {
            scan.at = 0;
            scan.slash_date()?
        }
    };
    let mut clock = Clock::default();
    if scan.accept(b'T') || scan.accept(b' ') {
        clock = scan.clock()?;
        scan.offset().then_some(())?;
    }
    (scan.done() && valid_date(date) && valid_clock(clock)).then(|| {
        civil::join(
            date.year,
            date.month,
            date.day,
            clock.hour,
            clock.minute,
            clock.second,
        )
    })
}
