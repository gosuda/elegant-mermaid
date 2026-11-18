//! Emulation of dayjs strict custom-format parsing and formatting as the gantt database
//! applies it (`spec/grammar/gantt.md`, date resolution). Input is measured in UTF-16
//! code units, as the upstream parser does.

use crate::civil;
use crate::syntax::gantt::is_space;

pub(super) const MAX_MILLIS: i64 = 8_640_000_000_000_000;
const YEAR_GUARD: i64 = 1_000_000;
const COMPONENT_GUARD: i64 = 1_000_000_000;
const DIGIT_SAT: i64 = 1_000_000_000_000_000;
pub(super) const MILLIS_PER_SEC: i64 = 1000;

const MONTH_NAMES: [&str; 12] = [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
];

const WEEKDAY_NAMES: [&str; 7] = [
    "Sunday",
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
];

type Run = (usize, usize);

fn is_digit(c: u16) -> bool {
    (u16::from(b'0')..=u16::from(b'9')).contains(&c)
}

fn is_space16(c: u16) -> bool {
    char::from_u32(u32::from(c)).is_some_and(is_space)
}

pub(super) fn to_u16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

fn text_of(part: &[u16]) -> String {
    String::from_utf16_lossy(part)
}

pub(super) fn digits_value(part: &[u16]) -> i64 {
    let mut n = 0_i64;
    for &c in part {
        if is_digit(c) {
            n = (n * 10 + i64::from(c - u16::from(b'0'))).min(DIGIT_SAT);
        }
    }
    n
}

fn is(c: u16, ascii: u8) -> bool {
    c == u16::from(ascii)
}

fn same_at(input: &[u16], at: usize, word: &str) -> bool {
    word.bytes()
        .enumerate()
        .all(|(i, b)| input.get(at + i).is_some_and(|&c| is(c, b)))
}

fn first_run(part: &[u16], width: usize) -> Option<Run> {
    let mut i = 0;
    while i + width <= part.len() {
        if part.get(i..i + width)?.iter().all(|&c| is_digit(c)) {
            return Some((i, i + width));
        }
        i += 1;
    }
    None
}

fn digit_at(part: &[u16], i: usize) -> bool {
    part.get(i).is_some_and(|&c| is_digit(c))
}

fn digits_at(part: &[u16], i: usize, n: usize) -> bool {
    i + n <= part.len() && (0..n).all(|k| digit_at(part, i + k))
}

#[derive(Clone, Copy)]
enum Matcher {
    Digits(usize),
    OneOrTwo,
    Signed,
    Offset,
    Word,
}

impl Matcher {
    fn find(self, part: &[u16]) -> Option<Run> {
        match self {
            Self::Digits(width) => first_run(part, width),
            Self::OneOrTwo => match_one_or_two(part),
            Self::Signed => match_signed(part),
            Self::Offset => match_offset(part),
            Self::Word => match_word(part),
        }
    }
}

fn match_one_or_two(part: &[u16]) -> Option<Run> {
    let (from, to) = first_run(part, 1)?;
    Some((from, if digit_at(part, to) { to + 1 } else { to }))
}

fn match_signed(part: &[u16]) -> Option<Run> {
    for (from, &c) in part.iter().enumerate() {
        let start = if is(c, b'+') || is(c, b'-') {
            from + 1
        } else {
            from
        };
        if !digit_at(part, start) {
            continue;
        }
        let mut end = start;
        while digit_at(part, end) {
            end += 1;
        }
        return Some((from, end));
    }
    None
}

fn signed_offset_end(part: &[u16], i: usize) -> Option<usize> {
    let c = *part.get(i)?;
    if !(is(c, b'+') || is(c, b'-')) || !digits_at(part, i + 1, 2) {
        return None;
    }
    let mut end = i + 3;
    if part.get(end).is_some_and(|&c| is(c, b':')) {
        end += 1;
    }
    if digits_at(part, end, 2) {
        end += 2;
    }
    Some(end)
}

fn match_offset(part: &[u16]) -> Option<Run> {
    for (i, &c) in part.iter().enumerate() {
        if is(c, b'Z') {
            return Some((i, i + 1));
        }
        if let Some(end) = signed_offset_end(part, i) {
            return Some((i, end));
        }
    }
    None
}

fn word_separator(c: u16) -> bool {
    b"-_:/,()".iter().any(|&b| is(c, b)) || is_space16(c)
}

fn match_word(part: &[u16]) -> Option<Run> {
    for i in 0..part.len() {
        let mut j = i;
        while digit_at(part, j) {
            j += 1;
        }
        let Some(&c) = part.get(j) else {
            continue;
        };
        if word_separator(c) || is_digit(c) {
            continue;
        }
        let mut end = j;
        while part
            .get(end)
            .is_some_and(|&c| !word_separator(c) && !is_digit(c))
        {
            end += 1;
        }
        return Some((i, end));
    }
    None
}

#[derive(Default)]
struct Parsed {
    year: i64,
    month: i64,
    day: i64,
    hours: i64,
    minutes: i64,
    seconds: i64,
    millis: i64,
    afternoon: u8,
    hours_set: bool,
    week: bool,
    zone: bool,
    offset: i64,
}

type Setter = fn(&mut Parsed, &[u16]) -> bool;

fn signed_value(value: &[u16]) -> i64 {
    let n = digits_value(value);
    if value.first().is_some_and(|&c| is(c, b'-')) {
        -n
    } else {
        n
    }
}

fn zone_offset(value: &[u16]) -> i64 {
    let text = text_of(value);
    if text == "Z" {
        return 0;
    }
    let sign = text.as_bytes().first().copied().unwrap_or(b'+');
    let atoi = |part: Option<&str>| part.and_then(|p| p.parse::<i64>().ok()).unwrap_or(0);
    let mut minutes = atoi(text.get(1..3)) * 60;
    let rest = text.get(3..).unwrap_or("");
    let rest = rest.strip_prefix(':').unwrap_or(rest);
    if rest.len() == 2 {
        minutes += atoi(Some(rest));
    }
    match (minutes, sign) {
        (0, _) => 0,
        (_, b'+') => -minutes,
        _ => minutes,
    }
}

fn set_meridiem(p: &mut Parsed, value: &[u16], pm: &str) -> bool {
    p.afternoon = if text_of(value) == pm { 1 } else { 2 };
    true
}

fn set_upper_meridiem(p: &mut Parsed, value: &[u16]) -> bool {
    set_meridiem(p, value, "PM")
}

fn set_lower_meridiem(p: &mut Parsed, value: &[u16]) -> bool {
    set_meridiem(p, value, "pm")
}

fn set_quarter(p: &mut Parsed, value: &[u16]) -> bool {
    p.month = (digits_value(value) - 1) * 3 + 1;
    true
}

fn set_tenths(p: &mut Parsed, value: &[u16]) -> bool {
    p.millis = digits_value(value) * 100;
    true
}

fn set_hundredths(p: &mut Parsed, value: &[u16]) -> bool {
    p.millis = digits_value(value) * 10;
    true
}

fn set_millis(p: &mut Parsed, value: &[u16]) -> bool {
    p.millis = digits_value(value);
    true
}

fn set_seconds(p: &mut Parsed, value: &[u16]) -> bool {
    p.seconds = digits_value(value);
    true
}

fn set_minutes(p: &mut Parsed, value: &[u16]) -> bool {
    p.minutes = digits_value(value);
    true
}

fn set_hours(p: &mut Parsed, value: &[u16]) -> bool {
    p.hours = digits_value(value);
    p.hours_set = true;
    true
}

fn set_day(p: &mut Parsed, value: &[u16]) -> bool {
    p.day = digits_value(value);
    true
}

fn set_month(p: &mut Parsed, value: &[u16]) -> bool {
    p.month = digits_value(value);
    true
}

fn set_year(p: &mut Parsed, value: &[u16]) -> bool {
    p.year = digits_value(value);
    true
}

fn set_week(p: &mut Parsed, value: &[u16]) -> bool {
    p.week = digits_value(value) != 0;
    true
}

fn set_signed_year(p: &mut Parsed, value: &[u16]) -> bool {
    p.year = signed_value(value);
    true
}

fn set_two_digit_year(p: &mut Parsed, value: &[u16]) -> bool {
    let n = digits_value(value);
    p.year = n + if n > 68 { 1900 } else { 2000 };
    true
}

fn set_zone(p: &mut Parsed, value: &[u16]) -> bool {
    p.zone = true;
    p.offset = zone_offset(value);
    true
}

fn set_month_name(p: &mut Parsed, value: &[u16], width: usize) -> bool {
    let text = text_of(value);
    for (i, name) in MONTH_NAMES.iter().enumerate() {
        let candidate = if width == 3 {
            name.get(..3)
        } else {
            Some(*name)
        };
        if candidate == Some(text.as_str()) {
            p.month = i64::try_from(i + 1).unwrap_or(0);
            return true;
        }
    }
    false
}

fn set_short_month(p: &mut Parsed, value: &[u16]) -> bool {
    set_month_name(p, value, 3)
}

fn set_long_month(p: &mut Parsed, value: &[u16]) -> bool {
    set_month_name(p, value, 0)
}

fn ordinal_suffix(day: i64) -> &'static str {
    match day % 100 {
        1 | 21 | 31 => "st",
        2 | 22 => "nd",
        3 | 23 => "rd",
        _ => "th",
    }
}

fn set_ordinal_day(p: &mut Parsed, value: &[u16]) -> bool {
    let Some((from, to)) = first_run(value, 1) else {
        return false;
    };
    let mut end = to;
    while digit_at(value, end) {
        end += 1;
    }
    p.day = digits_value(value.get(from..end).unwrap_or(&[]));
    let text = text_of(value);
    for d in 1..=31_i64 {
        if format!("{d}{}", ordinal_suffix(d)) == text {
            p.day = d;
        }
    }
    true
}

const EXPRESSIONS: [(&str, Matcher, Setter); 28] = [
    ("A", Matcher::Word, set_upper_meridiem),
    ("a", Matcher::Word, set_lower_meridiem),
    ("Q", Matcher::Digits(1), set_quarter),
    ("S", Matcher::Digits(1), set_tenths),
    ("SS", Matcher::Digits(2), set_hundredths),
    ("SSS", Matcher::Digits(3), set_millis),
    ("s", Matcher::OneOrTwo, set_seconds),
    ("ss", Matcher::OneOrTwo, set_seconds),
    ("m", Matcher::OneOrTwo, set_minutes),
    ("mm", Matcher::OneOrTwo, set_minutes),
    ("H", Matcher::OneOrTwo, set_hours),
    ("h", Matcher::OneOrTwo, set_hours),
    ("HH", Matcher::OneOrTwo, set_hours),
    ("hh", Matcher::OneOrTwo, set_hours),
    ("D", Matcher::OneOrTwo, set_day),
    ("DD", Matcher::Digits(2), set_day),
    ("Do", Matcher::Word, set_ordinal_day),
    ("w", Matcher::OneOrTwo, set_week),
    ("ww", Matcher::Digits(2), set_week),
    ("M", Matcher::OneOrTwo, set_month),
    ("MM", Matcher::Digits(2), set_month),
    ("MMM", Matcher::Word, set_short_month),
    ("MMMM", Matcher::Word, set_long_month),
    ("Y", Matcher::Signed, set_signed_year),
    ("YY", Matcher::Digits(2), set_two_digit_year),
    ("YYYY", Matcher::Digits(4), set_year),
    ("Z", Matcher::Offset, set_zone),
    ("ZZ", Matcher::Offset, set_zone),
];

fn expression_for(token: &str) -> Option<(Matcher, Setter)> {
    EXPRESSIONS
        .iter()
        .find(|(name, _, _)| *name == token)
        .map(|&(_, matcher, setter)| (matcher, setter))
}

enum Piece {
    Literal(usize),
    Token(String),
}

fn bracket_end(f: &[u16], at: usize) -> Option<usize> {
    if !f.get(at).is_some_and(|&c| is(c, b'[')) {
        return None;
    }
    let mut last = None;
    let mut k = at + 1;
    while let Some(&c) = f.get(k) {
        if is(c, b'[') {
            break;
        }
        if is(c, b']') {
            last = Some(k);
        }
        k += 1;
    }
    last
}

fn format_separator(c: u16) -> bool {
    b"-_:/.,()".iter().any(|&b| is(c, b)) || is_space16(c)
}

fn separator_run(f: &[u16], at: usize) -> usize {
    let mut end = at;
    while f.get(end).is_some_and(|&c| format_separator(c)) {
        end += 1;
    }
    end
}

fn repeated(f: &[u16], at: usize, c: u8, limit: usize) -> usize {
    let mut n = 0;
    while n < limit && f.get(at + n).is_some_and(|&x| is(x, c)) {
        n += 1;
    }
    n
}

fn token_at(f: &[u16], at: usize) -> Option<String> {
    let c = u8::try_from(*f.get(at)?).ok()?;
    let run = |c: u8, limit: usize| char::from(c).to_string().repeat(repeated(f, at, c, limit));
    Some(match c {
        b'A' | b'a' | b'Q' | b'z' => char::from(c).to_string(),
        b'Y' if repeated(f, at, b'Y', 4) == 4 => "YYYY".into(),
        b'Y' | b'w' | b'h' | b'H' | b'm' | b's' | b'Z' => run(c, 2),
        b'M' => run(c, 4),
        b'D' if same_at(f, at, "Do") => "Do".into(),
        b'D' => run(c, 2),
        b'S' => run(c, 3),
        _ => return None,
    })
}

fn format_pieces(f: &[u16]) -> Vec<Piece> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < f.len() {
        if let Some(end) = bracket_end(f, i) {
            out.push(Piece::Literal(end - i - 1));
            i = end + 1;
            continue;
        }
        let run = separator_run(f, i);
        if run > i {
            out.push(Piece::Literal(run - i));
            i = run;
            continue;
        }
        if let Some(name) = token_at(f, i) {
            i += name.len();
            out.push(if expression_for(&name).is_some() {
                Piece::Token(name)
            } else {
                Piece::Literal(name.len())
            });
            continue;
        }
        i += 1;
    }
    out
}

fn inner_bracket(f: &[u16], at: usize) -> Option<usize> {
    if !f.get(at).is_some_and(|&c| is(c, b'[')) {
        return None;
    }
    let k = (at + 1..f.len()).find(|&k| f.get(k).is_some_and(|&c| is(c, b']')))?;
    (k != at + 1).then_some(k)
}

fn has_localized(format: &str) -> bool {
    let f = to_u16(format);
    let mut i = 0;
    while i < f.len() {
        if let Some(end) = inner_bracket(&f, i) {
            i = end + 1;
            continue;
        }
        if f.get(i).is_some_and(|&c| is(c, b'L') || is(c, b'l')) {
            return true;
        }
        i += 1;
    }
    false
}

fn index_of16(input: &[u16], value: &[u16]) -> Option<usize> {
    let mut i = 0;
    while i + value.len() <= input.len() {
        if input.get(i..i + value.len()) == Some(value) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn parse_formatted(input: &str, format: &str) -> Option<i64> {
    if has_localized(format) {
        return None;
    }
    let pieces = format_pieces(&to_u16(format));
    if pieces.is_empty() {
        return None;
    }
    let mut remaining = to_u16(input);
    let mut parsed = Parsed::default();
    let mut start = 0;
    for piece in &pieces {
        let name = match piece {
            Piece::Literal(n) => {
                start += n;
                continue;
            }
            Piece::Token(name) => name,
        };
        let (matcher, setter) = expression_for(name)?;
        let part: &[u16] = remaining.get(start..).unwrap_or(&[]);
        let (from, to) = matcher.find(part)?;
        let value = part.get(from..to)?.to_vec();
        if !setter(&mut parsed, &value) {
            return None;
        }
        if let Some(i) = index_of16(&remaining, &value) {
            remaining.drain(i..i + value.len());
        }
    }
    parsed.instant()
}

impl Parsed {
    fn correct_hours(&mut self) {
        if self.afternoon == 0 || !self.hours_set {
            return;
        }
        if self.afternoon == 1 && self.hours < 12 {
            self.hours += 12;
        } else if self.afternoon == 2 && self.hours == 12 {
            self.hours = 0;
        }
    }

    fn instant(&mut self) -> Option<i64> {
        self.correct_hours();
        if self.week {
            return None;
        }
        let day = if self.day == 0 { 1 } else { self.day };
        let year = if self.year == 0 { 1970 } else { self.year };
        let month = (self.month - 1).max(0);
        let millis = if self.zone {
            self.millis + self.offset * 60 * 1000
        } else {
            self.millis
        };
        civil_instant(
            year,
            month,
            day,
            [self.hours, self.minutes, self.seconds],
            millis,
        )
    }
}

fn civil_instant(year: i64, month: i64, day: i64, clock: [i64; 3], millis: i64) -> Option<i64> {
    let [hours, minutes, seconds] = clock;
    let year = if (0..=99).contains(&year) {
        year + 1900
    } else {
        year
    };
    if [month, day, hours, minutes, seconds]
        .iter()
        .any(|v| v.abs() > COMPONENT_GUARD)
        || year.abs() > YEAR_GUARD
    {
        return None;
    }
    let y = year + civil::floor_div(month, 12);
    let m = civil::floor_mod(month, 12) + 1;
    let days = civil::days_from_civil(y, m, 1) + day - 1;
    let total = days * 86_400 * MILLIS_PER_SEC
        + hours * 3600 * MILLIS_PER_SEC
        + minutes * 60 * MILLIS_PER_SEC
        + seconds * MILLIS_PER_SEC
        + millis;
    (total.abs() <= MAX_MILLIS).then_some(total)
}

fn pad_number(n: i64, width: usize) -> String {
    format!("{:0>width$}", n.to_string())
}

struct Clock {
    fields: civil::Fields,
    millis: i64,
    total: i64,
}

impl Clock {
    fn new(total: i64) -> Self {
        let secs = civil::floor_div(total, MILLIS_PER_SEC);
        Self {
            fields: civil::split(secs),
            millis: civil::floor_mod(total, MILLIS_PER_SEC),
            total,
        }
    }

    fn hour12(&self) -> i64 {
        match self.fields.hour % 12 {
            0 => 12,
            h => h,
        }
    }

    fn meridiem(&self) -> &'static str {
        if self.fields.hour >= 12 { "PM" } else { "AM" }
    }

    fn clock_hour24(&self) -> i64 {
        if self.fields.hour == 0 {
            24
        } else {
            self.fields.hour
        }
    }

    fn month_name(&self, width: usize) -> String {
        let name = usize::try_from(self.fields.month - 1)
            .ok()
            .and_then(|i| MONTH_NAMES.get(i))
            .copied()
            .unwrap_or("");
        name.get(..width.min(name.len())).unwrap_or("").into()
    }

    fn weekday_name(&self, width: usize) -> String {
        let name = usize::try_from(self.fields.weekday % 7)
            .ok()
            .and_then(|i| WEEKDAY_NAMES.get(i))
            .copied()
            .unwrap_or("");
        name.get(..width.min(name.len())).unwrap_or("").into()
    }

    fn two_digit_year(&self) -> String {
        let s = self.fields.year.to_string();
        s.get(s.len().saturating_sub(2)..).unwrap_or("").into()
    }

    fn iso_week(&self) -> (i64, i64) {
        civil::iso_week(self.fields.days)
    }

    fn advanced(&self, token: &str) -> Option<String> {
        let f = &self.fields;
        Some(match token {
            "Q" => ((f.month - 1) / 3 + 1).to_string(),
            "Do" => format!("[{}{}]", f.day, ordinal_suffix(f.day)),
            "GGGG" => self.iso_week().1.to_string(),
            "W" => pad_number(self.iso_week().0, 1),
            "WW" => pad_number(self.iso_week().0, 2),
            "k" => pad_number(self.clock_hour24(), 1),
            "kk" => pad_number(self.clock_hour24(), 2),
            "X" => civil::floor_div(self.total, MILLIS_PER_SEC).to_string(),
            "x" => self.total.to_string(),
            "S" => "S".into(),
            _ => return None,
        })
    }

    fn core(&self, token: &str) -> String {
        let f = &self.fields;
        match token {
            "YYYY" => pad_number(f.year, 4),
            "YY" => self.two_digit_year(),
            "M" => f.month.to_string(),
            "MM" => pad_number(f.month, 2),
            "MMM" => self.month_name(3),
            "MMMM" => self.month_name(9),
            "D" => f.day.to_string(),
            "DD" => pad_number(f.day, 2),
            "d" => (f.weekday % 7).to_string(),
            "dd" => self.weekday_name(2),
            "ddd" => self.weekday_name(3),
            "dddd" => self.weekday_name(9),
            "H" => f.hour.to_string(),
            "HH" => pad_number(f.hour, 2),
            "h" => self.hour12().to_string(),
            "hh" => pad_number(self.hour12(), 2),
            "a" => self.meridiem().to_ascii_lowercase(),
            "A" => self.meridiem().into(),
            "m" => f.minute.to_string(),
            "mm" => pad_number(f.minute, 2),
            "s" => f.second.to_string(),
            "ss" => pad_number(f.second, 2),
            "SSS" => pad_number(self.millis, 3),
            "Z" => "+00:00".into(),
            _ => "+0000".into(),
        }
    }
}

const ADVANCED_TOKENS: [&str; 16] = [
    "wo", "ww", "w", "WW", "W", "zzz", "z", "gggg", "GGGG", "Do", "X", "x", "kk", "k", "S", "Q",
];

const CORE_TOKENS: [&str; 25] = [
    "YYYY", "YY", "MMMM", "MMM", "MM", "M", "DD", "D", "dddd", "ddd", "dd", "d", "HH", "H", "hh",
    "h", "a", "A", "mm", "m", "ss", "s", "ZZ", "Z", "SSS",
];

fn scan_alternatives<'a>(text: &[u8], alternatives: &[&'a str]) -> Option<&'a str> {
    alternatives
        .iter()
        .find(|alt| text.starts_with(alt.as_bytes()))
        .copied()
}

fn bracket_span(text: &[u8]) -> Option<usize> {
    if text.first() != Some(&b'[') {
        return None;
    }
    let end = text.get(1..)?.iter().position(|&c| c == b']')?;
    (end > 0).then_some(end + 2)
}

impl Clock {
    fn advanced_pass(&self, format: &[u8]) -> Option<Vec<u8>> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < format.len() {
            let rest = format.get(i..)?;
            if let Some(n) = bracket_span(rest) {
                out.extend_from_slice(rest.get(..n)?);
                i += n;
                continue;
            }
            let Some(token) = scan_alternatives(rest, &ADVANCED_TOKENS) else {
                out.push(*rest.first()?);
                i += 1;
                continue;
            };
            out.extend_from_slice(self.advanced(token)?.as_bytes());
            i += token.len();
        }
        Some(out)
    }

    fn core_pass(&self, format: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        let mut i = 0;
        while let Some(rest) = format.get(i..).filter(|r| !r.is_empty()) {
            if let Some(n) = bracket_span(rest) {
                out.extend_from_slice(rest.get(1..n - 1).unwrap_or(&[]));
                i += n;
                continue;
            }
            if let Some(token) = scan_alternatives(rest, &CORE_TOKENS) {
                out.extend_from_slice(self.core(token).as_bytes());
                i += token.len();
                continue;
            }
            out.extend_from_slice(rest.get(..1).unwrap_or(&[]));
            i += 1;
        }
        out
    }
}

fn format_millis(total: i64, format: &str) -> Option<String> {
    let clock = Clock::new(total);
    let middle = clock.advanced_pass(format.as_bytes())?;
    Some(String::from_utf8_lossy(&clock.core_pass(&middle)).into_owned())
}

fn canonical_integer(text: &str) -> Option<i64> {
    let body = text.strip_prefix('-').unwrap_or(text);
    if body.is_empty()
        || (body.len() > 1 && body.starts_with('0'))
        || body.len() > 17
        || !body.bytes().all(|c| c.is_ascii_digit())
        || text == "-0"
    {
        return None;
    }
    text.parse().ok()
}

fn parse_timestamp(input: &str, format: &str) -> Option<i64> {
    let mut n = canonical_integer(input)?;
    if format == "X" {
        n = n.checked_mul(MILLIS_PER_SEC)?;
    }
    (n.abs() <= MAX_MILLIS).then_some(n)
}

pub(super) fn parse_strict(input: &str, format: &str) -> Option<i64> {
    if format == "x" || format == "X" {
        return parse_timestamp(input, format);
    }
    let total = parse_formatted(input, format)?;
    (format_millis(total, format)? == input).then_some(total)
}

#[cfg(test)]
mod tests {
    use super::parse_strict;

    fn cases() -> Vec<(String, String, Option<i64>)> {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../internal/model/gantt/testdata/dayjs_cases.json"
        );
        let text = std::fs::read_to_string(path).unwrap_or_default();
        let mut cursor = text.chars().peekable();
        let mut cases = Vec::new();
        let mut strings: Vec<String> = Vec::new();
        let mut number = String::new();
        while let Some(c) = cursor.next() {
            match c {
                '"' => {
                    let mut s = String::new();
                    while let Some(d) = cursor.next() {
                        match d {
                            '"' => break,
                            '\\' => s.extend(cursor.next()),
                            _ => s.push(d),
                        }
                    }
                    strings.push(s);
                }
                '-' | '0'..='9' if strings.len() == 2 => number.push(c),
                'n' if strings.len() == 2 => {
                    number.clear();
                    for _ in 0..3 {
                        cursor.next();
                    }
                    cases.push((strings.remove(0), strings.remove(0), None));
                }
                ']' if strings.len() == 2 => {
                    cases.push((
                        strings.remove(0),
                        strings.remove(0),
                        Some(number.parse().unwrap_or(0)),
                    ));
                    number.clear();
                }
                _ => {}
            }
        }
        cases
    }

    #[test]
    fn strict_parse_matches_dayjs() {
        let cases = cases();
        assert!(cases.len() > 1000, "{}", cases.len());
        let mut valid = 0;
        for (format, input, want) in &cases {
            let got = parse_strict(input, format);
            assert_eq!(got, *want, "{format:?} {input:?}");
            valid += usize::from(want.is_some());
        }
        assert!(valid > 100);
    }
}
