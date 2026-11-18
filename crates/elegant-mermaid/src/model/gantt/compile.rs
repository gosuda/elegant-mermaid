//! Date compilation of gantt tasks: start and end resolution over at most eleven passes,
//! predecessor references, and exclusion-aware end extension.

use crate::civil;
use crate::source::Span;
use crate::syntax::gantt::is_space;

use super::dayjs::{MAX_MILLIS, MILLIS_PER_SEC, digits_value, parse_strict, to_u16};
use super::duration::{add_duration, parse_duration, valid_seconds};
use super::fallback::fallback_seconds;
use super::{Resolver, StartKind, trim};

const MAX_SCANS: usize = 11;
const EXCLUSION_LIMIT_DAYS: i64 = 10_000;
const EXCLUSION_STEP_CAP: usize = 5_000_000;
const C_INVALID_DATE: &str = "gantt/invalid-date";
const C_INVALID_END: &str = "gantt/invalid-end";
const C_PREDECESSOR: &str = "gantt/predecessor-missing";
const C_UNKNOWN_REF: &str = "gantt/unknown-task-reference";
const C_EXCLUSION: &str = "gantt/exclusion-limit";
const C_UNRESOLVED: &str = "gantt/unresolved-task";
const DATE_ONLY_FORMAT: &str = "YYYY-MM-DD";

struct Reference {
    id: String,
    span: Span,
}

type DateResult = (i64, bool, bool);

fn id_class(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b'_' | b'-' | b' ')
}

fn reference_ids(text: &str, keyword: &str, operand: Span) -> Option<Vec<Reference>> {
    let rest = text.strip_prefix(keyword)?;
    let lead = rest.len() - rest.trim_start_matches(is_space).len();
    if lead == 0 {
        return None;
    }
    let body = rest.get(lead..)?.as_bytes();
    let run = body.iter().take_while(|&&c| id_class(c)).count();
    if run == 0 {
        let first = rest.chars().next().map_or(0, char::len_utf8);
        let spaced = rest
            .get(first..lead)
            .is_some_and(|gap| gap.as_bytes().contains(&b' '));
        return spaced.then(Vec::new);
    }
    let base = operand.start + keyword.len() + lead;
    let mut out = Vec::new();
    let mut at = 0;
    while at < run {
        if body.get(at) == Some(&b' ') {
            at += 1;
            continue;
        }
        let mut end = at;
        while end < run && body.get(end) != Some(&b' ') {
            end += 1;
        }
        out.push(Reference {
            id: String::from_utf8_lossy(body.get(at..end).unwrap_or(&[])).into_owned(),
            span: Span {
                start: base + at,
                end: base + end,
            },
        });
        at = end;
    }
    Some(out)
}

impl Resolver {
    fn first_report(&mut self, task: usize, keyword: &'static str, id: usize) -> bool {
        self.scans.seen.insert((task, keyword, id))
    }

    pub(super) fn compile(&mut self) {
        self.scans.calendar = civil::Calendar::new(
            &self.model.excludes,
            &self.model.includes,
            &self.model.weekend,
        );
        for _ in 0..MAX_SCANS {
            if self.scan() {
                break;
            }
        }
        for i in 0..self.model.tasks.len() {
            let Some(t) = self.model.tasks.get(i) else {
                continue;
            };
            if !t.failed && !(t.resolved && t.has_start && t.has_end) {
                let span = t.data_span;
                self.report(
                    C_UNRESOLVED,
                    "task dates remain unresolved after eleven passes".into(),
                    span,
                );
            }
        }
    }

    fn scan(&mut self) -> bool {
        let mut done = true;
        for i in 0..self.model.tasks.len() {
            self.compile_task(i);
            done = done
                && self
                    .model
                    .tasks
                    .get(i)
                    .is_some_and(|t| t.resolved || t.failed);
        }
        done
    }

    fn compile_task(&mut self, i: usize) {
        let failed = self.model.tasks.get(i).is_none_or(|t| t.failed);
        if failed || !self.compile_start(i) || !self.model.tasks.get(i).is_some_and(|t| t.has_start)
        {
            return;
        }
        let (end, defined, ok) = self.end_date(i);
        if !ok {
            return;
        }
        let Some(t) = self.model.tasks.get_mut(i) else {
            return;
        };
        t.end_seconds = end;
        t.has_end = defined;
        if !defined {
            return;
        }
        t.resolved = true;
        t.manual_end = parse_strict(&t.end.text, DATE_ONLY_FORMAT).is_some();
        self.check_dates(i);
    }

    fn compile_start(&mut self, i: usize) -> bool {
        let Some(t) = self.model.tasks.get(i) else {
            return false;
        };
        if t.start_kind == StartKind::PrevEnd {
            let previous = t
                .prev_id
                .as_ref()
                .and_then(|id| self.ids.get(id))
                .and_then(|&at| self.model.tasks.get(at))
                .map(|prev| (prev.end_seconds, prev.has_end));
            let span = t.end.span;
            let Some((seconds, has_end)) = previous else {
                self.report(C_PREDECESSOR, "task has no preceding task".into(), span);
                if let Some(t) = self.model.tasks.get_mut(i) {
                    t.failed = true;
                }
                return false;
            };
            if let Some(t) = self.model.tasks.get_mut(i) {
                t.start_seconds = seconds;
                t.has_start = has_end;
            }
            return true;
        }
        let (seconds, defined, ok) = self.start_date(i);
        if defined && let Some(t) = self.model.tasks.get_mut(i) {
            t.start_seconds = seconds;
            t.has_start = true;
        }
        ok
    }

    fn invalid_date(&mut self, i: usize) -> DateResult {
        let Some(t) = self.model.tasks.get_mut(i) else {
            return (0, false, false);
        };
        t.failed = true;
        let (text, span) = (t.start.text.clone(), t.start.span);
        self.report(C_INVALID_DATE, format!("invalid date {text}"), span);
        (0, false, false)
    }

    fn start_date(&mut self, i: usize) -> DateResult {
        let Some(t) = self.model.tasks.get(i) else {
            return (0, false, false);
        };
        let (text, span) = (t.start.text.clone(), t.start.span);
        let format = trim(&self.model.date_format).to_owned();
        if (format == "x" || format == "X")
            && !text.is_empty()
            && text.bytes().all(|c| c.is_ascii_digit())
        {
            let ms = digits_value(&to_u16(&text));
            if ms > MAX_MILLIS {
                return self.invalid_date(i);
            }
            return (civil::floor_div(ms, MILLIS_PER_SEC), true, true);
        }
        if let Some(refs) = reference_ids(&text, "after", span) {
            let (seconds, defined) = self.latest_end(i, &refs);
            return (seconds, defined, true);
        }
        if let Some(ms) = parse_strict(&text, &format) {
            return (civil::floor_div(ms, MILLIS_PER_SEC), true, true);
        }
        if let Some(seconds) = fallback_seconds(&text) {
            return (seconds, true, true);
        }
        self.invalid_date(i)
    }

    fn end_date(&mut self, i: usize) -> DateResult {
        let Some(t) = self.model.tasks.get(i) else {
            return (0, false, false);
        };
        let (text, span, start) = (t.end.text.clone(), t.end.span, t.start_seconds);
        if let Some(refs) = reference_ids(&text, "until", span) {
            let (seconds, defined) = self.earliest_start(i, &refs);
            return (seconds, defined, true);
        }
        if let Some(ms) = parse_strict(&text, trim(&self.model.date_format)) {
            let mut seconds = civil::floor_div(ms, MILLIS_PER_SEC);
            let next = seconds + civil::SECONDS_PER_DAY;
            if self.model.inclusive_end && valid_seconds(next) {
                seconds = next;
            }
            return (seconds, true, true);
        }
        let Some((decimal, unit)) = parse_duration(&text) else {
            if self.first_report(i, "end", 0) {
                self.report(
                    C_INVALID_END,
                    format!("{text} is neither a date nor a duration; task has zero duration"),
                    span,
                );
            }
            return (start, true, true);
        };
        (
            add_duration(start, decimal, unit).unwrap_or(start),
            true,
            true,
        )
    }

    fn unknown_reference(&mut self, i: usize, keyword: &'static str, k: usize, r: &Reference) {
        if self.first_report(i, keyword, k + 1) {
            self.report(
                C_UNKNOWN_REF,
                format!("{keyword} references unknown task id {}", r.id),
                r.span,
            );
        }
    }

    fn latest_end(&mut self, i: usize, refs: &[Reference]) -> (i64, bool) {
        let mut latest: Option<(i64, bool)> = None;
        for (k, r) in refs.iter().enumerate() {
            let Some(&at) = self.ids.get(&r.id) else {
                self.unknown_reference(i, "after", k, r);
                continue;
            };
            let Some(task) = self.model.tasks.get(at) else {
                continue;
            };
            let candidate = (task.end_seconds, task.has_end);
            latest = match latest {
                Some((seconds, has)) if !(candidate.1 && has && candidate.0 > seconds) => {
                    Some((seconds, has))
                }
                _ => Some(candidate),
            };
        }
        latest.unwrap_or((0, true))
    }

    fn earliest_start(&mut self, i: usize, refs: &[Reference]) -> (i64, bool) {
        let mut earliest: Option<(i64, bool)> = None;
        for (k, r) in refs.iter().enumerate() {
            let Some(&at) = self.ids.get(&r.id) else {
                self.unknown_reference(i, "until", k, r);
                continue;
            };
            let Some(task) = self.model.tasks.get(at) else {
                continue;
            };
            let candidate = (task.start_seconds, task.has_start);
            earliest = match earliest {
                Some((seconds, has)) if !(candidate.1 && has && candidate.0 < seconds) => {
                    Some((seconds, has))
                }
                _ => Some(candidate),
            };
        }
        earliest.unwrap_or((0, true))
    }

    fn check_dates(&mut self, i: usize) {
        let Some(t) = self.model.tasks.get(i) else {
            return;
        };
        if self.model.excludes.is_empty() || t.manual_end {
            return;
        }
        let (mut start, mut end) = (t.start_seconds + civil::SECONDS_PER_DAY, t.end_seconds);
        let span = t.end.span;
        let limit = end + EXCLUSION_LIMIT_DAYS * civil::SECONDS_PER_DAY;
        let (mut invalid, mut render) = (false, None);
        while start <= end {
            if !invalid {
                render = Some(end);
            }
            invalid = self
                .scans
                .calendar
                .excluded(civil::floor_div(start, civil::SECONDS_PER_DAY));
            if invalid {
                end += civil::SECONDS_PER_DAY;
            }
            self.scans.steps += 1;
            if end > limit || self.scans.steps > EXCLUSION_STEP_CAP {
                self.report(
                    C_EXCLUSION,
                    "cannot find a non-excluded end within 10000 days".into(),
                    span,
                );
                if let Some(t) = self.model.tasks.get_mut(i) {
                    t.failed = true;
                }
                return;
            }
            start += civil::SECONDS_PER_DAY;
        }
        if let Some(t) = self.model.tasks.get_mut(i) {
            t.end_seconds = end;
            t.render_end = render.unwrap_or(0);
            t.has_render_end = render.is_some();
        }
    }
}
