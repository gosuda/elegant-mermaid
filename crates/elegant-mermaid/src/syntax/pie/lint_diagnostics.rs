use crate::{
    diag::{Diagnostic, Edit, Fix, FixSafety, Severity},
    source::Span,
};

pub(super) fn merge(
    source: &str,
    parsed: Vec<Diagnostic>,
    removed: &[Span],
    body: &[super::ast::Statement],
) -> Vec<Diagnostic> {
    let mut specific = Vec::new();
    let mut ranges = Vec::new();
    let mut start = 0;
    while start < source.len() {
        let end = source[start..]
            .find(['\r', '\n'])
            .map_or(source.len(), |n| start + n);
        let raw = &source[start..end];
        let line = slice_comment(raw).trim();
        let at = start + raw.len() - raw.trim_start_matches([' ', '\t']).len();
        let metadata = body.iter().any(|s| match &s.kind {
            super::ast::StatementKind::TitleAndAccessibilities(_) => {
                s.span.start < end && s.span.end > start
            }
            super::ast::StatementKind::PieSection(section) => {
                section.label.span.start < end
                    && section.label.span.end > start
                    && (section.label.span.start < start || section.label.span.end > end)
            }
        });
        if !metadata && !ignored(line, Span { start, end }, removed) {
            let findings = slice_line(line, at);
            if !findings.is_empty() {
                ranges.push(Span { start, end });
            }
            specific.extend(findings);
        }
        start = end + 1;
        if source.as_bytes().get(end) == Some(&b'\r')
            && source.as_bytes().get(start) == Some(&b'\n')
        {
            start += 1;
        }
    }
    let mut out: Vec<_> = parsed
        .into_iter()
        .filter(|d| {
            !ranges
                .iter()
                .any(|s| d.span.start >= s.start && d.span.start <= s.end)
        })
        .collect();
    out.extend(specific);
    out
}

fn ignored(line: &str, span: Span, removed: &[Span]) -> bool {
    if line.is_empty()
        || line.starts_with("%%")
        || removed
            .iter()
            .any(|r| r.start < span.end && r.end > span.start)
    {
        return true;
    }
    ["pie", "title", "accTitle", "accDescr"]
        .iter()
        .any(|prefix| {
            line.strip_prefix(prefix)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with([' ', '\t', ':']))
        })
}

fn issue(code: &'static str, span: Span, replacement: String) -> Vec<Diagnostic> {
    let Some(row) = crate::r#gen::lintrules::LINT_RULES
        .iter()
        .find(|r| r.code == code)
    else {
        return Vec::new();
    };
    let mut d = Diagnostic {
        code,
        severity: Severity::Error,
        message: row.summary.into(),
        span,
        related: Vec::new(),
        help: row.help.into(),
        fixes: Vec::new(),
    };
    if row.fix_safety != "none" {
        d.fixes.push(Fix {
            title: "Repair pie slice label".into(),
            safety: if row.fix_safety == "unsafe" {
                FixSafety::Unsafe
            } else {
                FixSafety::Safe
            },
            edits: vec![Edit {
                span,
                new_text: replacement,
            }],
        });
    }
    vec![d]
}

fn slice_line(line: &str, at: usize) -> Vec<Diagnostic> {
    let emit = |code, lo, hi, replacement| {
        issue(
            code,
            Span {
                start: at + lo,
                end: at + hi,
            },
            replacement,
        )
    };
    let quote = line.as_bytes()[0];
    if quote != b'"' && quote != b'\'' {
        if let Some((label, _)) = line.split_once(':') {
            let label = label.trim();
            if !label.is_empty() {
                return emit(
                    "pie/label-requires-quotes",
                    0,
                    label.len(),
                    format!("\"{label}\""),
                );
            }
        }
        return Vec::new();
    }
    let Some(close) = label_close(line, quote) else {
        let end = line.split_once(':').map_or(line.len(), |(head, _)| {
            head.trim_end_matches([' ', '\t']).len()
        });
        return emit(
            "pie/quote-unclosed",
            end,
            end,
            char::from(quote).to_string(),
        );
    };
    let label = &line[1..close];
    if quote == b'"' && !label.contains("\\\"") && label.contains('"') {
        return emit("pie/label-double-in-double", 1, close, String::new());
    }
    let tail = line[close + 1..].trim();
    let Some(number) = tail.strip_prefix(':') else {
        return emit("pie/missing-colon", close + 1, close + 1, " :".into());
    };
    if number.trim().is_empty() {
        return emit("pie/missing-number", line.len(), line.len(), String::new());
    }
    Vec::new()
}

fn label_close(line: &str, quote: u8) -> Option<usize> {
    let mut escaped = false;
    let first = line.bytes().enumerate().skip(1).find_map(|(i, c)| {
        if escaped {
            escaped = false;
            return None;
        }
        if c == b'\\' {
            escaped = true;
            return None;
        }
        (c == quote).then_some(i)
    })?;
    if line[first + 1..].trim_start().starts_with(':') {
        return Some(first);
    }
    let Some(colon) = line[first + 1..].find(':').map(|n| first + 1 + n) else {
        return Some(first);
    };
    line[..colon].rfind(char::from(quote))
}

fn slice_comment(line: &str) -> &str {
    let mut quote = 0;
    let mut escaped = false;
    let bytes = line.as_bytes();
    for (i, &c) in bytes.iter().enumerate() {
        if escaped {
            escaped = false;
            continue;
        }
        if quote != 0 {
            if c == b'\\' {
                escaped = true;
            } else if c == quote {
                quote = 0;
            }
            continue;
        }
        if c == b'"' || c == b'\'' {
            quote = c;
            continue;
        }
        if c == b'%' && bytes.get(i + 1) == Some(&b'%') {
            return &line[..i];
        }
    }
    line
}
