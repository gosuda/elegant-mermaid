use super::ast::Notation;

pub(super) fn is_js_space(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\u{b}'
            | '\u{c}'
            | '\r'
            | ' '
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
            | '\u{2000}'..='\u{200a}'
    )
}

pub(super) fn is_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

pub(super) fn trim_js(s: &str) -> &str {
    s.trim_matches(is_js_space)
}

pub(super) fn collapse_blanks(s: &str) -> String {
    collapse_runs(s, |c| c == ' ' || c == '\t', ' ')
}

pub(super) fn collapse_breaks(s: &str) -> String {
    collapse_runs(s, |c| c == '\n' || c == '\r', '\n')
}

fn collapse_runs(s: &str, in_run: fn(char) -> bool, replacement: char) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < chars.len() {
        if !in_run(chars[i]) {
            out.push(chars[i]);
            i += 1;
            continue;
        }
        let mut j = i;
        while j < chars.len() && in_run(chars[j]) {
            j += 1;
        }
        if j - i >= 2 {
            out.push(replacement);
        } else {
            out.extend(&chars[i..j]);
        }
        i = j;
    }
    out
}

pub(super) fn decode_escapes(quoted: &str) -> String {
    let content = strip_quotes(quoted);
    let mut out = String::with_capacity(content.len());
    let mut chars = content.chars().peekable();
    while let Some(c) = chars.next() {
        let Some(escaped) = chars.next_if(|_| c == '\\') else {
            out.push(c);
            continue;
        };
        out.push(match escaped {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            other => other,
        });
    }
    out
}

pub(super) fn strip_quotes(quoted: &str) -> &str {
    quoted
        .len()
        .checked_sub(1)
        .filter(|&last| last >= 1)
        .and_then(|last| quoted.get(1..last))
        .unwrap_or("")
}

fn is_quoted(s: &str) -> bool {
    let bytes = s.as_bytes();
    matches!(
        (bytes.first(), bytes.last()),
        (Some(b'"'), Some(b'"')) | (Some(b'\''), Some(b'\''))
    )
}

pub(super) fn single_line(s: &str) -> String {
    collapse_blanks(trim_js(s))
}

pub(super) fn meta_title(raw: &str, notation: Notation) -> String {
    let text = single_line(raw.strip_prefix("title").unwrap_or(raw));
    let trimmed = trim_js(&text);
    if !is_quoted(trimmed) {
        return text;
    }
    if notation == Notation::Abnf {
        return strip_quotes(trimmed).to_owned();
    }
    decode_escapes(trimmed)
}

pub(super) fn meta_acc_title(raw: &str) -> String {
    raw.split_once(':')
        .map_or_else(String::new, |(_, value)| single_line(value))
}

pub(super) fn meta_acc_descr(raw: &str) -> String {
    let rest = raw.strip_prefix("accDescr").unwrap_or(raw);
    let brace = rest.trim_start_matches(is_js_space);
    if let Some(block) = brace.strip_prefix('{') {
        let inner = block.get(..block.len().saturating_sub(1)).unwrap_or("");
        return multi_line_descr(inner);
    }
    rest.split_once(':')
        .map_or_else(String::new, |(_, value)| single_line(value))
}

fn multi_line_descr(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let chars = strip_leading_blank_lines(&chars);
    let chars = strip_trailing_space(&chars);
    let joined: String = chars.into_iter().collect();
    collapse_breaks(&collapse_blanks(&joined))
}

fn at_line_start(chars: &[char], i: usize) -> bool {
    i == 0 || chars.get(i - 1).copied().is_some_and(is_line_terminator)
}

fn strip_leading_blank_lines(chars: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(chars.len());
    let mut i = 0;
    while i < chars.len() {
        if at_line_start(chars, i) {
            let mut j = i;
            while j < chars.len() && is_js_space(chars[j]) {
                j += 1;
            }
            if j > i {
                i = j;
                continue;
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn strip_trailing_space(chars: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(chars.len());
    let mut i = 0;
    while i < chars.len() {
        let end = trailing_space_end(chars, i);
        if end > i {
            i = end;
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn trailing_space_end(chars: &[char], i: usize) -> usize {
    if !is_js_space(chars[i]) {
        return i;
    }
    let mut run = i;
    while run < chars.len() && is_js_space(chars[run]) {
        run += 1;
    }
    (i + 1..=run)
        .rev()
        .find(|&k| k == chars.len() || is_line_terminator(chars[k]))
        .unwrap_or(i)
}
