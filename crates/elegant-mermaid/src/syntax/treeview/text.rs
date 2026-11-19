pub(super) fn js_space(c: char) -> bool {
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
    ) || ('\u{2000}'..='\u{200a}').contains(&c)
}

fn line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

pub(super) fn trim_js(s: &str) -> &str {
    s.trim_matches(js_space)
}

pub(super) fn trim_end_js(s: &str) -> &str {
    s.trim_end_matches(js_space)
}

pub(super) fn blank(c: u8) -> bool {
    c == b' ' || c == b'\t'
}

pub(super) fn word_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn collapse_runs(s: &str, member: fn(char) -> bool, joined: char) -> String {
    let mut out = String::with_capacity(s.len());
    let mut run = String::new();
    for c in s.chars() {
        if member(c) {
            run.push(c);
            continue;
        }
        flush_run(&mut out, &mut run, joined);
        out.push(c);
    }
    flush_run(&mut out, &mut run, joined);
    out
}

fn flush_run(out: &mut String, run: &mut String, joined: char) {
    if run.chars().count() >= 2 {
        out.push(joined);
    } else {
        out.push_str(run);
    }
    run.clear();
}

fn is_blank_char(c: char) -> bool {
    c == ' ' || c == '\t'
}

fn is_break_char(c: char) -> bool {
    c == '\n' || c == '\r'
}

pub(super) fn collapse_blanks(s: &str) -> String {
    collapse_runs(s, is_blank_char, ' ')
}

fn collapse_breaks(s: &str) -> String {
    collapse_runs(s, is_break_char, '\n')
}

fn single_line(s: &str) -> String {
    collapse_blanks(trim_js(s))
}

fn line_rest(s: &str) -> &str {
    s.find(['\n', '\r'])
        .and_then(|end| s.get(..end))
        .unwrap_or(s)
}

fn after<'a>(raw: &'a str, word: &str) -> &'a str {
    raw.find(word)
        .and_then(|at| raw.get(at + word.len()..))
        .unwrap_or("")
}

pub(super) fn title_value(raw: &str) -> String {
    let rest = after(raw, "title");
    match rest.as_bytes().first() {
        Some(c) if blank(*c) => single_line(line_rest(rest)),
        _ => String::new(),
    }
}

pub(super) fn acc_title_value(raw: &str) -> String {
    let rest = after(raw, "accTitle");
    rest.find(':')
        .and_then(|colon| rest.get(colon + 1..))
        .map_or_else(String::new, |tail| single_line(line_rest(tail)))
}

pub(super) fn acc_descr_value(raw: &str) -> String {
    let rest = after(raw, "accDescr");
    let line = rest.trim_start_matches([' ', '\t']);
    if let Some(tail) = line.strip_prefix(':') {
        return single_line(line_rest(tail));
    }
    let Some(brace) = rest.find('{') else {
        return String::new();
    };
    let inner = rest.get(brace + 1..).unwrap_or("");
    let end = inner.find('}').unwrap_or(inner.len());
    multi_line(inner.get(..end).unwrap_or(""))
}

fn multi_line(content: &str) -> String {
    let rs: Vec<char> = content.chars().collect();
    let rs = strip_trailing_space(&strip_leading_space(&rs));
    let text: String = rs.into_iter().collect();
    collapse_breaks(&collapse_blanks(&text))
}

fn at_line_start(rs: &[char], i: usize) -> bool {
    i == 0 || rs.get(i - 1).copied().is_some_and(line_terminator)
}

fn space_run_end(rs: &[char], from: usize) -> usize {
    let mut j = from;
    while rs.get(j).copied().is_some_and(js_space) {
        j += 1;
    }
    j
}

fn strip_leading_space(rs: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(rs.len());
    let mut i = 0;
    while let Some(c) = rs.get(i) {
        let j = space_run_end(rs, i);
        if at_line_start(rs, i) && j > i {
            i = j;
            continue;
        }
        out.push(*c);
        i += 1;
    }
    out
}

fn strip_trailing_space(rs: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(rs.len());
    let mut i = 0;
    while let Some(c) = rs.get(i) {
        let end = trailing_space_end(rs, i);
        if end > i {
            i = end;
            continue;
        }
        out.push(*c);
        i += 1;
    }
    out
}

fn trailing_space_end(rs: &[char], i: usize) -> usize {
    let run = space_run_end(rs, i);
    (i + 1..=run)
        .rev()
        .find(|k| *k == rs.len() || rs.get(*k).copied().is_some_and(line_terminator))
        .unwrap_or(i)
}

pub(super) fn class_value(raw: &str) -> String {
    trim_js(trim_js(raw).get(3..).unwrap_or("")).to_owned()
}

pub(super) fn icon_value(raw: &str) -> String {
    let trimmed = trim_js(raw);
    trimmed
        .get("icon(".len()..trimmed.len().saturating_sub(1))
        .unwrap_or("")
        .to_owned()
}

pub(super) fn desc_value(raw: &str) -> String {
    trim_js(trim_js(raw).get(2..).unwrap_or("")).to_owned()
}

pub(super) fn quoted_name_value(raw: &str) -> String {
    raw.get(1..raw.len().saturating_sub(1))
        .unwrap_or("")
        .to_owned()
}

pub(super) fn bare_name_value(raw: &str) -> String {
    raw.trim_end_matches([' ', '\t']).to_owned()
}

pub(super) fn utf16_len(s: &str) -> usize {
    s.chars().map(char::len_utf16).sum()
}
