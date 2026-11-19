//! The `encodeEntities` pre-pass of the authority: `#name;` and `#N;` become one opaque
//! text token, except where a style or `classDef` colour makes the `#` a colour sign.

use std::collections::BTreeSet;

use super::lexer::{is_word_byte, js_space};

pub(super) fn entity_end(source: &str, deleted: &BTreeSet<usize>, at: usize) -> usize {
    let bytes = source.as_bytes();
    if bytes.get(at) != Some(&b'#') {
        return 0;
    }
    let mut end = at + 1;
    while bytes.get(end).is_some_and(|b| is_word_byte(*b)) {
        end += 1;
    }
    if end == at + 1 || bytes.get(end) != Some(&b';') || deleted.contains(&end) {
        return 0;
    }
    end + 1 - at
}

pub(super) fn deleted_semicolons(source: &str) -> BTreeSet<usize> {
    let bytes = source.as_bytes();
    let mut deleted = BTreeSet::new();
    let mut start = 0;
    while start < bytes.len() {
        let mut end = start;
        while end < bytes.len() && line_end_size(&bytes[end..]) == 0 {
            end += 1;
        }
        if let Some(last) = bytes[start..end].iter().rposition(|b| *b == b';')
            && annotated_line(source.get(start..end).unwrap_or(""), last)
        {
            deleted.insert(start + last);
        }
        start = end + line_end_size(&bytes[end..]).max(1);
    }
    deleted
}

fn line_end_size(bytes: &[u8]) -> usize {
    match bytes {
        [b'\n' | b'\r', ..] => 1,
        [0xe2, 0x80, 0xa8 | 0xa9, ..] => 3,
        _ => 0,
    }
}

fn annotated_line(line: &str, last: usize) -> bool {
    annotated(line, "style", last) || annotated(line, "classDef", last)
}

fn annotated(line: &str, word: &str, last: usize) -> bool {
    let Some(from) = line.find(word) else {
        return false;
    };
    let floor = from + word.len();
    let mut reaches_hash = false;
    let mut at = last;
    while at > floor {
        let Some(c) = line.get(..at).and_then(|head| head.chars().next_back()) else {
            break;
        };
        at -= c.len_utf8();
        match c {
            '#' => reaches_hash = true,
            c if js_space(c) => reaches_hash = false,
            ':' if reaches_hash => return true,
            _ => {}
        }
    }
    false
}
