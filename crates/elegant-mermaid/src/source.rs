use std::borrow::Cow;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineIndex {
    text: String,
    line_starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> LineIndex {
        LineIndex {
            text: text.to_owned(),
            line_starts: line_starts(text),
        }
    }

    pub fn position(&self, offset: usize) -> Position {
        line_position(&self.text, &self.line_starts, offset)
    }

    pub fn utf16_column(&self, offset: usize) -> usize {
        let offset = align(&self.text, offset);
        let index = line_index(&self.line_starts, offset);
        let start = self.line_starts[index];
        let units: usize = self.text[start..offset].chars().map(utf16_units).sum();
        1 + units
    }
}

pub fn repair_utf8(bytes: &[u8]) -> (Cow<'_, str>, Option<usize>) {
    match std::str::from_utf8(bytes) {
        Ok(text) => (Cow::Borrowed(text), None),
        Err(error) => (String::from_utf8_lossy(bytes), Some(error.valid_up_to())),
    }
}

fn utf16_units(scalar: char) -> usize {
    if (scalar as u32) > 0xFFFF { 2 } else { 1 }
}

pub(crate) fn line_starts(text: &str) -> Vec<usize> {
    let bytes = text.as_bytes();
    let mut starts = vec![0];
    let mut cursor = 0;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'\r' if bytes.get(cursor + 1) == Some(&b'\n') => {
                cursor += 2;
                starts.push(cursor);
            }
            b'\r' | b'\n' => {
                cursor += 1;
                starts.push(cursor);
            }
            _ => cursor += 1,
        }
    }
    starts
}

pub(crate) fn line_index(starts: &[usize], offset: usize) -> usize {
    match starts.binary_search(&offset) {
        Ok(index) => index,
        Err(index) => index - 1,
    }
}

pub(crate) fn line_content_end(text: &str, starts: &[usize], index: usize) -> usize {
    let next = match starts.get(index + 1) {
        Some(&next) => next,
        None => return text.len(),
    };
    let bytes = text.as_bytes();
    if next >= 2 && bytes[next - 2] == b'\r' && bytes[next - 1] == b'\n' {
        return next - 2;
    }
    next - 1
}

pub(crate) fn line_content(text: &str, starts: &[usize], line: usize) -> Span {
    let index = line.saturating_sub(1).min(starts.len() - 1);
    Span {
        start: starts[index],
        end: line_content_end(text, starts, index),
    }
}

pub(crate) fn line_position(text: &str, starts: &[usize], offset: usize) -> Position {
    let offset = align(text, offset);
    let index = line_index(starts, offset);
    let start = starts[index];
    Position {
        line: index + 1,
        column: 1 + text[start..offset].chars().count(),
    }
}

pub(crate) fn align(text: &str, offset: usize) -> usize {
    let mut offset = offset.min(text.len());
    while !text.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOKENS: [&str; 10] = ["a", "Z", "\n", "\r\n", "\r", "é", "世", "😀", " ", "~"];

    fn xorshift32(state: &mut u32) -> u32 {
        let mut value = *state;
        value ^= value << 13;
        value ^= value >> 17;
        value ^= value << 5;
        *state = value;
        value
    }

    fn naive_position(text: &str, offset: usize) -> (usize, usize) {
        let bytes = text.as_bytes();
        let mut offset = offset.min(bytes.len());
        while offset > 0 && offset < bytes.len() && bytes[offset] & 0xC0 == 0x80 {
            offset -= 1;
        }
        let mut line = 1;
        let mut start = 0;
        let mut cursor = 0;
        while cursor < offset {
            match bytes[cursor] {
                b'\r' => {
                    let stop = if bytes.get(cursor + 1) == Some(&b'\n') {
                        cursor + 2
                    } else {
                        cursor + 1
                    };
                    if stop > offset {
                        break;
                    }
                    line += 1;
                    start = stop;
                    cursor = stop;
                }
                b'\n' => {
                    line += 1;
                    start = cursor + 1;
                    cursor += 1;
                }
                _ => cursor += 1,
            }
        }
        (line, 1 + text[start..offset].chars().count())
    }

    #[test]
    fn position_matches_naive_scan() {
        for case in 0..500u32 {
            let mut state = case + 1;
            let tokens = usize::try_from(xorshift32(&mut state) % 24).unwrap_or(0);
            let mut text = String::new();
            for _ in 0..tokens {
                let span = u32::try_from(TOKENS.len()).unwrap_or(1);
                let pick = usize::try_from(xorshift32(&mut state) % span).unwrap_or(0);
                text.push_str(TOKENS[pick]);
            }
            let index = LineIndex::new(&text);
            for offset in 0..=text.len() + 3 {
                let got = index.position(offset);
                let want = naive_position(&text, offset);
                assert_eq!(
                    (got.line, got.column),
                    want,
                    "case {case} offset {offset} text {text:?}"
                );
            }
        }
    }

    #[test]
    fn position_counts_scalars_not_bytes() {
        let index = LineIndex::new("é\n世x\r\nab\rc");
        assert_eq!(index.position(0), Position { line: 1, column: 1 });
        assert_eq!(index.position(2), Position { line: 1, column: 2 });
        assert_eq!(index.position(3), Position { line: 2, column: 1 });
        assert_eq!(index.position(6), Position { line: 2, column: 2 });
        assert_eq!(index.position(7), Position { line: 2, column: 3 });
        assert_eq!(index.position(8), Position { line: 2, column: 4 });
        assert_eq!(index.position(9), Position { line: 3, column: 1 });
        assert_eq!(index.position(11), Position { line: 3, column: 3 });
        assert_eq!(index.position(12), Position { line: 4, column: 1 });
        assert_eq!(index.position(99), Position { line: 4, column: 2 });
        assert_eq!(index.position(1), Position { line: 1, column: 1 });
    }

    #[test]
    fn utf16_column_counts_surrogate_pairs() {
        let index = LineIndex::new("a😀b\né");
        assert_eq!(index.utf16_column(0), 1);
        assert_eq!(index.utf16_column(1), 2);
        assert_eq!(index.utf16_column(5), 4);
        assert_eq!(index.utf16_column(6), 5);
        assert_eq!(index.utf16_column(7), 1);
        assert_eq!(index.utf16_column(9), 2);
    }

    #[test]
    fn repair_keeps_valid_input_borrowed() {
        let bytes = b"plain ascii\nand \xc3\xa9";
        let (text, first_bad) = repair_utf8(bytes);
        assert!(
            matches!(text, Cow::Borrowed(_)),
            "valid UTF-8 {bytes:?} must remain borrowed; observed {text:?}"
        );
        assert_eq!(first_bad, None);
        assert_eq!(text.as_ref(), "plain ascii\nand é");
    }

    #[test]
    fn repair_replaces_maximal_subparts() {
        let cases: [(&[u8], &str, usize); 4] = [
            (&[0xF0, 0x9F, 0x98], "\u{FFFD}", 0),
            (&[0xC0, 0x80], "\u{FFFD}\u{FFFD}", 0),
            (&[0xE2, 0x28, 0xA1], "\u{FFFD}(\u{FFFD}", 0),
            (b"ok\xE2\x82tail", "ok\u{FFFD}tail", 2),
        ];
        for (bytes, want, first_bad) in cases {
            let (text, got) = repair_utf8(bytes);
            assert!(
                matches!(text, Cow::Owned(_)),
                "invalid UTF-8 {bytes:?} must be repaired into owned text; observed {text:?}"
            );
            assert_eq!(text.as_ref(), want);
            assert_eq!(got, Some(first_bad));
        }
    }
}
