use std::borrow::Cow;

use crate::source::Span;

const TAB_WIDTH: usize = 4;
const MAX_INDENT: usize = 3;
const MAX_LIST_DIGITS: usize = 9;
const INFO_WORDS: [&[u8]; 3] = [b"mermaid", b"mmd", b"{mermaid}"];
const COLON_OPEN: &[u8] = b":::mermaid";
const COLON_CLOSE: &[u8] = b":::";

/// A Mermaid block found in a Markdown host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block<'src> {
    pub source: Cow<'src, [u8]>,
    pub span: Span,
    pub lines: Vec<BlockLine>,
}

/// One line of a block's `source`, with its position in the host.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockLine {
    pub host_offset: usize,
    pub block_offset: usize,
    pub len: usize,
}

impl Block<'_> {
    /// Maps a byte offset in `source` to the host file offset.
    ///
    /// The offset is clamped to `0..=source.len()`. An offset on a line ending
    /// maps to the host position just after that line's content. A block with
    /// no lines maps every offset to the start of its span.
    pub fn host_offset(&self, block_offset: usize) -> usize {
        let offset = block_offset.min(self.source.len());
        let index = match self
            .lines
            .binary_search_by(|line| line.block_offset.cmp(&offset))
        {
            Ok(index) => index,
            Err(0) => return self.span.start,
            Err(index) => index - 1,
        };
        let line = self.lines[index];
        line.host_offset + (offset - line.block_offset).min(line.len)
    }
}

/// Returns every Mermaid block of `source`, in host order.
pub fn blocks(source: &[u8]) -> Vec<Block<'_>> {
    let lines = line_table(source);
    let mut frames: Vec<Frame> = Vec::new();
    let mut open: Option<OpenBlock> = None;
    let mut found: Vec<Block<'_>> = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let line = lines[index];
        let (cursor, matched) = strip_frames(source, line, &frames);
        if matched < frames.len() {
            frames.truncate(matched);
            if let Some(block) = open.take()
                && block.accepted()
            {
                found.push(finish(source, block));
            }
            continue;
        }
        index += 1;
        let mut block = match open.take() {
            Some(block) => block,
            None => {
                open = detect_line(source, line, cursor, &mut frames);
                continue;
            }
        };
        if !block.closes(source, cursor, line.content_end) {
            block.push(line, cursor);
            open = Some(block);
            continue;
        }
        block.close(line.content_end);
        frames.truncate(block.frame_depth);
        if block.accepted() {
            found.push(finish(source, block));
        }
    }
    if let Some(block) = open
        && block.accepted()
    {
        found.push(finish(source, block));
    }
    found
}

#[derive(Debug, Clone, Copy)]
struct Line {
    start: usize,
    content_end: usize,
    end: usize,
}

#[derive(Debug, Clone, Copy)]
struct ContentLine {
    line_start: usize,
    content_start: usize,
    content_end: usize,
    end: usize,
}

#[derive(Debug, Clone, Copy)]
enum Frame {
    Quote,
    Item { indent: usize },
    Colon,
}

#[derive(Debug, Clone, Copy)]
enum FenceChar {
    Backtick,
    Tilde,
}

#[derive(Debug, Clone, Copy)]
struct Fence {
    ch: FenceChar,
    len: usize,
    mermaid: bool,
}

impl Fence {
    fn byte(self) -> u8 {
        match self.ch {
            FenceChar::Backtick => b'`',
            FenceChar::Tilde => b'~',
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum BlockKind {
    Fence(Fence),
    Colon,
}

struct OpenBlock {
    kind: BlockKind,
    frame_depth: usize,
    span_start: usize,
    span_end: usize,
    content: Vec<ContentLine>,
}

impl OpenBlock {
    fn accepted(&self) -> bool {
        match self.kind {
            BlockKind::Fence(fence) => fence.mermaid,
            BlockKind::Colon => true,
        }
    }

    fn new(kind: BlockKind, line: Line, frame_depth: usize) -> OpenBlock {
        OpenBlock {
            kind,
            frame_depth,
            span_start: line.start,
            span_end: line.content_end,
            content: Vec::new(),
        }
    }

    fn closes(&self, source: &[u8], cursor: usize, end: usize) -> bool {
        match self.kind {
            BlockKind::Fence(fence) => fence_close(source, cursor, end, fence),
            BlockKind::Colon => colon_close(source, cursor, end),
        }
    }

    fn push(&mut self, line: Line, cursor: usize) {
        self.content.push(ContentLine {
            line_start: line.start,
            content_start: cursor,
            content_end: line.content_end,
            end: line.end,
        });
        self.span_end = line.end;
    }

    fn close(&mut self, end: usize) {
        self.span_end = end;
    }
}

fn line_table(source: &[u8]) -> Vec<Line> {
    let mut lines = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < source.len() {
        match source[index] {
            b'\r' => {
                lines.push(Line {
                    start,
                    content_end: index,
                    end: index
                        + if source.get(index + 1) == Some(&b'\n') {
                            2
                        } else {
                            1
                        },
                });
                index += if source.get(index + 1) == Some(&b'\n') {
                    2
                } else {
                    1
                };
                start = index;
            }
            b'\n' => {
                lines.push(Line {
                    start,
                    content_end: index,
                    end: index + 1,
                });
                index += 1;
                start = index;
            }
            _ => index += 1,
        }
    }
    if start < source.len() {
        lines.push(Line {
            start,
            content_end: source.len(),
            end: source.len(),
        });
    }
    lines
}

fn strip_frames(source: &[u8], line: Line, frames: &[Frame]) -> (usize, usize) {
    let mut cursor = line.start;
    for (index, frame) in frames.iter().enumerate() {
        match strip_frame(source, cursor, line.content_end, *frame) {
            Some(next) => cursor = next,
            None => return (cursor, index),
        }
    }
    (cursor, frames.len())
}

fn strip_frame(source: &[u8], cursor: usize, end: usize, frame: Frame) -> Option<usize> {
    match frame {
        Frame::Quote => after_quote(source, cursor),
        Frame::Colon => Some(cursor),
        Frame::Item { indent } => strip_item(source, cursor, end, indent),
    }
}

fn strip_item(source: &[u8], cursor: usize, end: usize, indent: usize) -> Option<usize> {
    if blank(source, cursor, end) {
        return Some(end);
    }
    let mut column = 0;
    let mut index = cursor;
    while column < indent && index < end {
        match source[index] {
            b' ' => {
                column += 1;
                index += 1;
            }
            b'\t' => {
                column = next_tab(column);
                index += 1;
            }
            _ => return None,
        }
    }
    (column >= indent).then_some(index)
}

fn next_tab(column: usize) -> usize {
    (column / TAB_WIDTH + 1) * TAB_WIDTH
}

fn detect_line(
    source: &[u8],
    line: Line,
    start: usize,
    frames: &mut Vec<Frame>,
) -> Option<OpenBlock> {
    let mut cursor = start;
    loop {
        if let Some(next) = quote_marker(source, cursor, line.content_end) {
            frames.push(Frame::Quote);
            cursor = next;
        } else if let Some((next, indent)) = list_marker(source, cursor, line.content_end) {
            frames.push(Frame::Item { indent });
            cursor = next;
        } else if colon_open(source, cursor, line.content_end) {
            let depth = frames.len();
            frames.push(Frame::Colon);
            return Some(OpenBlock::new(BlockKind::Colon, line, depth));
        } else {
            let fence = fence_open(source, cursor, line.content_end)?;
            return Some(OpenBlock::new(BlockKind::Fence(fence), line, frames.len()));
        }
    }
}

fn quote_marker(source: &[u8], from: usize, end: usize) -> Option<usize> {
    let marker = skip_spaces(source, from, end, MAX_INDENT);
    after_quote(source, marker)
}

fn after_quote(source: &[u8], cursor: usize) -> Option<usize> {
    if source.get(cursor) != Some(&b'>') {
        return None;
    }
    let after = cursor + 1;
    Some(after + usize::from(source.get(after) == Some(&b' ')))
}

fn list_marker(source: &[u8], from: usize, end: usize) -> Option<(usize, usize)> {
    let start = skip_spaces(source, from, end, MAX_INDENT);
    let width = list_marker_width(source, start, end)?;
    let after = start + width;
    let mut column = after - from;
    if after < end && !matches!(source[after], b' ' | b'\t') {
        return None;
    }
    let mut index = after;
    while index < end {
        match source[index] {
            b' ' => {
                column += 1;
                index += 1;
            }
            b'\t' => {
                column = next_tab(column);
                index += 1;
            }
            _ => break,
        }
    }
    Some((index, column))
}

fn list_marker_width(source: &[u8], start: usize, end: usize) -> Option<usize> {
    if start >= end {
        return None;
    }
    match source[start] {
        b'-' | b'*' | b'+' => Some(1),
        b'0'..=b'9' => {
            let mut index = start;
            while index < end && source[index].is_ascii_digit() {
                index += 1;
            }
            if index - start > MAX_LIST_DIGITS || index >= end {
                return None;
            }
            match source[index] {
                b'.' | b')' => Some(index + 1 - start),
                _ => None,
            }
        }
        _ => None,
    }
}

fn fence_open(source: &[u8], from: usize, end: usize) -> Option<Fence> {
    let start = skip_spaces(source, from, end, MAX_INDENT);
    let byte = *source.get(start)?;
    if start >= end {
        return None;
    }
    let ch = match byte {
        b'`' => FenceChar::Backtick,
        b'~' => FenceChar::Tilde,
        _ => return None,
    };
    let mut index = start;
    while index < end && source[index] == byte {
        index += 1;
    }
    let len = index - start;
    if len < 3 {
        return None;
    }
    Some(Fence {
        ch,
        len,
        mermaid: info_word(source, index, end),
    })
}

fn info_word(source: &[u8], from: usize, end: usize) -> bool {
    let start = skip_blank(source, from, end);
    let mut stop = start;
    while stop < end && !matches!(source[stop], b' ' | b'\t') {
        stop += 1;
    }
    let word = &source[start..stop];
    INFO_WORDS
        .iter()
        .any(|known| word.eq_ignore_ascii_case(known))
}

fn fence_close(source: &[u8], from: usize, end: usize, fence: Fence) -> bool {
    let start = skip_spaces(source, from, end, MAX_INDENT);
    let byte = fence.byte();
    let mut index = start;
    while index < end && source[index] == byte {
        index += 1;
    }
    if index - start < fence.len {
        return false;
    }
    blank(source, index, end)
}

fn colon_open(source: &[u8], from: usize, end: usize) -> bool {
    let rest = match source.get(from.min(end)..end) {
        Some(rest) => rest,
        None => return false,
    };
    match rest.strip_prefix(COLON_OPEN) {
        Some(tail) => blank(tail, 0, tail.len()),
        None => false,
    }
}

fn colon_close(source: &[u8], from: usize, end: usize) -> bool {
    let rest = match source.get(from.min(end)..end) {
        Some(rest) => rest,
        None => return false,
    };
    match rest.strip_prefix(COLON_CLOSE) {
        Some(tail) => blank(tail, 0, tail.len()),
        None => false,
    }
}

fn skip_spaces(source: &[u8], from: usize, end: usize, limit: usize) -> usize {
    let mut index = from;
    let mut count = 0;
    while count < limit && index < end && source[index] == b' ' {
        index += 1;
        count += 1;
    }
    index
}

fn skip_blank(source: &[u8], from: usize, end: usize) -> usize {
    let mut index = from;
    while index < end && matches!(source[index], b' ' | b'\t') {
        index += 1;
    }
    index
}

fn blank(source: &[u8], from: usize, end: usize) -> bool {
    from <= end && skip_blank(source, from, end) == end
}

fn finish(source: &[u8], block: OpenBlock) -> Block<'_> {
    let lines = line_records(&block);
    let text = if block.frame_depth == 0 {
        match (block.content.first(), block.content.last()) {
            (Some(first), Some(last)) => Cow::Borrowed(&source[first.content_start..last.end]),
            _ => Cow::Borrowed(&source[block.span_start..block.span_start]),
        }
    } else {
        Cow::Owned(join(source, &block.content))
    };
    Block {
        source: text,
        span: Span {
            start: block.span_start,
            end: block.span_end,
        },
        lines,
    }
}

fn line_records(block: &OpenBlock) -> Vec<BlockLine> {
    let mut out = Vec::with_capacity(block.content.len());
    let mut offset = 0;
    let mut previous: Option<ContentLine> = None;
    for line in &block.content {
        if let Some(prev) = previous {
            offset += line.line_start - prev.content_end;
        }
        out.push(BlockLine {
            host_offset: line.content_start,
            block_offset: offset,
            len: line.content_end - line.content_start,
        });
        offset += line.content_end - line.content_start;
        previous = Some(*line);
    }
    out
}

fn join(source: &[u8], content: &[ContentLine]) -> Vec<u8> {
    let mut out = Vec::new();
    for line in content {
        out.extend_from_slice(&source[line.content_start..line.end]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn markdown_go_cases() {
        let cases: &[(&[u8], &[u8])] = &[
            (b"```mermaid\nflowchart LR\n```\n", b"flowchart LR\n"),
            (b"~~~mmd\nx\n~~~~\n", b"x\n"),
            (b"```Mermaid\nx", b"x"),
            (b"> ```MMD\n> x\n> ```\ny\n", b"x\n"),
            (b"- x\n  ```mermaid\n  x\n  ```\n", b"x\n"),
            (
                b"> - x\n>   ```mermaid\n>   flowchart LR\n>     A --> B\n>   ```\n",
                b"flowchart LR\n  A --> B\n",
            ),
            (b"- x\n  > ```mermaid\n  > x\n  > ```\n", b"x\n"),
            (b"-\tx\n\t```mermaid\n\tx\n\t```\n", b"x\n"),
            (b":::mermaid\nx\n:::\n", b"x\n"),
            (b"```{mermaid}\r\nx\r\n```\r\n", b"x\r\n"),
            (b"> ```mermaid\n> x\ny\n", b"x\n"),
            (b"```mermaid\n```\n", b""),
        ];
        let spans = [
            (0, 27),
            (0, 13),
            (0, 12),
            (0, 18),
            (4, 26),
            (6, 59),
            (4, 32),
            (4, 23),
            (0, 16),
            (0, 20),
            (0, 17),
            (0, 14),
        ];
        let line_tables: &[&[(usize, usize, usize)]] = &[
            &[(11, 0, 12)],
            &[(7, 0, 1)],
            &[(11, 0, 1)],
            &[(11, 0, 1)],
            &[(19, 0, 1)],
            &[(25, 0, 12), (42, 13, 9)],
            &[(23, 0, 1)],
            &[(17, 0, 1)],
            &[(11, 0, 1)],
            &[(14, 0, 1)],
            &[(15, 0, 1)],
            &[],
        ];
        for (index, (host, expected)) in cases.iter().enumerate() {
            let found = blocks(host);
            assert_eq!(found.len(), 1);
            assert_eq!(found[0].source.as_ref(), *expected);
            assert_eq!((found[0].span.start, found[0].span.end), spans[index]);
            let lines: Vec<_> = found[0]
                .lines
                .iter()
                .map(|line| (line.host_offset, line.block_offset, line.len))
                .collect();
            assert_eq!(lines, line_tables[index]);
            mapping(host);
        }
    }

    #[test]
    fn markdown_nested_reference() {
        let host = b"> - x\n>   ```mermaid\n>   flowchart LR\n>     A --> B\n>   ```\n";
        let found = blocks(host);
        let block = &found[0];
        assert_eq!(block.span, Span { start: 6, end: 59 });
        assert_eq!(
            block.lines,
            vec![
                BlockLine {
                    host_offset: 25,
                    block_offset: 0,
                    len: 12
                },
                BlockLine {
                    host_offset: 42,
                    block_offset: 13,
                    len: 9
                },
            ]
        );
        assert!(
            matches!(block.source, Cow::Owned(_)),
            "container prefixes require owned source; host={host:?}, source={:?}",
            block.source
        );
        let top = blocks(b"```mermaid\nx\n```\n");
        assert!(
            matches!(top[0].source, Cow::Borrowed(_)),
            "top-level fence must borrow source; observed {:?}",
            top[0].source
        );
    }

    #[test]
    fn markdown_ignores_other_fences() {
        let found = blocks(b"```text\n```mermaid\nx\n```\n~~~mermaid\ny\n~~~\n");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].source.as_ref(), b"y\n");
    }

    fn mapping(host: &[u8]) {
        for block in blocks(host) {
            assert!(
                block.span.start <= block.span.end && block.span.end <= host.len(),
                "block span {:?} exceeds host {host:?}",
                block.span
            );
            for line in &block.lines {
                for delta in 0..line.len {
                    assert_eq!(
                        block.host_offset(line.block_offset + delta),
                        line.host_offset + delta
                    );
                    assert_eq!(
                        block.source[line.block_offset + delta],
                        host[line.host_offset + delta]
                    );
                }
                assert_eq!(
                    block.host_offset(line.block_offset + line.len),
                    line.host_offset + line.len
                );
                if block
                    .source
                    .get(line.block_offset + line.len..)
                    .is_some_and(|tail| tail.starts_with(b"\r\n"))
                {
                    assert_eq!(
                        block.host_offset(line.block_offset + line.len + 1),
                        line.host_offset + line.len
                    );
                }
            }
            if block.lines.is_empty() {
                assert_eq!(block.host_offset(usize::MAX), block.span.start);
            }
        }
    }

    #[test]
    fn markdown_seeded_byte_maps() {
        let shapes = [
            "```mermaid\nx\n```\n",
            "> ```mmd\n> x\n> ```\n",
            "- x\n  ~~~mermaid\n  x\n  ~~~\n",
            ":::mermaid\nx\n:::\n",
            "```text\nx\n```\n",
        ];
        for seed in 1..=2000u32 {
            let mut state = seed;
            let mut host = String::new();
            for _ in 0..8 {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                host.push_str(shapes[state as usize % shapes.len()]);
            }
            mapping(host.as_bytes());
        }
    }
}
