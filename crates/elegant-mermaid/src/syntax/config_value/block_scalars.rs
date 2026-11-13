use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn plain_value_text(&mut self) -> String {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            let c = self.raw(j);
            if matches!(c, Some(b' ') | Some(b'\t')) && self.raw(j + 1) == Some(b'#') {
                break;
            }
            j += 1;
        }
        self.pos = j;
        let te = trim_end(self.b, from, j);
        let text = self.text(from, te);
        self.fold_plain_continuations(text, j, to)
    }

    pub(super) fn fold_plain_continuations(
        &mut self,
        mut text: String,
        mut j: usize,
        mut to: usize,
    ) -> String {
        let n = self.yaml_value_indent.unwrap_or(0);
        let mut next = to + self.eol(to);
        let mut blanks = 0;
        while j == to && next < self.end {
            let line = self.line_scan(next);
            if self.line_blank(&line) {
                blanks += 1;
                next = line.next;
                continue;
            }
            if line.col <= n || self.raw(line.content) == Some(b'#') {
                break;
            }
            self.pos = line.content;
            if self.sequence_start() || self.plain_line_kind() == LineKind::Entry {
                self.pos = j;
                break;
            }
            let line = self.take_line(next);
            if self.stop {
                break;
            }
            self.pos = line.content;
            let part = self.plain_value_line();
            if blanks == 0 {
                text.push(' ');
            } else {
                text.extend(std::iter::repeat_n('\n', blanks));
            }
            text.push_str(&part);
            blanks = 0;
            j = self.pos;
            if j != line.eol_pos {
                break;
            }
            to = line.eol_pos;
            next = line.next;
        }
        text
    }

    pub(super) fn plain_value_line(&mut self) -> String {
        let from = self.pos;
        let to = self.content_end(from);
        let mut j = from;
        while j < to {
            if matches!(self.raw(j), Some(b' ' | b'\t')) && self.raw(j + 1) == Some(b'#') {
                break;
            }
            j += 1;
        }
        self.pos = j;
        self.text(from, trim_end(self.b, from, j))
    }
    pub(super) fn finish_line(&mut self) -> Option<()> {
        if self.stop {
            return None;
        }
        self.skip_inline_ws();
        let e = self.content_end(self.pos);
        if self.pos < e {
            if self.raw(self.pos) == Some(b'#') {
                self.pos = e;
            } else {
                self.fail(self.pos);
                return None;
            }
        }
        self.pos = e + self.eol(e);
        Some(())
    }

    pub(super) fn block_scalar(&mut self, n: usize) -> Option<String> {
        let (folded, chomp) = self.block_header()?;
        self.finish_line()?;
        let (leading, parts) = self.block_content(n);
        if self.stop {
            return None;
        }
        Some(assemble_block(folded, chomp, leading, &parts))
    }

    pub(super) fn block_header(&mut self) -> Option<(bool, u8)> {
        let folded = self.raw(self.pos)? == b'>';
        self.pos += 1;
        let mut chomp = b'c';
        match self.raw(self.pos) {
            Some(c @ (b'-' | b'+')) => {
                chomp = c;
                self.pos += 1;
            }
            Some(c) if c.is_ascii_digit() => {
                self.err(
                    C_MALFORMED,
                    "block scalar indentation indicator is not supported",
                    Span {
                        start: self.pos,
                        end: self.pos + 1,
                    },
                );
                self.stop = true;
                return None;
            }
            _ => {}
        }
        Some((folded, chomp))
    }

    pub(super) fn block_content(&mut self, n: usize) -> (usize, Vec<Option<Vec<u8>>>) {
        let mut leading = 0usize;
        let mut parts: Vec<Option<Vec<u8>>> = Vec::new();
        let mut m = 0usize;
        let mut m_set = false;
        while !self.stop && self.pos < self.end {
            let l = self.take_line(self.pos);
            if self.stop {
                break;
            }
            if self.line_blank(&l) {
                if m_set {
                    parts.push(None);
                } else {
                    leading += 1;
                }
                self.pos = l.next;
                continue;
            }
            if !m_set {
                if l.col <= n {
                    break;
                }
                m = l.col;
                m_set = true;
            } else if l.col < m {
                break;
            }
            let cs = (l.from + m).min(l.eol_pos);
            parts.push(Some(self.b.get(cs..l.eol_pos).unwrap_or_default().to_vec()));
            self.pos = l.next;
        }
        (leading, parts)
    }
}
