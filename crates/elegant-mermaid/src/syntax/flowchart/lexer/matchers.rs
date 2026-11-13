use super::{
    Lexer, horizontal_space, js_space, line_end, marker_end, marker_start, unicode::UNICODE_RANGES,
};

impl Lexer<'_> {
    pub(super) fn bytes(&self) -> &[u8] {
        self.src.as_bytes()
    }
    pub(super) fn matches(&self, p: usize, n: usize, s: &str) -> bool {
        p + s.len() <= n && self.bytes().get(p..p + s.len()) == Some(s.as_bytes())
    }
    pub(super) fn run(&self, mut p: usize, n: usize, pred: impl Fn(u8) -> bool) -> usize {
        while p < n && pred(self.bytes()[p]) {
            p += 1;
        }
        p
    }
    pub(super) fn nonempty(&self, p: usize) -> Option<usize> {
        (p > self.pos).then_some(p)
    }
    pub(super) fn lit(&self, n: usize, s: &str) -> Option<usize> {
        if !self.matches(self.pos, n, s) {
            return None;
        }
        let end = self.pos + s.len();
        let b = s.as_bytes();
        if b.first().is_some_and(u8::is_ascii_alphanumeric)
            && b.last().is_some_and(u8::is_ascii_alphanumeric)
            && !self.boundary(end, n)
        {
            return None;
        }
        Some(end)
    }
    pub(super) fn boundary(&self, p: usize, n: usize) -> bool {
        p >= n || !(self.bytes()[p].is_ascii_alphanumeric() || self.bytes()[p] == b'_')
    }
    pub(super) fn keyword_then_space(&self, n: usize, s: &str) -> Option<usize> {
        if !self.matches(self.pos, n, s) {
            return None;
        }
        let p = self.pos + s.len();
        let end = self.run(p, n, js_space);
        (end > p).then_some(end)
    }
    pub(super) fn keyword_delimiter(&self, n: usize, s: &str, b: u8) -> Option<usize> {
        if !self.matches(self.pos, n, s) {
            return None;
        }
        let p = self.run(self.pos + s.len(), n, js_space);
        if p >= n || self.bytes()[p] != b {
            return None;
        }
        Some(self.run(p + 1, n, js_space))
    }
    pub(super) fn keyword_spaces_colon_spaces(&self, n: usize, s: &str) -> Option<usize> {
        self.keyword_delimiter(n, s, b':')
    }
    pub(super) fn keyword_spaces_brace(&self, n: usize, s: &str) -> Option<usize> {
        self.keyword_delimiter(n, s, b'{')
    }
    pub(super) fn end_keyword(&self, n: usize) -> Option<usize> {
        let p = self.pos + 3;
        if !self.matches(self.pos, n, "end") || !self.boundary(p, n) {
            return None;
        }
        Some(self.run(p, n, horizontal_space))
    }
    pub(super) fn href_keyword(&self, n: usize) -> Option<usize> {
        let p = self.pos + 4;
        (self.matches(self.pos, n, "href") && p < n && js_space(self.bytes()[p])).then_some(p + 1)
    }
    pub(super) fn dir_no_dir(&self, n: usize) -> Option<usize> {
        let mut p = self.pos;
        while p < n && js_space(self.bytes()[p]) {
            if matches!(self.bytes()[p], b'\n' | b'\r') {
                return Some(p + 1);
            }
            p += 1;
        }
        (p > self.pos && p >= n).then_some(p)
    }
    pub(super) fn dir_keyword_rule(&self, n: usize, s: &str) -> Option<usize> {
        let p = self.run(self.pos, n, horizontal_space);
        self.matches(p, n, s).then_some(p + s.len())
    }
    pub(super) fn link_id_rule(&self, n: usize) -> Option<usize> {
        let p = self.run(self.pos, n, |b| !js_space(b) && !b"@\"[](){}|".contains(&b));
        if p == self.pos
            || p + 1 >= n
            || self.bytes()[p] != b'@'
            || matches!(self.bytes()[p + 1], b'{' | b'"')
        {
            return None;
        }
        Some(p + 1)
    }
    pub(super) fn num_rule(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| b.is_ascii_digit()))
    }
    pub(super) fn link_start(&self, n: usize) -> usize {
        let p = self.run(self.pos, n, js_space);
        if p < n && marker_start(self.bytes()[p]) {
            p + 1
        } else {
            p
        }
    }
    pub(super) fn solid_link(&self, n: usize, b: u8) -> Option<usize> {
        let p = self.link_start(n);
        let end = self.run(p, n, |c| c == b);
        let count = end - p;
        if count >= 2 && end < n && marker_end(self.bytes()[end]) {
            return Some(self.run(end + 1, n, js_space));
        }
        (count >= 3).then(|| self.run(end, n, js_space))
    }
    pub(super) fn solid_start(&self, n: usize, s: &str) -> Option<usize> {
        let p = self.link_start(n);
        self.matches(p, n, s)
            .then(|| self.run(p + s.len(), n, js_space))
    }
    pub(super) fn link_rule(&self, n: usize) -> Option<usize> {
        self.solid_link(n, b'-')
    }
    pub(super) fn thick_link_rule(&self, n: usize) -> Option<usize> {
        self.solid_link(n, b'=')
    }
    pub(super) fn start_link_rule(&self, n: usize) -> Option<usize> {
        self.solid_start(n, "--")
    }
    pub(super) fn thick_start_link_rule(&self, n: usize) -> Option<usize> {
        self.solid_start(n, "==")
    }
    pub(super) fn dotted_start_link_rule(&self, n: usize) -> Option<usize> {
        self.solid_start(n, "-.")
    }
    pub(super) fn dotted_link_rule(&self, n: usize) -> Option<usize> {
        let mut p = self.link_start(n);
        if p < n && self.bytes()[p] == b'-' {
            p += 1;
        }
        let end = self.run(p, n, |b| b == b'.');
        if end == p || end >= n || self.bytes()[end] != b'-' {
            return None;
        }
        p = end + 1;
        if p < n && marker_end(self.bytes()[p]) {
            p += 1;
        }
        Some(self.run(p, n, js_space))
    }
    pub(super) fn invisible_link_rule(&self, n: usize) -> Option<usize> {
        let p = self.run(self.pos, n, js_space);
        if !self.matches(p, n, "~~~") {
            return None;
        }
        Some(self.run(self.run(p + 3, n, |b| b == b'~'), n, js_space))
    }
    pub(super) fn node_string_rule(&self, n: usize) -> Option<usize> {
        let mut p = self.pos;
        while p < n && self.node_byte(p, n) {
            p += 1;
        }
        self.nonempty(p)
    }
    pub(super) fn node_byte(&self, p: usize, n: usize) -> bool {
        let b = self.bytes()[p];
        if b.is_ascii_alphanumeric() || b"!\"#$%&'*+.`?\\_/".contains(&b) {
            return true;
        }
        match b {
            b'-' => p + 1 < n && !b">-.".contains(&self.bytes()[p + 1]),
            b'=' => p + 1 >= n || self.bytes()[p + 1] != b'=',
            _ => false,
        }
    }
    pub(super) fn unicode_text_rule(&self, n: usize) -> Option<usize> {
        let c = self.src.get(self.pos..n)?.chars().next()?;
        let r = c as u32;
        let i = UNICODE_RANGES.partition_point(|&(_, hi)| hi < r);
        UNICODE_RANGES
            .get(i)
            .filter(|&&(lo, _)| lo <= r)
            .map(|_| self.pos + c.len_utf8())
    }
    pub(super) fn newline_rule(&self, n: usize) -> Option<usize> {
        let mut p = self.pos;
        while let Some(end) = line_end(self.bytes(), p) {
            if end > n {
                break;
            }
            p = end;
        }
        self.nonempty(p)
    }
    pub(super) fn space_rule(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, horizontal_space))
    }
    pub(super) fn acc_value_run(&self, n: usize) -> Option<usize> {
        Some(self.run(self.pos, n, |b| !b"\n\r;#".contains(&b)))
    }
    pub(super) fn acc_block_run(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| b != b'}'))
    }
    pub(super) fn string_run(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| b != b'"'))
    }
    pub(super) fn md_string_run(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| b != b'"' && b != b'`'))
    }
    pub(super) fn one_byte_unless(&self, n: usize, b: u8) -> Option<usize> {
        (!(self.bytes()[self.pos] == b && self.pos + 1 < n && self.bytes()[self.pos + 1] == b))
            .then_some(self.pos + 1)
    }
    pub(super) fn callback_name_run(&self, n: usize) -> Option<usize> {
        if self.bytes()[self.pos] == b'"' {
            return None;
        }
        self.nonempty(self.run(self.pos, n, |b| b != b'('))
    }
    pub(super) fn callback_args_run(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| b != b')'))
    }
    pub(super) fn empty_call_args(&self, n: usize) -> Option<usize> {
        if self.bytes()[self.pos] != b'(' {
            return None;
        }
        let p = self.run(self.pos + 1, n, js_space);
        (p < n && self.bytes()[p] == b')').then_some(p + 1)
    }
    pub(super) fn shape_plain_run(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| !b"}^\"".contains(&b)))
    }
    pub(super) fn shape_quoted_run(&self, n: usize) -> Option<usize> {
        self.string_run(n)
    }
    pub(super) fn ellipse_text_run(&self, n: usize) -> Option<usize> {
        if !b"()[]{}".contains(&self.bytes()[self.pos]) {
            return Some(self.pos + 1);
        }
        let mut p = self.pos;
        while self.matches(p, n, "-!)") {
            p += 3;
        }
        self.nonempty(p)
    }
    pub(super) fn ellipse_end_rule(&self, n: usize) -> Option<usize> {
        let p = self.pos;
        (p + 1 < n && b"-/)".contains(&self.bytes()[p]) && self.bytes()[p + 1] == b')')
            .then_some(p + 2)
    }
    pub(super) fn trap_end_rule(&self, n: usize) -> Option<usize> {
        self.matches(self.pos, n, "\\]").then_some(self.pos + 2)
    }
    pub(super) fn inv_trap_end_rule(&self, n: usize) -> Option<usize> {
        self.matches(self.pos, n, "/]").then_some(self.pos + 2)
    }
    pub(super) fn trap_text_run(&self, n: usize) -> Option<usize> {
        let p = self.run(self.pos, n, |b| !b"\\[](){}/".contains(&b));
        if p == self.pos
            && p + 1 < n
            && b"/\\".contains(&self.bytes()[p])
            && self.bytes()[p + 1] != b']'
        {
            return Some(p + 1);
        }
        self.nonempty(p)
    }
    pub(super) fn text_run(&self, n: usize) -> Option<usize> {
        let mut p = self.pos;
        let mut in_tag = false;
        while p < n {
            let b = self.bytes()[p];
            if b"[](){}|".contains(&b) || b == b'"' && !in_tag {
                break;
            }
            if b == b'<' {
                in_tag = true;
            }
            if b == b'>' {
                in_tag = false;
            }
            p += 1;
        }
        self.nonempty(p)
    }
    pub(super) fn direction_statement(&self, n: usize, s: &str) -> Option<usize> {
        let stop = self.run(self.pos, n, |b| b != b'\n');
        for i in self.pos..stop {
            if !self.matches(i, stop, "direction") {
                continue;
            }
            let p = self.run(i + 9, stop, js_space);
            if p > i + 9 && self.matches(p, stop, s) {
                return Some(self.run(p, n, |b| b != b'\n'));
            }
        }
        None
    }
    pub(super) fn colon_run(&self, n: usize) -> Option<usize> {
        self.matches(self.pos, n, ":::").then_some(self.pos + 3)
    }
    pub(super) fn any_space_byte(&self, n: usize) -> Option<usize> {
        (self.pos < n && js_space(self.bytes()[self.pos])).then_some(self.pos + 1)
    }
    pub(super) fn any_non_space(&self, n: usize) -> Option<usize> {
        self.nonempty(self.run(self.pos, n, |b| !js_space(b)))
    }
}
