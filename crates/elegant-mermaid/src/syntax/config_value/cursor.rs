use super::*;

impl<'a> Cfg<'a> {
    pub(super) fn new(src: &'a str, start: usize, end: usize, json: bool) -> Cfg<'a> {
        Cfg {
            src,
            b: src.as_bytes(),
            start,
            end,
            pos: start,
            depth: 0,
            yaml_value_indent: None,
            json,
            stop: false,
            diags: Vec::new(),
            starts: Vec::new(),
        }
    }

    pub(super) fn raw(&self, i: usize) -> Option<u8> {
        self.b.get(i).copied()
    }

    pub(super) fn at(&self, i: usize) -> Option<u8> {
        self.b
            .get(i)
            .map(|c| if self.json && *c == b'\'' { b'"' } else { *c })
    }

    pub(super) fn cur(&self) -> Option<u8> {
        self.at(self.pos)
    }

    pub(super) fn at_end(&self) -> bool {
        self.pos >= self.end
    }

    pub(super) fn text(&self, a: usize, b: usize) -> String {
        self.src.get(a..b).unwrap_or_default().to_string()
    }

    pub(super) fn eol(&self, i: usize) -> usize {
        eol_len(self.b, i)
    }

    pub(super) fn content_end(&self, from: usize) -> usize {
        line_content_end(self.b, from, self.end)
    }

    pub(super) fn token_span(&self, at: usize) -> Span {
        let p = at.min(self.end).max(self.start);
        if p >= self.end {
            return Span { start: p, end: p };
        }
        let e = match self.raw(p).unwrap_or(0) {
            b'\n' => p + 1,
            b'\r' => p + self.eol(p),
            b' ' | b'\t' => p + 1,
            _ => self.token_run(p),
        };
        Span { start: p, end: e }
    }

    pub(super) fn token_run(&self, p: usize) -> usize {
        let mut j = p;
        while j < self.end && matches!(self.raw(j), Some(c) if !is_ws_byte(c)) {
            j += 1;
        }
        j
    }

    pub(super) fn err(&mut self, code: &'static str, msg: &str, span: Span) {
        self.diags.push(Diagnostic {
            code,
            severity: Severity::Error,
            message: msg.to_string(),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        });
    }

    pub(super) fn fail(&mut self, at: usize) {
        let span = self.token_span(at);
        self.err(C_MALFORMED, "malformed config value", span);
        self.stop = true;
    }

    pub(super) fn enter(&mut self, open: usize) -> bool {
        if self.depth >= 64 {
            self.err(
                C_DEPTH,
                "nesting depth exceeds 64",
                Span {
                    start: open,
                    end: open + 1,
                },
            );
            self.stop = true;
            return false;
        }
        self.depth += 1;
        true
    }

    pub(super) fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    pub(super) fn skip_inline_ws(&mut self) {
        while matches!(self.cur(), Some(b' ') | Some(b'\t')) {
            self.pos += 1;
        }
    }

    pub(super) fn boundary(&self, i: usize) -> bool {
        matches!(
            self.raw(i),
            Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
        )
    }

    pub(super) fn map_boundary(&self, i: usize) -> bool {
        i >= self.end || self.boundary(i)
    }
}
