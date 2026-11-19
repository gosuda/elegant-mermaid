use super::*;

impl Parser<'_> {
    pub(super) fn peek(&self) -> Token {
        self.tokens.get(self.i).cloned().unwrap_or_else(|| {
            Token::new(
                K::Eof,
                Span {
                    start: self.src.len(),
                    end: self.src.len(),
                },
                TextVal::None,
            )
        })
    }
    pub(super) fn at(&self, kind: K) -> bool {
        self.peek().kind == kind
    }
    pub(super) fn any(&self, kinds: &[K]) -> bool {
        kinds.contains(&self.peek().kind)
    }
    pub(super) fn next(&mut self) -> Token {
        let token = self.peek();
        if self.i < self.tokens.len() {
            self.i += 1;
        }
        token
    }
    pub(super) fn accept(&mut self, kind: K) -> Option<Token> {
        if self.at(kind) {
            Some(self.next())
        } else {
            None
        }
    }
    pub(super) fn text(&self, token: &Token) -> String {
        token.text(self.src).to_owned()
    }
    pub(super) fn skip_spaces(&mut self) {
        while self.at(K::Space) {
            self.next();
        }
    }
    pub(super) fn trivia(&mut self) {
        while self.any(&[K::Space, K::Newline, K::Semi]) {
            self.next();
        }
    }
    pub(super) fn boundary(&self) -> bool {
        self.any(&[K::Eof, K::Newline, K::Semi])
    }
    pub(super) fn recover(&mut self) {
        while !self.boundary() {
            self.next();
        }
    }
    pub(super) fn last_end(&self) -> usize {
        self.i
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(self.peek().span.start, |t| t.span.end)
    }
    pub(super) fn plain(&mut self, code: &'static str, span: Span) {
        self.token_diag(code, span, "TOKEN");
    }
    pub(super) fn token_diag(&mut self, code: &'static str, span: Span, token: &str) {
        let (message, help) = diagnostic_row(code);
        let mut d = crate::syntax::flowchart::diagnostic(
            code,
            Severity::Error,
            message.replace("TOKEN", token),
            span,
        );
        d.help = help.to_owned();
        self.diags.push(d);
    }
    pub(super) fn unexpected(&mut self, names: &[&str]) {
        let token = self.peek();
        let message = format!(
            "unexpected {}, expected one of: {}",
            token.text(self.src),
            names.join(", ")
        );
        let mut d = crate::syntax::flowchart::diagnostic(
            "flowchart/unexpected-token",
            Severity::Error,
            message,
            token.span,
        );
        d.help = diagnostic_row("flowchart/unexpected-token").1.to_owned();
        self.diags.push(d);
    }
}
