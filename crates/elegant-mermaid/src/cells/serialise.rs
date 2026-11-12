use super::{Canvas, Cell, Charset, ColorMode, Label, Rgb, Token, colour, join};
impl Cell {
    fn glyph(&self, charset: Charset) -> char {
        if self.symbol != 0 {
            return char::from_u32(self.symbol).unwrap_or(' ');
        }
        if self.mask != 0 {
            return join::glyph(charset, self.style, self.mask);
        }
        join::braille(self.dots, charset)
    }
    fn is_space(&self, charset: Charset) -> bool {
        match &self.label {
            Label::Cluster { text, .. } => text == " ",
            Label::Continuation => false,
            Label::None => self.glyph(charset) == ' ',
        }
    }
    fn colour_token(&self) -> Token {
        let token = if matches!(self.label, Label::Cluster { .. }) {
            self.label_token
        } else {
            self.token
        }
        .unwrap_or(Token::Fg);
        if token == Token::Bg { Token::Fg } else { token }
    }
    fn write_text(&self, out: &mut String, charset: Charset) {
        match &self.label {
            Label::Continuation => (),
            Label::Cluster { text, .. } => out.push_str(text),
            Label::None => out.push(self.glyph(charset)),
        }
    }
}
impl Canvas {
    pub fn serialise(
        &self,
        charset: Charset,
        mode: ColorMode,
        lookup: impl Fn(Token) -> Rgb,
    ) -> String {
        let mut out = String::new();
        for y in 0..self.height() {
            self.write_row(&mut out, y, charset, mode, &lookup)
        }
        out
    }
    fn write_row(
        &self,
        out: &mut String,
        y: i32,
        charset: Charset,
        mode: ColorMode,
        lookup: &impl Fn(Token) -> Rgb,
    ) {
        let mut end = self.width();
        while end > 0 && self.cell(end - 1, y).is_some_and(|c| c.is_space(charset)) {
            end -= 1
        }
        let mut current = Token::Fg;
        for x in 0..end {
            let Some(cell) = self.cell(x, y) else {
                continue;
            };
            let token = cell.colour_token();
            if mode != ColorMode::None
                && !cell.is_space(charset)
                && cell.label != Label::Continuation
                && token != current
            {
                out.push_str(&colour::sgr(lookup(token), token, mode));
                current = token
            }
            cell.write_text(out, charset);
        }
        if mode != ColorMode::None && current != Token::Fg {
            out.push_str("\x1b[39m")
        }
        out.push('\n');
    }
}
