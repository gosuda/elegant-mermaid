use super::{Canvas, Cell, Charset, ColorMode, Label, Rgb, Token, colour, join};

pub(super) fn printable(ch: char) -> char {
    if ch <= '\u{1f}' || ('\u{7f}'..='\u{9f}').contains(&ch) {
        '\u{fffd}'
    } else {
        ch
    }
}

impl Cell {
    fn glyph(&self, charset: Charset) -> char {
        if self.symbol != 0 {
            return printable(char::from_u32(self.symbol).unwrap_or(' '));
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
        .unwrap_or(Token::Foreground);
        if token == Token::Background {
            Token::Foreground
        } else {
            token
        }
    }
    fn write_text(&self, out: &mut String, charset: Charset) {
        match &self.label {
            Label::Continuation => (),
            Label::Cluster { text, .. } => out.extend(text.chars().map(printable)),
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
        let mut current = Token::Foreground;
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
        if mode != ColorMode::None && current != Token::Foreground {
            out.push_str("\x1b[39m")
        }
        out.push('\n');
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_canvas_controls_are_replaced_in_every_colour_mode()
    -> Result<(), crate::geom::GeomError> {
        for ch in (0..=0x1f).chain(0x7f..=0x9f).filter_map(char::from_u32) {
            for (mode, prefix) in [
                (ColorMode::None, ""),
                (ColorMode::Ansi16, "\u{1b}[30m"),
                (ColorMode::Ansi256, "\u{1b}[38;5;16m"),
                (ColorMode::Truecolor, "\u{1b}[38;2;0;0;0m"),
            ] {
                let mut canvas = Canvas::new(2, 1)?;
                assert!(
                    canvas.put_label(0, 0, &ch.to_string(), 1, Token::Border),
                    "direct canvas controls are replaced in every colour mode: contract canvas.put_label(0, 0, &ch.to_string(), 1, Token::Border) failed; observed predicate=false"
                );
                canvas.put_symbol(1, 0, u32::from(ch));
                canvas.put(1, 0, |cell| cell.token = Some(Token::Border));
                let suffix = if mode == ColorMode::None {
                    ""
                } else {
                    "\u{1b}[39m"
                };
                let body = if ch == '\0' { "�" } else { "��" };
                let out = canvas.serialise(Charset::Unicode, mode, |_| Rgb { r: 0, g: 0, b: 0 });
                assert_eq!(out, format!("{prefix}{body}{suffix}\n"), "{ch:?} {mode:?}");
            }
        }
        Ok(())
    }

    #[test]
    fn direct_canvas_preserves_legitimate_unicode() -> Result<(), crate::geom::GeomError> {
        let mut canvas = Canvas::new(3, 1)?;
        assert!(
            canvas.put_label(0, 0, "世", 2, Token::Foreground),
            "direct canvas preserves legitimate unicode: contract canvas.put_label(0, 0, \"世\", 2, Token::Foreground) failed; observed predicate=false"
        );
        assert!(
            canvas.put_label(2, 0, "e\u{301}", 1, Token::Foreground),
            "direct canvas preserves legitimate unicode: contract canvas.put_label(2, 0, \"e\\u{{301}}\", 1, Token::Foreground) failed; observed predicate=false"
        );
        for charset in [Charset::Unicode, Charset::Ascii] {
            assert_eq!(
                canvas.serialise(charset, ColorMode::None, |_| Rgb { r: 0, g: 0, b: 0 }),
                "世e\u{301}\n"
            );
        }
        Ok(())
    }
}
