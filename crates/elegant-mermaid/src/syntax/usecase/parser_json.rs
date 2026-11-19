use super::{
    ast::{JsonObject, JsonStatement},
    diagnostic,
    lexer::Token,
    lexer_json::json_object,
    parser::Parser,
};
impl<'a> Parser<'a> {
    pub(super) fn json(&mut self) -> Option<JsonStatement<'a>> {
        let header = self.expect("JSON_DECLARATION_START")?;
        let id = self.json_identifier(&header)?;
        let token = self.expect("JSON_OBJECT_LITERAL")?;
        let object = self.checked_json(&token)?;
        let classes = self.optional_classes()?;
        Some(JsonStatement {
            span: self.span(header.span.start),
            header,
            id,
            object,
            classes,
        })
    }
    fn checked_json(&mut self, token: &Token<'a>) -> Option<JsonObject<'a>> {
        match json_object(token, &self.cleaned) {
            Ok(object) => Some(object),
            Err(error) => {
                let (code, message) = if error.limit {
                    ("limit/nesting-depth", "nesting depth exceeds 64".into())
                } else {
                    (
                        "usecase/invalid-json",
                        format!("invalid JSON object: {}", error.reason),
                    )
                };
                self.diagnostics.push(diagnostic(code, message, error.span));
                None
            }
        }
    }
    fn json_identifier(&self, header: &Token<'a>) -> Option<Token<'a>> {
        let tail = header.text.get(4..)?.trim_start_matches([' ', '\t']);
        let text = tail
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .next()?;
        let start = self.cleaned.index(header.span.start) + header.text.len() - tail.len();
        Some(Token {
            kind: "IDENTIFIER",
            text: self.cleaned.cow(start, start + text.len()),
            span: self.cleaned.span(start, start + text.len()),
        })
    }
}
