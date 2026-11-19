use super::{
    ast::*,
    lexer::Token,
    parser::{Parser, id_kind, text_kind},
};
use crate::source::Span;

impl<'a> Parser<'a, '_> {
    pub(super) fn id(&mut self) -> Option<IdString<'a>> {
        let start = self.position();
        let mut tokens = Vec::new();
        while id_kind(self.kind()) {
            tokens.push(self.take()?);
        }
        if tokens.is_empty() {
            self.unexpected("AMP, BRKT, COLON, COMMA, DEFAULT, DOWN, MINUS, MULT, NODE_STRING, NUM, UNICODE_TEXT");
            return None;
        }
        Some(IdString {
            span: self.span(start),
            tokens,
        })
    }
    pub(super) fn vertex_statement(&mut self) -> Option<VertexStatement<'a>> {
        let start = self.position();
        let mut nodes = vec![self.node()?];
        let mut links = Vec::new();
        self.spaces();
        while matches!(self.kind(), "LINK" | "LINK_ID" | "START_LINK") {
            links.push(self.link()?);
            self.spaces();
            nodes.push(self.node()?);
            self.spaces();
        }
        Some(VertexStatement {
            span: self.span(start),
            nodes,
            links,
        })
    }
    fn node(&mut self) -> Option<Node<'a>> {
        let start = self.position();
        let mut vertices = vec![self.styled_vertex()?];
        loop {
            let spaces = self.spaces();
            if spaces == 0 || self.kind() != "AMP" {
                break;
            }
            self.at += 1;
            if self.spaces() == 0 {
                self.unexpected("SPACE");
                return None;
            }
            vertices.push(self.styled_vertex()?);
        }
        Some(Node {
            span: self.span(start),
            vertices,
        })
    }
    fn styled_vertex(&mut self) -> Option<StyledVertex<'a>> {
        let vertex = self.vertex()?;
        let start = vertex.span.start;
        let class = if self.kind() == "STYLE_SEPARATOR" {
            self.at += 1;
            Some(self.id()?)
        } else {
            None
        };
        let metadata = self.metadata()?;
        Some(StyledVertex {
            span: self.span(start),
            vertex,
            class,
            metadata,
        })
    }
    fn vertex(&mut self) -> Option<Vertex<'a>> {
        let id = self.id()?;
        let start = id.span.start;
        let mut result = Vertex {
            span: id.span,
            id,
            label: None,
            shape: None,
            delimiters: None,
            property: None,
        };
        if self.kind() == "VERTEX_WITH_PROPS_START" {
            let open = self.take()?;
            let key = self.require("NODE_STRING")?;
            self.require("COLON")?;
            let value = self.require("NODE_STRING")?;
            self.require("PIPE")?;
            let label = self.label_text(&open)?;
            let close = self.close(&open, "SQE")?;
            result.label = Some(label);
            result.shape = Some("rect");
            result.property = Some((key, value));
            result.delimiters = Some((open.span, close.span));
        } else if opener(self.kind()).is_some() {
            let (label, shape, delimiters) = self.bracket_text()?;
            result.label = Some(label);
            result.shape = Some(shape);
            result.delimiters = Some(delimiters);
        }
        result.span = self.span(start);
        Some(result)
    }
    pub(super) fn bracket_text(&mut self) -> Option<(Text<'a>, &'static str, (Span, Span))> {
        let open = self.take()?;
        let (mut shape, mut close_kind) = opener(open.kind)?;
        let doubled = matches!(open.kind, "PS" | "DIAMOND_START") && self.kind() == open.kind;
        if doubled {
            self.at += 1;
            shape = if open.kind == "PS" {
                "circle"
            } else {
                "hexagon"
            };
        }
        let label = self.label_text(&open)?;
        if matches!(open.kind, "TRAPSTART" | "INVTRAPSTART") {
            (shape, close_kind) = trap_shape(open.kind, self.kind());
        }
        let mut close = self.close(&open, close_kind)?;
        if doubled {
            close = self.close(&open, close_kind)?;
        }
        Some((label, shape, (open.span, close.span)))
    }
    pub(super) fn label_text(&mut self, open: &Token<'a>) -> Option<Text<'a>> {
        if matches!(self.kind(), "EOF" | "UNTERMINATED") {
            self.close(open, "")?;
            return None;
        }
        self.text(&["TEXT", "TAGSTART", "TAGEND", "UNICODE_TEXT"])
    }
    pub(super) fn close(&mut self, open: &Token<'a>, kind: &'static str) -> Option<Token<'a>> {
        if self.kind() == "UNTERMINATED" {
            let token = self.take()?;
            let quoted = self
                .source
                .get(token.span.start..)
                .is_some_and(|s| s.starts_with('"'));
            let span = if quoted { token.span } else { open.span };
            self.unterminated(span);
            return None;
        }
        if self.kind() == "EOF" {
            self.unterminated(open.span);
            return None;
        }
        self.require(kind)
    }
    pub(super) fn text(&mut self, accepted: &[&str]) -> Option<Text<'a>> {
        let start = self.position();
        let mut pieces = Vec::new();
        if matches!(self.kind(), "STR" | "MD_STR") {
            let t = self.take()?;
            return Some(Text {
                span: t.span,
                kind: text_kind(t.kind),
                pieces: vec![t],
            });
        }
        while accepted.contains(&self.kind()) {
            pieces.push(self.take()?);
        }
        if pieces.is_empty() {
            let mut expected = accepted.to_vec();
            expected.extend(["MD_STR", "STR"]);
            expected.sort_unstable();
            self.unexpected(&expected.join(", "));
            return None;
        }
        Some(Text {
            span: self.span(start),
            pieces,
            kind: TextKind::Plain,
        })
    }
    pub(super) fn metadata(&mut self) -> Option<Vec<ShapeData<'a>>> {
        let mut data = Vec::new();
        loop {
            let before_spaces = self.at;
            self.spaces();
            if self.kind() != "SHAPE_DATA" {
                self.at = before_spaces;
                break;
            }
            let start = self.position();
            let mut pieces = vec![self.take()?];
            while self.kind() == "SHAPE_DATA"
                && self.tokens.get(self.at).is_some_and(|t| !t.text.is_empty())
            {
                pieces.push(self.take()?);
            }
            if self.kind() == "UNTERMINATED" {
                self.unexpected("");
                return None;
            }
            let span = self.span(start);
            let value = self.cleaned.slice(Span {
                start: start + 2,
                end: span.end.saturating_sub(1),
            });
            data.push(ShapeData {
                span,
                pieces,
                value,
            });
        }
        Some(data)
    }
}
fn opener(kind: &str) -> Option<(&'static str, &'static str)> {
    match kind {
        "SQS" => Some(("square", "SQE")),
        "DOUBLECIRCLESTART" => Some(("doublecircle", "DOUBLECIRCLEEND")),
        "PS" => Some(("round", "PE")),
        "(-" => Some(("ellipse", "-)")),
        "STADIUMSTART" => Some(("stadium", "STADIUMEND")),
        "SUBROUTINESTART" => Some(("subroutine", "SUBROUTINEEND")),
        "CYLINDERSTART" => Some(("cylinder", "CYLINDEREND")),
        "DIAMOND_START" => Some(("diamond", "DIAMOND_STOP")),
        "TAGEND" => Some(("odd", "SQE")),
        "TRAPSTART" => Some(("trapezoid", "TRAPEND")),
        "INVTRAPSTART" => Some(("inv_trapezoid", "INVTRAPEND")),
        _ => None,
    }
}
fn trap_shape(open: &str, close: &'static str) -> (&'static str, &'static str) {
    match (open, close) {
        ("TRAPSTART", "INVTRAPEND") => ("lean_right", close),
        ("INVTRAPSTART", "TRAPEND") => ("lean_left", close),
        ("INVTRAPSTART", _) => ("inv_trapezoid", "INVTRAPEND"),
        _ => ("trapezoid", "TRAPEND"),
    }
}
