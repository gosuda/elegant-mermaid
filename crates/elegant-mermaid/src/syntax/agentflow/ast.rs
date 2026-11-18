use std::borrow::Cow;

use super::lexer::Token;
use crate::source::Span;

#[derive(Debug, Clone)]
pub struct Start<'a> {
    pub span: Span,
    pub header: Token<'a>,
    pub config: GraphConfig<'a>,
    pub document: Document<'a>,
}
#[derive(Debug, Clone)]
pub struct GraphConfig<'a> {
    pub span: Span,
    pub direction: Direction,
    pub authored: Option<Token<'a>>,
    pub separator: Option<FirstStmtSeparator<'a>>,
}
#[derive(Debug, Clone)]
pub struct Document<'a> {
    pub span: Span,
    pub lines: Vec<Line<'a>>,
}
#[derive(Debug, Clone)]
pub struct Line<'a> {
    pub span: Span,
    pub statement: Option<Statement<'a>>,
}
#[derive(Debug, Clone)]
pub struct Statement<'a> {
    pub span: Span,
    pub kind: StatementKind<'a>,
}
#[derive(Debug, Clone)]
pub enum StatementKind<'a> {
    Vertex(VertexStatement<'a>),
    ClassDef(ClassDefStatement<'a>),
    Class(ClassStatement<'a>),
    Style(StyleStatement<'a>),
    LinkStyle(LinkStyleStatement<'a>),
    Click(ClickStatement<'a>),
    Flow {
        name: Option<TextNoTags<'a>>,
        title: Option<Text<'a>>,
        metadata: Vec<ShapeData<'a>>,
        opening: Span,
        body: Document<'a>,
        close: Span,
    },
    Global {
        opening: Span,
        body: Document<'a>,
        close: Span,
    },
    Connector {
        name: TextNoTags<'a>,
        title: Option<Text<'a>>,
        metadata: Vec<ShapeData<'a>>,
    },
    Direction(Direction),
    Accessibility {
        title: bool,
        value: Token<'a>,
    },
}
#[derive(Debug, Clone)]
pub struct VertexStatement<'a> {
    pub span: Span,
    pub nodes: Vec<Node<'a>>,
    pub links: Vec<Link<'a>>,
}
#[derive(Debug, Clone)]
pub struct Node<'a> {
    pub span: Span,
    pub vertices: Vec<StyledVertex<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyledVertex<'a> {
    pub span: Span,
    pub vertex: Vertex<'a>,
    pub class: Option<IdString<'a>>,
    pub metadata: Vec<ShapeData<'a>>,
}
#[derive(Debug, Clone)]
pub struct Vertex<'a> {
    pub span: Span,
    pub id: IdString<'a>,
    pub label: Option<Text<'a>>,
    pub shape: Option<&'static str>,
    pub delimiters: Option<(Span, Span)>,
    pub property: Option<(Token<'a>, Token<'a>)>,
}
#[derive(Debug, Clone)]
pub struct ShapeData<'a> {
    pub span: Span,
    pub pieces: Vec<Token<'a>>,
    pub value: Cow<'a, str>,
}
impl<'a> ShapeData<'a> {
    pub fn normalized_value(&self) -> Cow<'_, str> {
        if !has_quoted_linebreak(&self.value) {
            return Cow::Borrowed(&self.value);
        }
        let mut output = String::with_capacity(self.value.len());
        let mut quoted = false;
        let mut characters = self.value.chars().peekable();
        while let Some(c) = characters.next() {
            if c == '"' {
                quoted = !quoted;
            }
            if !quoted || !matches!(c, '\r' | '\n') {
                output.push(c);
                continue;
            }
            output.push_str("<br/>");
            while characters.peek().is_some_and(|c| c.is_whitespace()) {
                characters.next();
            }
        }
        Cow::Owned(output)
    }
}
fn has_quoted_linebreak(value: &str) -> bool {
    let mut quoted = false;
    for c in value.chars() {
        if c == '"' {
            quoted = !quoted;
        }
        if quoted && matches!(c, '\r' | '\n') {
            return true;
        }
    }
    false
}
#[derive(Debug, Clone)]
pub struct Link<'a> {
    pub span: Span,
    pub statement: LinkStatement<'a>,
    pub opening: Option<Token<'a>>,
    pub arrow_text: Option<ArrowText<'a>>,
    pub edge_text: Option<EdgeText<'a>>,
}
#[derive(Debug, Clone)]
pub struct LinkStatement<'a> {
    pub span: Span,
    pub id: Option<Token<'a>>,
    pub operator: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ArrowText<'a> {
    pub span: Span,
    pub text: Text<'a>,
}
#[derive(Debug, Clone)]
pub struct EdgeText<'a> {
    pub span: Span,
    pub text: Text<'a>,
}
impl<'a> Link<'a> {
    pub fn label(&self) -> Option<&Text<'a>> {
        self.arrow_text
            .as_ref()
            .map(|a| &a.text)
            .or_else(|| self.edge_text.as_ref().map(|e| &e.text))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextKind {
    Plain,
    String,
    Markdown,
}
#[derive(Debug, Clone)]
pub struct Text<'a> {
    pub span: Span,
    pub pieces: Vec<Token<'a>>,
    pub kind: TextKind,
}
#[derive(Debug, Clone)]
pub struct TextNoTags<'a> {
    pub span: Span,
    pub pieces: Vec<Token<'a>>,
    pub kind: TextKind,
}
#[derive(Debug, Clone)]
pub struct IdString<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct AlphaNum<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct ClassDefStatement<'a> {
    pub span: Span,
    pub id: IdString<'a>,
    pub styles: StylesOpt<'a>,
}
#[derive(Debug, Clone)]
pub struct ClassStatement<'a> {
    pub span: Span,
    pub targets: IdString<'a>,
    pub class: IdString<'a>,
}
#[derive(Debug, Clone)]
pub struct StyleStatement<'a> {
    pub span: Span,
    pub targets: IdString<'a>,
    pub styles: StylesOpt<'a>,
}
#[derive(Debug, Clone)]
pub struct LinkStyleStatement<'a> {
    pub span: Span,
    pub default: Option<Token<'a>>,
    pub indices: Option<NumList<'a>>,
    pub interpolation: Option<AlphaNum<'a>>,
    pub styles: Option<StylesOpt<'a>>,
}
#[derive(Debug, Clone)]
pub struct NumList<'a> {
    pub span: Span,
    pub indices: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct StylesOpt<'a> {
    pub span: Span,
    pub styles: Vec<Style<'a>>,
}
#[derive(Debug, Clone)]
pub struct Style<'a> {
    pub span: Span,
    pub components: Vec<StyleComponent<'a>>,
}
#[derive(Debug, Clone)]
pub struct StyleComponent<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct ClickStatement<'a> {
    pub span: Span,
    pub id: Token<'a>,
    pub callback: Option<AlphaNum<'a>>,
    pub arguments: Option<Token<'a>>,
    pub url: Option<Token<'a>>,
    pub tooltip: Option<Token<'a>>,
    pub target: Option<Token<'a>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Direction {
    pub span: Span,
    pub value: &'static str,
}
#[derive(Debug, Clone)]
pub struct Keywords<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct IdStringToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct TextToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct TextNoTagsToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct EdgeTextToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct AlphaNumToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct FirstStmtSeparator<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct Separator<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
#[derive(Debug, Clone)]
pub struct SpaceList<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct SpaceListNewline<'a> {
    pub span: Span,
    pub tokens: Vec<Token<'a>>,
}
#[derive(Debug, Clone)]
pub struct Ending<'a> {
    pub span: Span,
    pub tokens: Vec<EndToken<'a>>,
}
#[derive(Debug, Clone)]
pub struct EndToken<'a> {
    pub span: Span,
    pub token: Token<'a>,
}
