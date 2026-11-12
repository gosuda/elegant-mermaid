//! Tokens of the flowchart grammar, `spec/grammar/flowchart.md` flowchart-030.

use crate::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TokenKind {
    Graph,
    Nodir,
    Dir,
    DirectionTb,
    DirectionBt,
    DirectionRl,
    DirectionLr,
    DirectionTd,
    Subgraph,
    End,
    LinkTarget,
    LinkId,
    Link,
    StartLink,
    EdgeText,
    Text,
    Str,
    MdStr,
    ShapeData,
    Num,
    Brkt,
    StyleSeparator,
    Colon,
    Amp,
    Semi,
    Comma,
    Mult,
    Minus,
    Ps,
    Pe,
    Sqs,
    Sqe,
    DiamondStart,
    DiamondStop,
    TagStart,
    TagEnd,
    Up,
    Down,
    Pipe,
    EllipseStart,
    EllipseEnd,
    StadiumStart,
    StadiumEnd,
    SubroutineStart,
    SubroutineEnd,
    CylinderStart,
    CylinderEnd,
    DoubleCircleStart,
    DoubleCircleEnd,
    TrapStart,
    InvTrapStart,
    TrapEnd,
    InvTrapEnd,
    VertexWithPropsStart,
    Style,
    Default,
    LinkStyle,
    Interpolate,
    ClassDef,
    Class,
    Href,
    Click,
    CallbackName,
    CallbackArgs,
    AccTitle,
    AccTitleValue,
    AccDescr,
    AccDescrValue,
    AccDescrMultilineValue,
    NodeString,
    UnicodeText,
    Newline,
    Space,
    Eof,
}

impl TokenKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            TokenKind::Graph => "GRAPH",
            TokenKind::Nodir => "NODIR",
            TokenKind::Dir => "DIR",
            TokenKind::DirectionTb => "direction_tb",
            TokenKind::DirectionBt => "direction_bt",
            TokenKind::DirectionRl => "direction_rl",
            TokenKind::DirectionLr => "direction_lr",
            TokenKind::DirectionTd => "direction_td",
            TokenKind::Subgraph => "subgraph",
            TokenKind::End => "end",
            TokenKind::LinkTarget => "LINK_TARGET",
            TokenKind::LinkId => "LINK_ID",
            TokenKind::Link => "LINK",
            TokenKind::StartLink => "START_LINK",
            TokenKind::EdgeText => "EDGE_TEXT",
            TokenKind::Text => "TEXT",
            TokenKind::Str => "STR",
            TokenKind::MdStr => "MD_STR",
            TokenKind::ShapeData => "SHAPE_DATA",
            TokenKind::Num => "NUM",
            TokenKind::Brkt => "BRKT",
            TokenKind::StyleSeparator => "STYLE_SEPARATOR",
            TokenKind::Colon => "COLON",
            TokenKind::Amp => "AMP",
            TokenKind::Semi => "SEMI",
            TokenKind::Comma => "COMMA",
            TokenKind::Mult => "MULT",
            TokenKind::Minus => "MINUS",
            TokenKind::Ps => "PS",
            TokenKind::Pe => "PE",
            TokenKind::Sqs => "SQS",
            TokenKind::Sqe => "SQE",
            TokenKind::DiamondStart => "DIAMOND_START",
            TokenKind::DiamondStop => "DIAMOND_STOP",
            TokenKind::TagStart => "TAGSTART",
            TokenKind::TagEnd => "TAGEND",
            TokenKind::Up => "UP",
            TokenKind::Down => "DOWN",
            TokenKind::Pipe => "PIPE",
            TokenKind::EllipseStart => "ELLIPSE_START",
            TokenKind::EllipseEnd => "ELLIPSE_END",
            TokenKind::StadiumStart => "STADIUMSTART",
            TokenKind::StadiumEnd => "STADIUMEND",
            TokenKind::SubroutineStart => "SUBROUTINESTART",
            TokenKind::SubroutineEnd => "SUBROUTINEEND",
            TokenKind::CylinderStart => "CYLINDERSTART",
            TokenKind::CylinderEnd => "CYLINDEREND",
            TokenKind::DoubleCircleStart => "DOUBLECIRCLESTART",
            TokenKind::DoubleCircleEnd => "DOUBLECIRCLEEND",
            TokenKind::TrapStart => "TRAPSTART",
            TokenKind::InvTrapStart => "INVTRAPSTART",
            TokenKind::TrapEnd => "TRAPEND",
            TokenKind::InvTrapEnd => "INVTRAPEND",
            TokenKind::VertexWithPropsStart => "VERTEX_WITH_PROPS_START",
            TokenKind::Style => "STYLE",
            TokenKind::Default => "DEFAULT",
            TokenKind::LinkStyle => "LINKSTYLE",
            TokenKind::Interpolate => "INTERPOLATE",
            TokenKind::ClassDef => "CLASSDEF",
            TokenKind::Class => "CLASS",
            TokenKind::Href => "HREF",
            TokenKind::Click => "CLICK",
            TokenKind::CallbackName => "CALLBACKNAME",
            TokenKind::CallbackArgs => "CALLBACKARGS",
            TokenKind::AccTitle => "acc_title",
            TokenKind::AccTitleValue => "acc_title_value",
            TokenKind::AccDescr => "acc_descr",
            TokenKind::AccDescrValue => "acc_descr_value",
            TokenKind::AccDescrMultilineValue => "acc_descr_multiline_value",
            TokenKind::NodeString => "NODE_STRING",
            TokenKind::UnicodeText => "UNICODE_TEXT",
            TokenKind::Newline => "NEWLINE",
            TokenKind::Space => "SPACE",
            TokenKind::Eof => "EOF",
        }
    }
}

/// Lexer mode; one per row of the mode table, `flowchart-015`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Initial,
    Dir,
    AccTitle,
    AccDescr,
    AccDescrMultiline,
    Stringlit,
    MdString,
    Click,
    CallbackName,
    CallbackArgs,
    Text,
    EllipseText,
    TrapText,
    EdgeText,
    ThickEdgeText,
    DottedEdgeText,
    ShapeData,
    ShapeDataStr,
}

/// The text a token carries: a source slice, an owned rewritten string, or none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TextVal {
    None,
    Slice(Span),
    Owned(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BRPoint {
    pub text: usize,
    pub src: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub text: TextVal,
    pub string_open: Option<usize>,
    pub split_continuation: bool,
    pub brs: Vec<BRPoint>,
}

impl Token {
    pub(crate) const fn new(kind: TokenKind, span: Span, text: TextVal) -> Token {
        Token {
            kind,
            span,
            text,
            string_open: None,
            split_continuation: false,
            brs: Vec::new(),
        }
    }

    pub fn text<'b>(&'b self, src: &'b str) -> &'b str {
        match &self.text {
            TextVal::None => "",
            TextVal::Slice(span) => src.get(span.start..span.end).unwrap_or(""),
            TextVal::Owned(owned) => owned.as_str(),
        }
    }
}

pub(crate) fn is_alpha_num_token(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Num
            | TokenKind::UnicodeText
            | TokenKind::NodeString
            | TokenKind::Dir
            | TokenKind::Down
            | TokenKind::Minus
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Amp
            | TokenKind::Brkt
            | TokenKind::Mult
    )
}
