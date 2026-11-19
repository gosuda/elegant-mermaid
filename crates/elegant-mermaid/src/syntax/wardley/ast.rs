//! Abstract syntax tree of the wardley grammar (`spec/grammar/wardley.md`).
//!
//! Node names retain the upstream production names in PascalCase, and spans run from
//! the first to the last consumed token without a trailing statement separator.

use crate::source::Span;

use super::lexer::Token;

const NO_SPAN: Span = Span { start: 0, end: 0 };

#[derive(Debug, Clone)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

impl Value {
    pub(crate) fn empty() -> Value {
        Value {
            text: String::new(),
            span: NO_SPAN,
        }
    }

    pub(crate) fn of(token: Token) -> Value {
        Value {
            text: token.text,
            span: token.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Metadata {
    pub field: &'static str,
    pub value: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Wardley {
    pub span: Span,
    pub header: Option<Token>,
    pub metadata: Vec<Metadata>,
    pub size: Option<Size>,
    pub evolution: Option<Evolution>,
    pub anchors: Vec<Anchor>,
    pub components: Vec<Component>,
    pub links: Vec<Link>,
    pub evolves: Vec<Evolve>,
    pub pipelines: Vec<Pipeline>,
    pub notes: Vec<Note>,
    pub annotations: Vec<Annotations>,
    pub annotation: Vec<Annotation>,
    pub accelerators: Vec<Accelerator>,
    pub deaccelerators: Vec<Accelerator>,
}

#[derive(Debug, Clone)]
pub struct Size {
    pub span: Span,
    pub width: Value,
    pub height: Value,
}

#[derive(Debug, Clone)]
pub struct Evolution {
    pub span: Span,
    pub stages: Vec<EvolutionStage>,
}

#[derive(Debug, Clone)]
pub struct EvolutionStage {
    pub span: Span,
    pub name: Value,
    pub boundary: Option<Value>,
    pub second_name: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Anchor {
    pub span: Span,
    pub name: Value,
    pub visibility: Value,
    pub evolution: Value,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub span: Span,
    pub name: Value,
    pub visibility: Value,
    pub evolution: Value,
    pub label: Option<Label>,
    pub decorator: Option<Decorator>,
    pub inertia: bool,
}

#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub neg_x: bool,
    pub offset_x: Value,
    pub neg_y: bool,
    pub offset_y: Value,
}

#[derive(Debug, Clone)]
pub struct Decorator {
    pub span: Span,
    pub strategy: Value,
}

#[derive(Debug, Clone)]
pub struct Link {
    pub span: Span,
    pub from: Value,
    pub from_port: Option<Value>,
    pub arrow: Option<Value>,
    pub to: Value,
    pub to_port: Option<Value>,
    pub link_label: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct Evolve {
    pub span: Span,
    pub component: Value,
    pub target: Value,
}

#[derive(Debug, Clone)]
pub struct Pipeline {
    pub span: Span,
    pub parent: Value,
    pub components: Vec<PipelineComponent>,
}

#[derive(Debug, Clone)]
pub struct PipelineComponent {
    pub span: Span,
    pub name: Value,
    pub evolution: Value,
    pub label: Option<Label>,
}

#[derive(Debug, Clone)]
pub struct Note {
    pub span: Span,
    pub text: Value,
    pub visibility: Value,
    pub evolution: Value,
}

#[derive(Debug, Clone)]
pub struct Annotations {
    pub span: Span,
    pub x: Value,
    pub y: Value,
}

#[derive(Debug, Clone)]
pub struct Annotation {
    pub span: Span,
    pub number: Value,
    pub x: Value,
    pub y: Value,
    pub text: Value,
}

#[derive(Debug, Clone)]
pub struct Accelerator {
    pub span: Span,
    pub name: Value,
    pub x: Value,
    pub y: Value,
}
