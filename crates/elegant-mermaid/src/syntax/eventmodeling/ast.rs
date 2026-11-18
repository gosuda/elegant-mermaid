//! Abstract syntax tree of the eventmodeling grammar (`spec/grammar/eventmodeling.md`).
//!
//! Node names retain the upstream production names in PascalCase. A statement span
//! runs from its keyword to the end of its last token.

use crate::source::Span;

use super::lexer::Token;

#[derive(Debug, Clone)]
pub struct Value {
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EventModel {
    pub span: Span,
    pub header: Token,
    pub model_entities: Vec<EmModelEntity>,
    pub frames: Vec<EmFrame>,
    pub data_entities: Vec<EmDataEntity>,
    pub note_entities: Vec<EmNoteEntity>,
    pub gwt_entities: Vec<EmGwt>,
}

#[derive(Debug, Clone)]
pub enum EmFrame {
    TimeFrame(FrameFields),
    ResetFrame(FrameFields),
}

impl EmFrame {
    pub fn fields(&self) -> &FrameFields {
        match self {
            Self::TimeFrame(fields) | Self::ResetFrame(fields) => fields,
        }
    }

    pub fn is_reset(&self) -> bool {
        matches!(self, Self::ResetFrame(_))
    }
}

#[derive(Debug, Clone)]
pub struct FrameFields {
    pub span: Span,
    pub keyword: Span,
    pub name: Value,
    pub model_entity_type: Value,
    pub entity_identifier: Value,
    pub source_frames: Vec<Value>,
    pub data_reference: Option<Value>,
    pub data_type: Option<Value>,
    pub data_inline_value: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct EmModelEntity {
    pub span: Span,
    pub keyword: Span,
    pub name: Value,
}

#[derive(Debug, Clone)]
pub struct EmDataEntity {
    pub span: Span,
    pub keyword: Span,
    pub name: Value,
    pub data_type: Option<Value>,
    pub data_block_value: Value,
}

#[derive(Debug, Clone)]
pub struct EmNoteEntity {
    pub span: Span,
    pub keyword: Span,
    pub source_frame: Value,
    pub data_type: Option<Value>,
    pub data_block_value: Value,
}

#[derive(Debug, Clone)]
pub struct EmGwt {
    pub span: Span,
    pub keyword: Span,
    pub source_frame: Value,
    pub given_statements: Vec<EmGwtStatement>,
    pub when_statements: Vec<EmGwtStatement>,
    pub then_statements: Vec<EmGwtStatement>,
}

#[derive(Debug, Clone)]
pub struct EmGwtStatement {
    pub span: Span,
    pub model_entity_type: Value,
    pub entity_identifier: Value,
}
