//! The info model: the library version that the diagram shows (`spec/grammar/info.md`).

use crate::diag::Diagnostic;
use crate::syntax::info::ast::Info;

pub const VERSION: &str = "0.1.0";

#[derive(Debug, Clone)]
pub struct Model {
    pub version: String,
}

pub fn resolve(_document: &Info) -> (Model, Vec<Diagnostic>) {
    (
        Model {
            version: VERSION.to_owned(),
        },
        Vec::new(),
    )
}
