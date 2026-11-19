//! The `swimlane` model: the flowchart resolution with lane order.
//!
//! Each top-level subgraph is one lane; the lane order is the order of the first
//! subgraph openings, which is the order of [`flowchart::Model::groups`] with an
//! empty parent.

use crate::diag::Diagnostic;
use crate::syntax::flowchart::ast::Document;

/// The resolved swimlane model.
#[derive(Debug)]
pub struct Model {
    /// The flowchart resolution of the same source.
    pub flowchart: crate::model::flowchart::Model,
}

/// Resolves the swimlane document into its model.
pub fn resolve(source: &str, document: &Document) -> (Model, Vec<Diagnostic>) {
    let (flowchart, diagnostics) = crate::model::flowchart::resolve(source, document);
    (Model { flowchart }, diagnostics)
}

impl Model {
    /// The top-level lanes, in first-opening declaration order.
    pub fn lanes(&self) -> Vec<&str> {
        self.flowchart
            .groups
            .iter()
            .filter(|group| group.parent.is_empty())
            .map(|group| group.id.as_str())
            .collect()
    }
}
