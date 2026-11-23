//! Source provenance for semantic edge records, before layout adds decoration.

use super::{Resolved, gitgraph, sequence};
use crate::Span;

impl Resolved {
    pub(crate) fn edge_spans(&self) -> Vec<Span> {
        match self {
            Self::Flowchart(model) => model.edges.iter().map(|edge| edge.statement_span).collect(),
            Self::Swimlane(model) => model
                .flowchart
                .edges
                .iter()
                .map(|edge| edge.statement_span)
                .collect(),
            Self::Class(model) => model.relations.iter().map(|edge| edge.span).collect(),
            Self::State(model) => model.transitions.iter().map(|edge| edge.span).collect(),
            Self::C4(model) => model.relations.iter().map(|edge| edge.span).collect(),
            Self::Cynefin(model) => model.transitions.iter().map(|edge| edge.span).collect(),
            Self::Requirement(model) => model.relationships.iter().map(|edge| edge.span).collect(),
            Self::Er(model) => model.relationships.iter().map(|edge| edge.span).collect(),
            Self::Agentflow(model) => model.edges.iter().map(|edge| edge.statement_span).collect(),
            Self::Usecase(model) => model.relations.iter().map(|edge| edge.span).collect(),
            Self::Sequence(model) => model
                .events
                .iter()
                .filter_map(|event| match event {
                    sequence::Event::Message(message) => Some(message.span),
                    _ => None,
                })
                .collect(),
            Self::Mindmap(model) => model
                .nodes
                .iter()
                .filter(|node| node.parent.is_some())
                .map(|node| node.span)
                .collect(),
            Self::Eventmodeling(model) => model
                .relations
                .iter()
                .map(|edge| model.frames[edge.target].statement_span)
                .collect(),
            Self::Gitgraph(model) => gitgraph_edges(model),
            Self::Block(model) => model.edges.iter().map(|edge| edge.statement_span).collect(),
            Self::Wardley(model) => model.links.iter().map(|edge| edge.span).collect(),
            Self::Ishikawa(model) => model
                .nodes
                .iter()
                .filter(|node| node.parent.is_some())
                .map(|node| node.span)
                .collect(),
            Self::Architecture(model) => model.edges.iter().map(|edge| edge.span).collect(),
            Self::Treeview(model) => model
                .nodes
                .iter()
                .filter(|node| node.parent.is_some())
                .map(|node| node.span)
                .collect(),
            Self::Sankey(model) => model.links.iter().map(|edge| edge.span).collect(),
            Self::Xychart(_)
            | Self::Timeline(_)
            | Self::Railroad(_)
            | Self::Radar(_)
            | Self::Info(_)
            | Self::Packet(_)
            | Self::Kanban(_)
            | Self::Pie(_)
            | Self::Quadrant(_)
            | Self::Journey(_)
            | Self::Gantt(_)
            | Self::Venn(_)
            | Self::Treemap(_) => Vec::new(),
        }
    }
}

fn gitgraph_edges(model: &gitgraph::Model) -> Vec<Span> {
    let mut spans = Vec::new();
    let mut commits: Vec<_> = model.commits.iter().collect();
    commits.sort_by_key(|commit| commit.seq);
    for commit in commits {
        spans.extend(std::iter::repeat_n(commit.span, commit.parents.len()));
        if !commit.pick.is_empty() {
            spans.push(commit.span);
        }
    }
    spans
}
