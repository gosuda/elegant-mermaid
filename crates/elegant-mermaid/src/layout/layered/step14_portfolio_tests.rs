use super::*;
use crate::layout::layered::{
    cycles,
    graph::{Edge, Node, Params},
};

#[test]
fn greedy_feedback_ties_keep_lowest_declaration_first() -> Result<(), LayoutError> {
    let mut graph = Graph {
        nodes: (0..3)
            .map(|decl| Node {
                decl,
                ..Node::default()
            })
            .collect(),
        edges: vec![
            Edge {
                tail: 0,
                head: 1,
                min_len: 1,
                decl: 0,
                reversed: false,
            },
            Edge {
                tail: 1,
                head: 2,
                min_len: 1,
                decl: 1,
                reversed: false,
            },
            Edge {
                tail: 2,
                head: 0,
                min_len: 1,
                decl: 2,
                reversed: false,
            },
        ],
        params: Params::for_profile("cell")?,
    };
    greedy(&mut graph);
    assert_eq!(
        graph
            .edges
            .iter()
            .map(|edge| edge.reversed)
            .collect::<Vec<_>>(),
        vec![false, false, true]
    );
    Ok(())
}

#[test]
fn protected_constraints_never_reverse_during_semantic_insertion() -> Result<(), LayoutError> {
    let graph = Graph {
        nodes: (0..3)
            .map(|decl| Node {
                decl,
                ..Node::default()
            })
            .collect(),
        edges: vec![
            Edge {
                tail: 1,
                head: 0,
                min_len: 1,
                decl: 0,
                reversed: false,
            },
            Edge {
                tail: 1,
                head: 2,
                min_len: 1,
                decl: 1,
                reversed: false,
            },
            Edge {
                tail: 0,
                head: 1,
                min_len: 1,
                decl: i32::MAX,
                reversed: false,
            },
            Edge {
                tail: 0,
                head: 2,
                min_len: 1,
                decl: i32::MAX,
                reversed: false,
            },
        ],
        params: Params::for_profile("cell")?,
    };
    assert_eq!(
        cycles::break_cycles(&graph)?,
        vec![true, false, false, false]
    );
    Ok(())
}
