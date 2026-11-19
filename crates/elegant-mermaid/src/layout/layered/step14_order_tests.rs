use super::*;
use crate::layout::layered::{
    graph::{Edge, Graph, Node, Params},
    normalize,
};

#[test]
fn median_and_barycentre_use_different_rational_keys() -> Result<(), LayoutError> {
    let graph = Graph {
        nodes: (0..12)
            .map(|decl| Node {
                decl,
                ..Node::default()
            })
            .collect(),
        edges: [(0, 10), (1, 10), (9, 10), (2, 11), (3, 11), (4, 11)]
            .into_iter()
            .enumerate()
            .map(|(decl, (tail, head))| {
                Ok(Edge {
                    tail,
                    head,
                    decl: i32::try_from(decl).map_err(|_| LayoutError::Overflow)?,
                    min_len: 1,
                    reversed: false,
                })
            })
            .collect::<Result<Vec<_>, LayoutError>>()?,
        params: Params::for_profile("cell")?,
    };
    let mut ranks = vec![0; 12];
    ranks[10] = 1;
    ranks[11] = 1;
    let proper = normalize::normalize(&graph, &ranks)?;
    let (mut graph, layers) = OrderGraph::prepare(&proper)?;
    let mut barycentre = layers.clone();
    graph.sweep(&mut barycentre, 0)?;
    assert_eq!(barycentre[1], vec![11, 10]);
    graph.key = OrderKey::Median;
    let mut median = layers;
    graph.sweep(&mut median, 0)?;
    assert_eq!(median[1], vec![10, 11]);
    Ok(())
}

#[test]
fn reversed_start_tie_keeps_declaration_incumbent() -> Result<(), LayoutError> {
    let graph = Graph {
        nodes: vec![
            Node {
                decl: 0,
                ..Node::default()
            },
            Node {
                decl: 1,
                ..Node::default()
            },
        ],
        edges: Vec::new(),
        params: Params::for_profile("cell")?,
    };
    let proper = normalize::normalize(&graph, &[0, 0])?;
    assert_eq!(order(&proper, OrderOptions::default())?, vec![vec![0, 1]]);
    assert_eq!(
        order(
            &proper,
            OrderOptions {
                start: OrderStart::Reversed,
                key: OrderKey::Barycentre
            }
        )?,
        vec![vec![0, 1]]
    );
    Ok(())
}
