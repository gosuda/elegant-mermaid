use super::{
    clusters::{self, Cluster},
    graph::{Graph, Node, Params},
    normalize,
};

#[test]
fn proxy_rank_span() -> Result<(), super::LayoutError> {
    let graph = Graph {
        nodes: (0..6)
            .map(|_| Node {
                w: 2,
                ..Default::default()
            })
            .collect(),
        edges: vec![],
        params: Params::for_profile("cell")?,
    };
    let mut proper = normalize::normalize(&graph, &[0, 1, 0, 0, 1, 1])?;
    let cluster = Cluster {
        node: 0,
        bottom: 1,
        title: 0,
        left: vec![2, 4],
        right: vec![3, 5],
    };
    let mut x = vec![0, 0, 1, 9, 3, 19];
    clusters::ports(&[cluster], &mut proper, &mut x)?;
    assert_eq!((x[0], proper.nodes[0].node.w), (5, 10));
    assert_eq!((x[1], proper.nodes[1].node.w), (11, 18));
    Ok(())
}

#[test]
fn proxy_missing_rank_border() -> Result<(), super::LayoutError> {
    let graph = Graph {
        nodes: vec![Node::default(); 4],
        edges: vec![],
        params: Params::for_profile("cell")?,
    };
    let mut proper = normalize::normalize(&graph, &[0, 1, 0, 0])?;
    let cluster = Cluster {
        node: 0,
        bottom: 1,
        title: 0,
        left: vec![2],
        right: vec![3],
    };
    assert!(
        matches!(
            clusters::ports(&[cluster], &mut proper, &mut [0; 4]),
            Err(super::LayoutError::Domain)
        ),
        "proxy_missing_rank_border: input violates matches!( clusters::ports(&[cluster], &mut proper, &mut [0; 4]), Err(super::LayoutError::Domain) ); observed {:?}",
        proper
    );
    Ok(())
}
