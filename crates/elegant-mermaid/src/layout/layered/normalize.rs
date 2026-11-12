use super::{
    LayoutError,
    graph::{Graph, Node, Proper, ProperEdge, ProperNode},
};

pub fn normalize(g: &Graph, rank: &[i32]) -> Result<Proper, LayoutError> {
    g.validate()?;
    if rank.len() != g.nodes.len() || g.params.slot < 0 {
        return Err(LayoutError::Domain);
    }
    let slot = if g.params.slot == 0 {
        super::graph::Params::for_profile("vector")?.slot
    } else {
        g.params.slot
    };
    let nodes = g
        .nodes
        .iter()
        .map(|node| ProperNode {
            node: node.clone(),
            dummy: false,
            edge: -1,
        })
        .collect();
    let mut proper = Proper {
        nodes,
        edges: Vec::new(),
        rank: rank.to_vec(),
        chains: vec![Vec::new(); g.edges.len()],
        out: Vec::new(),
        r#in: Vec::new(),
        params: g.params,
    };
    for (index, e) in g.edges.iter().enumerate().filter(|(_, e)| !e.self_loop()) {
        let (tail, head) = e.chain();
        let span = i64::from(rank[head]) - i64::from(rank[tail]);
        if span < i64::from(e.min_len) {
            return Err(LayoutError::Domain);
        }
        let count = usize::try_from(span - 1).map_err(|_| LayoutError::Overflow)?;
        proper
            .nodes
            .len()
            .checked_add(count)
            .filter(|n| i32::try_from(*n).is_ok())
            .ok_or(LayoutError::Overflow)?;
        let mut chain = Vec::with_capacity(count + 2);
        chain.push(tail);
        for offset in 1..span {
            let node = proper.nodes.len();
            proper.nodes.push(ProperNode {
                node: Node {
                    id: String::new(),
                    decl: e.decl,
                    w: slot,
                    h: 0,
                },
                dummy: true,
                edge: i32::try_from(index).map_err(|_| LayoutError::Overflow)?,
            });
            proper.rank.push(
                i32::try_from(i64::from(rank[tail]) + offset).map_err(|_| LayoutError::Overflow)?,
            );
            chain.push(node);
        }
        chain.push(head);
        for pair in chain.windows(2) {
            proper.edges.push(ProperEdge {
                tail: pair[0],
                head: pair[1],
                decl: e.decl,
                original: index,
            });
        }
        proper.chains[index] = chain;
    }
    proper.out = vec![Vec::new(); proper.nodes.len()];
    proper.r#in = vec![Vec::new(); proper.nodes.len()];
    for (i, edge) in proper.edges.iter().enumerate() {
        proper.out[edge.tail].push(i);
        proper.r#in[edge.head].push(i);
    }
    Ok(proper)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::layered::graph::{Edge, Params};
    #[test]
    fn layered_normalize_unit_spans() -> Result<(), LayoutError> {
        let g = Graph {
            nodes: vec![Node::default(); 2],
            edges: vec![Edge {
                tail: 0,
                head: 1,
                min_len: 1,
                decl: 7,
                reversed: false,
            }],
            params: Params::for_profile("vector")?,
        };
        let p = normalize(&g, &[0, 4])?;
        assert_eq!(p.nodes.len() - g.nodes.len(), 3);
        assert!(p.edges.iter().all(|e| p.rank[e.head] - p.rank[e.tail] == 1));
        assert!(
            p.nodes[2..]
                .iter()
                .all(|n| n.node.decl == 7 && n.node.w == 768 && n.node.h == 0)
        );
        Ok(())
    }
}
