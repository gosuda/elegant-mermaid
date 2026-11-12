use super::LayoutError;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub decl: i32,
    pub w: i32,
    pub h: i32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge {
    pub tail: usize,
    pub head: usize,
    pub min_len: i32,
    pub decl: i32,
    pub reversed: bool,
}

impl Edge {
    pub fn self_loop(self) -> bool {
        self.tail == self.head
    }
    pub fn chain(self) -> (usize, usize) {
        if self.reversed {
            (self.head, self.tail)
        } else {
            (self.tail, self.head)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub slot: i32,
    pub pivot_factor: i32,
    pub node_gap: i32,
    pub rank_gap: i32,
    pub port_gap: i32,
    pub cluster_pad: i32,
}

impl Params {
    pub fn for_profile(profile: &str) -> Result<Self, LayoutError> {
        let lookup = |suffix: &str| {
            crate::r#gen::layoutconst::LAYOUT_CONST
                .iter()
                .find(|row| {
                    row.name
                        .strip_prefix(profile)
                        .and_then(|s| s.strip_prefix('.'))
                        == Some(suffix)
                })
                .map(|row| row.value)
                .ok_or(LayoutError::Domain)
        };
        Ok(Self {
            slot: lookup("slot")?,
            pivot_factor: lookup("pivot_factor")?,
            node_gap: lookup("node_gap")?,
            rank_gap: lookup("rank_gap")?,
            port_gap: lookup("port_gap")?,
            cluster_pad: lookup("cluster_pad")?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub params: Params,
}

impl Graph {
    pub fn validate(&self) -> Result<(), LayoutError> {
        if i32::try_from(self.nodes.len()).is_err() || i32::try_from(self.edges.len()).is_err() {
            return Err(LayoutError::Overflow);
        }
        if self.nodes.iter().any(|n| n.w < 0 || n.h < 0)
            || self.edges.windows(2).any(|e| e[0].decl > e[1].decl)
        {
            return Err(LayoutError::Domain);
        }
        if self
            .edges
            .iter()
            .any(|e| e.tail >= self.nodes.len() || e.head >= self.nodes.len() || e.min_len < 1)
        {
            return Err(LayoutError::Domain);
        }
        Ok(())
    }
    pub fn declared_out(&self) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new(); self.nodes.len()];
        for (i, e) in self.edges.iter().enumerate() {
            out[e.tail].push(i);
        }
        out
    }
    pub fn incident_edges(&self) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new(); self.nodes.len()];
        for (i, e) in self.edges.iter().enumerate() {
            out[e.tail].push(i);
            if !e.self_loop() {
                out[e.head].push(i);
            }
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProperNode {
    pub node: Node,
    pub dummy: bool,
    pub label: bool,
    pub edge: i32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProperEdge {
    pub tail: usize,
    pub head: usize,
    pub decl: i32,
    pub original: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proper {
    pub nodes: Vec<ProperNode>,
    pub edges: Vec<ProperEdge>,
    pub rank: Vec<i32>,
    pub chains: Vec<Vec<usize>>,
    pub out: Vec<Vec<usize>>,
    pub r#in: Vec<Vec<usize>>,
    pub params: Params,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn layered_profile_constants() {
        assert_eq!(
            Params::for_profile("vector"),
            Ok(Params {
                slot: 768,
                pivot_factor: 50,
                node_gap: 1536,
                rank_gap: 3072,
                port_gap: 512,
                cluster_pad: 1024,
            })
        );
    }
    #[test]
    fn layered_graph_rejects_invalid_endpoints() -> Result<(), LayoutError> {
        let g = Graph {
            nodes: vec![Node::default()],
            edges: vec![Edge {
                tail: 0,
                head: 1,
                min_len: 1,
                decl: 0,
                reversed: false,
            }],
            params: Params::for_profile("vector")?,
        };
        assert_eq!(g.validate(), Err(LayoutError::Domain));
        Ok(())
    }
}

#[cfg(test)]
#[path = "step14_compound_tests.rs"]
mod compound_tests;
