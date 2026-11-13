//! Region metadata: the group forest over the input, its projection onto a
//! retained subgraph, and the rank-quotient and reservation entry points
//! that feed the reservation solver.

use super::LayoutError;
use super::reserve::{
    Constraints, IndexedGroups, Minima, RegionSet, Reservation, Span, add, index_groups, solve,
};
use crate::layout::layered::{clusters, graph, pipeline, rank};

pub struct Metadata {
    pub parents: Vec<Option<usize>>,
    pub sets: Vec<crate::layout::input::RegionSet>,
}

impl Metadata {
    pub fn validate(input: &crate::layout::input::Input) -> Result<Self, LayoutError> {
        let parents = parent_indices(input)?;
        let sets: Vec<_> = input
            .region_sets
            .iter()
            .map(|set| RegionSet {
                parent: set.parent,
                regions: &set.regions,
            })
            .collect();
        let IndexedGroups {
            children, order, ..
        } = index_groups(&parents, &sets)?;
        let mut depths = vec![0usize; parents.len()];
        for parent in order {
            for &child in &children[parent] {
                depths[child] = depths[parent] + 1;
                if depths[child] >= 64 {
                    return Err(LayoutError::Domain);
                }
            }
        }
        Ok(Self {
            parents,
            sets: input.region_sets.clone(),
        })
    }

    /// A retained set parent requires all its regions. Sets outside the projected
    /// scope are omitted, including enclosing sets of an isolated subtree.
    pub fn project(
        &self,
        retained: &[bool],
    ) -> Result<Vec<crate::layout::input::RegionSet>, LayoutError> {
        if retained.len() != self.parents.len() {
            return Err(LayoutError::Domain);
        }
        let mut remap = vec![None; retained.len()];
        let mut next = 0;
        for (old, &keep) in retained.iter().enumerate() {
            if keep {
                remap[old] = Some(next);
                next += 1;
            }
        }
        let mut output = Vec::new();
        for set in &self.sets {
            let present = set.regions.iter().filter(|&&g| retained[g]).count();
            let Some(parent) = remap[set.parent] else {
                continue;
            };
            if present != set.regions.len() {
                return Err(LayoutError::Domain);
            }
            let regions = set
                .regions
                .iter()
                .map(|&g| remap[g].ok_or(LayoutError::Domain))
                .collect::<Result<Vec<_>, _>>()?;
            output.push(crate::layout::input::RegionSet { parent, regions });
        }
        Ok(output)
    }
}

pub struct ComponentSets {
    pub groups: Vec<usize>,
    pub sets: Vec<crate::layout::input::RegionSet>,
    pub parents: Vec<Option<usize>>,
}

impl ComponentSets {
    pub fn new(
        input: &crate::layout::input::Input,
        graph: &graph::Graph,
    ) -> Result<Self, LayoutError> {
        let metadata = Metadata::validate(input)?;
        let nodes: std::collections::BTreeMap<_, _> = graph
            .nodes
            .iter()
            .enumerate()
            .map(|(i, node)| (node.id.as_str(), i))
            .collect();
        let retained: Vec<_> = input
            .groups
            .iter()
            .map(|g| nodes.contains_key(g.id.as_str()))
            .collect();
        let sets = metadata.project(&retained)?;
        let groups: Vec<_> = retained
            .iter()
            .enumerate()
            .filter_map(|(g, keep)| keep.then_some(g))
            .collect();
        let mut remap = vec![None; retained.len()];
        for (local, &global) in groups.iter().enumerate() {
            remap[global] = Some(local);
        }
        let parents = groups
            .iter()
            .map(|&g| metadata.parents[g].and_then(|p| remap[p]))
            .collect();
        Ok(Self {
            groups,
            sets,
            parents,
        })
    }

    pub fn rank(
        &self,
        input: &crate::layout::input::Input,
        graph: &mut graph::Graph,
        clusters: &[clusters::Cluster],
    ) -> Result<rank::Ranking, LayoutError> {
        if self.sets.is_empty() {
            return rank::rank(graph);
        }
        let nodes: std::collections::BTreeMap<_, _> = graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| !n.id.is_empty())
            .map(|(i, n)| (n.id.as_str(), i))
            .collect();
        let cluster_nodes: std::collections::BTreeMap<_, _> =
            clusters.iter().map(|c| (c.node, c.bottom)).collect();
        let mut representatives: Vec<_> = (0..graph.nodes.len()).collect();
        for set in &self.sets {
            let first = self.groups[set.regions[0]];
            let top = *nodes
                .get(input.groups[first].id.as_str())
                .ok_or(LayoutError::Domain)?;
            let bottom = *cluster_nodes.get(&top).ok_or(LayoutError::Domain)?;
            for &region in &set.regions {
                let global = self.groups[region];
                let node = *nodes
                    .get(input.groups[global].id.as_str())
                    .ok_or(LayoutError::Domain)?;
                let end = *cluster_nodes.get(&node).ok_or(LayoutError::Domain)?;
                representatives[node] = top;
                representatives[end] = bottom;
            }
        }
        rank_equivalent(graph, &representatives)
    }
}

fn rank_equivalent(
    graph: &mut graph::Graph,
    representatives: &[usize],
) -> Result<rank::Ranking, LayoutError> {
    let mut remap = vec![usize::MAX; graph.nodes.len()];
    let mut nodes = Vec::new();
    for (index, &root) in representatives.iter().enumerate() {
        if root == index {
            remap[index] = nodes.len();
            nodes.push(graph.nodes[index].clone());
        }
    }
    for (index, &root) in representatives.iter().enumerate() {
        if representatives[root] != root {
            return Err(LayoutError::Domain);
        }
        remap[index] = remap[root];
    }
    let mut originals = Vec::with_capacity(graph.edges.len());
    let mut edges = Vec::with_capacity(graph.edges.len());
    for (index, edge) in graph.edges.iter().enumerate() {
        if edge.tail == edge.head {
            continue;
        }
        let mut edge = *edge;
        edge.tail = remap[edge.tail];
        edge.head = remap[edge.head];
        if edge.tail == edge.head {
            return Err(LayoutError::Domain);
        }
        originals.push(index);
        edges.push(edge);
    }
    let mut condensed = graph::Graph {
        nodes,
        edges,
        params: graph.params,
    };
    orient_rank_edges(&mut condensed, graph, &originals)?;
    let ranking = rank::rank(&condensed)?;
    Ok(rank::Ranking {
        ranks: remap.into_iter().map(|node| ranking.ranks[node]).collect(),
        budget_exhausted: ranking.budget_exhausted,
    })
}

/// Containment is fixed in the rank quotient. Semantic edges may reverse, but
/// retain their original endpoints and carry that orientation into normalization.
fn orient_rank_edges(
    condensed: &mut graph::Graph,
    graph: &mut graph::Graph,
    originals: &[usize],
) -> Result<(), LayoutError> {
    let mut successors = vec![Vec::new(); condensed.nodes.len()];
    let mut visited = vec![false; condensed.nodes.len()];
    let mut stack = Vec::with_capacity(condensed.nodes.len());
    for edge in &mut condensed.edges {
        if edge.decl == i32::MAX {
            edge.reversed = false;
            if rank_reachable(&successors, edge.head, edge.tail, &mut visited, &mut stack) {
                return Err(LayoutError::Domain);
            }
            successors[edge.tail].push(edge.head);
        }
    }
    for (edge, &original) in condensed.edges.iter_mut().zip(originals) {
        if edge.decl == i32::MAX {
            graph.edges[original].reversed = false;
            continue;
        }
        let (tail, head) = if edge.reversed {
            (edge.head, edge.tail)
        } else {
            (edge.tail, edge.head)
        };
        if rank_reachable(&successors, head, tail, &mut visited, &mut stack) {
            edge.reversed = !edge.reversed;
            successors[head].push(tail);
        } else {
            successors[tail].push(head);
        }
        graph.edges[original].reversed = edge.reversed;
    }
    Ok(())
}

fn rank_reachable(
    successors: &[Vec<usize>],
    start: usize,
    target: usize,
    visited: &mut [bool],
    stack: &mut Vec<usize>,
) -> bool {
    visited.fill(false);
    stack.clear();
    visited[start] = true;
    stack.push(start);
    while let Some(node) = stack.pop() {
        if node == target {
            return true;
        }
        for &next in &successors[node] {
            if !visited[next] {
                visited[next] = true;
                stack.push(next);
            }
        }
    }
    false
}

pub struct Footprints<'a> {
    pub input: &'a crate::layout::input::Input,
    pub graph: &'a graph::Graph,
    pub proper: &'a graph::Proper,
    pub clusters: &'a [clusters::Cluster],
    pub paths: &'a [Vec<usize>],
}

impl ComponentSets {
    pub fn constraints(&self, footprints: Footprints<'_>) -> Result<Constraints, LayoutError> {
        let Footprints {
            input,
            graph,
            proper,
            clusters,
            paths,
        } = footprints;
        let group_ids: std::collections::BTreeMap<_, _> = self
            .groups
            .iter()
            .enumerate()
            .map(|(local, &global)| (input.groups[global].id.as_str(), local))
            .collect();
        let mut local_nodes = vec![None; graph.nodes.len()];
        for (node, value) in graph.nodes.iter().enumerate() {
            local_nodes[node] = group_ids.get(value.id.as_str()).copied();
        }
        let mut reservations = Vec::new();
        for cluster in clusters {
            let group = local_nodes[cluster.node].ok_or(LayoutError::Domain)?;
            reservations.push(Reservation {
                group,
                left: 0,
                right: proper.nodes[cluster.title].node.w,
                span: Span {
                    first: proper.rank[cluster.node],
                    last: proper.rank[cluster.bottom],
                },
            });
        }
        let mut rows = std::collections::BTreeMap::<(usize, i32), i32>::new();
        for (node, path) in paths.iter().enumerate() {
            let Some(&owner) = path.last() else { continue };
            let group = local_nodes
                .get(owner)
                .copied()
                .flatten()
                .ok_or(LayoutError::Domain)?;
            let width = proper.nodes[node].node.w;
            let key = (group, proper.rank[node]);
            let row = rows.entry(key).or_insert(0);
            *row = add(add(*row, width)?, graph.params.node_gap)?;
        }
        for ((group, rank), width) in rows {
            reservations.push(Reservation {
                group,
                left: 0,
                right: width,
                span: Span {
                    first: rank,
                    last: rank,
                },
            });
        }
        let sets: Vec<_> = self
            .sets
            .iter()
            .map(|set| RegionSet {
                parent: set.parent,
                regions: &set.regions,
            })
            .collect();
        solve(
            &self.parents,
            &sets,
            &reservations,
            Minima {
                border: pipeline::constant(input.profile, "cluster_border_w"),
                padding: graph.params.cluster_pad,
                title: pipeline::constant(input.profile, "line_h"),
            },
        )
    }
}

fn parent_indices(input: &crate::layout::input::Input) -> Result<Vec<Option<usize>>, LayoutError> {
    use std::collections::BTreeMap;
    let mut groups = BTreeMap::new();
    let mut boxes = BTreeMap::new();
    for (index, group) in input.groups.iter().enumerate() {
        if group.id.is_empty() || groups.insert(group.id.as_str(), index).is_some() {
            return Err(LayoutError::Domain);
        }
    }
    for item in &input.boxes {
        if item.id.is_empty() || boxes.insert(item.id.as_str(), item).is_some() {
            return Err(LayoutError::Domain);
        }
        if !item.parent.is_empty() && !groups.contains_key(item.parent.as_str()) {
            return Err(LayoutError::Domain);
        }
    }
    let mut parents = Vec::with_capacity(input.groups.len());
    for group in &input.groups {
        let item = boxes.get(group.id.as_str()).ok_or(LayoutError::Domain)?;
        if item.parent != group.parent || item.role != crate::scene::BoxRole::Group {
            return Err(LayoutError::Domain);
        }
        parents.push(if group.parent.is_empty() {
            None
        } else {
            Some(
                *groups
                    .get(group.parent.as_str())
                    .ok_or(LayoutError::Domain)?,
            )
        });
    }
    Ok(parents)
}
