//! Cross-axis placement over solved region constraints: the containment
//! tree, per-group member buckets, the return-lane strip, and final frames.
//!
//! The internal return-lane strip is anchored at the frame's trailing edge
//! less the loop footprint and one inset; minimum-width slack stays before
//! the strip, never between the strip and the frame.

use super::LayoutError;
use super::metadata::ComponentSets;
use super::reserve::{Constraints, add};
use crate::layout::layered::{cluster_order, clusters, graph, pipeline};

pub struct CoordinateInput<'a> {
    pub input: &'a crate::layout::input::Input,
    pub sets: &'a ComponentSets,
    pub minimum: &'a Constraints,
    pub graph: &'a graph::Graph,
    pub proper: &'a graph::Proper,
    pub footprints: &'a graph::Graph,
    pub clusters: &'a [clusters::Cluster],
    pub paths: &'a [Vec<usize>],
    pub loop_extents: &'a [i32],
    pub label_sizes: &'a [(i32, i32)],
}

/// Algorithmic bands and physical group frames are distinct intervals.
pub struct Placement {
    pub x: Vec<i32>,
    pub lane_x: Vec<Option<i32>>,
    pub frames: Vec<(usize, i32, i32)>,
    pub bands: Vec<(usize, i32, i32)>,
    pub group_footprints: Vec<(usize, crate::geom::Size)>,
}

pub struct CrossTree {
    children: Vec<Vec<usize>>,
    order: Vec<usize>,
    node_groups: Vec<Option<usize>>,
    graph_groups: Vec<Option<usize>>,
}

impl CrossTree {
    pub fn new(context: &CoordinateInput<'_>) -> Result<Self, LayoutError> {
        let n = context.sets.groups.len();
        let ids: std::collections::BTreeMap<_, _> = context
            .sets
            .groups
            .iter()
            .enumerate()
            .map(|(local, &global)| (context.input.groups[global].id.as_str(), local))
            .collect();
        let graph_groups: Vec<_> = context
            .graph
            .nodes
            .iter()
            .map(|node| ids.get(node.id.as_str()).copied())
            .collect();
        let mut children = vec![Vec::new(); n + 1];
        for (group, parent) in context.sets.parents.iter().enumerate() {
            children[parent.unwrap_or(n)].push(group);
        }
        let mut region_owner = vec![None; n];
        for (index, set) in context.sets.sets.iter().enumerate() {
            for &region in &set.regions {
                region_owner[region] = Some(index);
            }
            let sequence = &mut children[set.parent];
            let first = sequence
                .iter()
                .position(|&g| region_owner[g] == Some(index))
                .ok_or(LayoutError::Domain)?;
            sequence.retain(|&g| region_owner[g] != Some(index));
            sequence.splice(first..first, set.regions.iter().copied());
        }
        let mut order = Vec::with_capacity(n + 1);
        let mut stack = vec![n];
        while let Some(group) = stack.pop() {
            order.push(group);
            stack.extend(children[group].iter().rev().copied());
        }
        let node_groups = context
            .paths
            .iter()
            .map(|path| {
                path.last()
                    .map(|&node| {
                        graph_groups
                            .get(node)
                            .copied()
                            .flatten()
                            .ok_or(LayoutError::Domain)
                    })
                    .transpose()
            })
            .collect::<Result<Vec<_>, _>>()?;
        if node_groups.len() != context.proper.nodes.len() || order.len() != n + 1 {
            return Err(LayoutError::Domain);
        }
        Ok(Self {
            children,
            order,
            node_groups,
            graph_groups,
        })
    }

    fn edge_owner(
        &self,
        context: &CoordinateInput<'_>,
        edge: &graph::Edge,
    ) -> Result<usize, LayoutError> {
        let a = context.paths.get(edge.tail).ok_or(LayoutError::Domain)?;
        let b = context.paths.get(edge.head).ok_or(LayoutError::Domain)?;
        let owner = a.iter().zip(b).take_while(|(a, b)| a == b).last();
        match owner {
            Some((&node, _)) => self.graph_groups[node].ok_or(LayoutError::Domain),
            None => Ok(self.children.len() - 1),
        }
    }
}

struct Buckets {
    members: Vec<Vec<usize>>,
    low: Vec<i32>,
    widths: Vec<i32>,
    lanes: Vec<Vec<usize>>,
    lane_width: Vec<i32>,
    loop_width: Vec<i32>,
}

impl Buckets {
    fn new(
        context: &CoordinateInput<'_>,
        tree: &CrossTree,
        desired: &[i32],
    ) -> Result<Self, LayoutError> {
        let n = tree.children.len();
        let mut members = vec![Vec::new(); n];
        let mut low = vec![i32::MAX; n];
        let mut high = vec![i32::MIN; n];
        for (node, value) in context.proper.nodes.iter().enumerate() {
            if matches!(value.edge, -5..=-2) {
                continue;
            }
            let owner = tree.node_groups[node].unwrap_or(n - 1);
            let left = desired[node]
                .checked_sub(value.node.w / 2)
                .ok_or(LayoutError::Overflow)?;
            let right = add(left, value.node.w)?;
            low[owner] = low[owner].min(left);
            high[owner] = high[owner].max(right);
            members[owner].push(node);
        }
        let widths = low
            .iter()
            .zip(&high)
            .map(|(&lo, &hi)| {
                if lo == i32::MAX {
                    Ok(0)
                } else {
                    hi.checked_sub(lo).ok_or(LayoutError::Overflow)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut lanes = vec![Vec::new(); n];
        let mut lane_width = vec![0; n];
        for (index, edge) in context.graph.edges.iter().enumerate() {
            if !edge.reversed || edge.self_loop() {
                continue;
            }
            let owner = tree.edge_owner(context, edge)?;
            if owner == n - 1 {
                continue;
            }
            lanes[owner].push(index);
            lane_width[owner] =
                lane_width[owner].max(context.label_sizes.get(index).map_or(0, |s| s.0));
        }
        let mut loop_width = vec![0; n];
        for cluster in context.clusters {
            let group = tree.graph_groups[cluster.node].ok_or(LayoutError::Domain)?;
            loop_width[group] = context.loop_extents.get(cluster.node).copied().unwrap_or(0);
        }
        Ok(Self {
            members,
            low,
            widths,
            lanes,
            lane_width,
            loop_width,
        })
    }

    fn lane_extent(&self, group: usize, slot: i32) -> Result<i32, LayoutError> {
        let stride = add(add(slot, slot)?, self.lane_width[group])?;
        stride
            .checked_mul(i32::try_from(self.lanes[group].len()).map_err(|_| LayoutError::Overflow)?)
            .ok_or(LayoutError::Overflow)
    }
}

impl Placement {
    pub fn solve(
        context: CoordinateInput<'_>,
        desired: Vec<i32>,
        tree: CrossTree,
    ) -> Result<Self, LayoutError> {
        if desired.len() != context.proper.nodes.len() {
            return Err(LayoutError::Domain);
        }
        tree.common_spans(&context)?;
        let buckets = Buckets::new(&context, &tree, &desired)?;
        let root = tree.children.len() - 1;
        let Allocation {
            widths,
            lefts,
            mut x,
            lane_x,
        } = buckets.allocate(&context, &tree, desired)?;
        let mut frames = Vec::with_capacity(root);
        let mut bands = Vec::with_capacity(root);
        let mut group_footprints = Vec::with_capacity(root);
        for cluster in context.clusters {
            let group = tree.graph_groups[cluster.node].ok_or(LayoutError::Domain)?;
            let right = add(lefts[group], widths[group])?;
            let frame_right = right
                .checked_sub(buckets.loop_width[group])
                .ok_or(LayoutError::Overflow)?;
            frames.push((cluster.node, lefts[group], frame_right));
            bands.push((cluster.node, lefts[group], right));
            group_footprints.push((
                cluster.node,
                crate::geom::Size {
                    w: context.footprints.nodes[cluster.node].w,
                    h: context.footprints.nodes[cluster.node].h,
                },
            ));
            for &node in &cluster.left {
                x[node] = add(
                    lefts[group],
                    pipeline::constant(context.input.profile, "cluster_border_w") / 2,
                )?;
            }
            for &node in &cluster.right {
                let width = pipeline::constant(context.input.profile, "cluster_border_w");
                x[node] = add(
                    frame_right
                        .checked_sub(width)
                        .ok_or(LayoutError::Overflow)?,
                    width / 2,
                )?;
            }
            x[cluster.title] = add(lefts[group], (frame_right - lefts[group]) / 2)?;
            x[cluster.node] = x[cluster.title];
            x[cluster.bottom] = x[cluster.title];
        }
        Ok(Self {
            x,
            lane_x,
            frames,
            bands,
            group_footprints,
        })
    }
}

impl CrossTree {
    pub fn pin(
        &self,
        context: &CoordinateInput<'_>,
        layers: &mut [Vec<usize>],
    ) -> Result<(), LayoutError> {
        let root = self.children.len() - 1;
        let mut prefixes = vec![Vec::new(); root + 1];
        for &group in &self.order {
            for (position, &child) in self.children[group].iter().enumerate() {
                let mut prefix = prefixes[group].clone();
                prefix.push(position.checked_add(2).ok_or(LayoutError::Overflow)?);
                prefixes[child] = prefix;
            }
        }
        let keys: Vec<_> = context
            .proper
            .nodes
            .iter()
            .enumerate()
            .map(|(node, value)| {
                let mut key = prefixes[self.node_groups[node].unwrap_or(root)].clone();
                key.push(match value.edge {
                    -2 => 0,
                    -3 => usize::MAX,
                    _ => 1,
                });
                key
            })
            .collect();
        cluster_order::pin(layers, &keys)
    }
}

struct Allocation {
    widths: Vec<i32>,
    lefts: Vec<i32>,
    x: Vec<i32>,
    lane_x: Vec<Option<i32>>,
}

impl Buckets {
    fn reserve_widths(
        &self,
        context: &CoordinateInput<'_>,
        tree: &CrossTree,
    ) -> Result<Vec<i32>, LayoutError> {
        let root = tree.children.len() - 1;
        let inset = add(
            context.graph.params.cluster_pad,
            pipeline::constant(context.input.profile, "cluster_border_w"),
        )?;
        let mut footprint_widths = vec![0; root];
        for cluster in context.clusters {
            let group = tree.graph_groups[cluster.node].ok_or(LayoutError::Domain)?;
            footprint_widths[group] = context.footprints.nodes[cluster.node].w;
        }
        let mut widths = vec![0; root + 1];
        for &group in tree.order.iter().rev() {
            let mut width = self.widths[group];
            for &child in &tree.children[group] {
                width = add(width, widths[child])?;
            }
            width = add(width, self.lane_extent(group, context.graph.params.slot)?)?;
            if group != root {
                width = add(add(width, inset)?, inset)?;
                width = width.max(context.minimum.widths[group]);
                width = width.max(add(add(footprint_widths[group], inset)?, inset)?);
            }
            widths[group] = add(width, self.loop_width[group])?;
        }
        Ok(widths)
    }

    fn allocate(
        &self,
        context: &CoordinateInput<'_>,
        tree: &CrossTree,
        mut x: Vec<i32>,
    ) -> Result<Allocation, LayoutError> {
        let root = tree.children.len() - 1;
        let widths = self.reserve_widths(context, tree)?;
        let mut lefts = vec![0; root + 1];
        let mut lane_x = vec![None; context.graph.edges.len()];
        for &group in &tree.order {
            let start = if group == root {
                lefts[group]
            } else {
                add(lefts[group], context.minimum.origins[group])?
            };
            let mut cursor = add(start, self.widths[group])?;
            if !self.members[group].is_empty() {
                let shift = start
                    .checked_sub(self.low[group])
                    .ok_or(LayoutError::Overflow)?;
                for &node in &self.members[group] {
                    x[node] = add(x[node], shift)?;
                }
            }
            for &child in &tree.children[group] {
                lefts[child] = cursor;
                cursor = add(cursor, widths[child])?;
            }
            if group != root && !self.lanes[group].is_empty() {
                let inset = add(
                    context.graph.params.cluster_pad,
                    pipeline::constant(context.input.profile, "cluster_border_w"),
                )?;
                let lane_extent = self.lane_extent(group, context.graph.params.slot)?;
                cursor = add(lefts[group], widths[group])?
                    .checked_sub(self.loop_width[group])
                    .and_then(|right| right.checked_sub(inset))
                    .and_then(|right| right.checked_sub(lane_extent))
                    .ok_or(LayoutError::Overflow)?;
            }
            for &edge in &self.lanes[group] {
                cursor = add(cursor, context.graph.params.slot)?;
                lane_x[edge] = Some(cursor);
                cursor = add(
                    add(cursor, context.graph.params.slot)?,
                    self.lane_width[group],
                )?;
            }
        }
        Ok(Allocation {
            widths,
            lefts,
            x,
            lane_x,
        })
    }
}

impl CrossTree {
    fn common_spans(&self, context: &CoordinateInput<'_>) -> Result<(), LayoutError> {
        let mut required = vec![None; context.sets.groups.len()];
        for band in &context.minimum.bands {
            if band.right <= band.left || context.minimum.spans[band.group] != Some(band.span) {
                return Err(LayoutError::Domain);
            }
            required[band.group] = Some(band.span);
        }
        for cluster in context.clusters {
            let group = self.graph_groups[cluster.node].ok_or(LayoutError::Domain)?;
            if let Some(span) = required[group]
                && (context.proper.rank[cluster.node] != span.first
                    || context.proper.rank[cluster.bottom] != span.last)
            {
                return Err(LayoutError::Domain);
            }
        }
        Ok(())
    }
}
