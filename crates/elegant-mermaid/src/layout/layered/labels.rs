use super::{
    LayoutError,
    graph::{Graph, Proper},
};
use crate::{
    geom::{Rect, Size},
    layout::input::Input,
    measure,
    scene::Direction,
};

pub struct Entry {
    pub index: usize,
    pub size: Size,
    pub rank_offset: i32,
}
pub struct Stack {
    pub entries: Vec<Entry>,
    pub size: Size,
}
pub struct Measured<'a> {
    pub graph: &'a Graph,
    pub stacks: &'a [Stack],
    pub gutter: i32,
}
pub struct Placement<'a> {
    pub proper: &'a Proper,
    pub x: &'a [i32],
    pub y: &'a [i32],
    pub gutter: i32,
}
pub struct Placed {
    pub labels: Vec<(usize, Rect)>,
    pub reservations: Vec<(usize, Rect)>,
}

pub fn stacks(
    input: &Input,
    lines: &[Vec<measure::StyledLine<'_>>],
) -> Result<Vec<Stack>, LayoutError> {
    let slot = super::pipeline::constant(input.profile, "slot");
    input
        .routes
        .iter()
        .map(|route| {
            let mut stack = Stack {
                entries: Vec::new(),
                size: Size { w: 0, h: 0 },
            };
            for (index, _) in input
                .labels
                .iter()
                .enumerate()
                .filter(|(_, label)| label.owner == route.id)
            {
                let measured = lines.get(index).ok_or(LayoutError::Domain)?;
                let size = label_size(input, measured)?;
                let offset = narrow(
                    i64::from(stack.size.h)
                        + if stack.entries.is_empty() {
                            0
                        } else {
                            i64::from(slot)
                        },
                )?;
                stack.entries.push(Entry {
                    index,
                    size,
                    rank_offset: offset,
                });
                stack.size.w = stack.size.w.max(size.w);
                stack.size.h = narrow(i64::from(offset) + i64::from(size.h))?;
            }
            Ok(stack)
        })
        .collect()
}

fn label_size(input: &Input, measured: &[measure::StyledLine<'_>]) -> Result<Size, LayoutError> {
    let width = measured.iter().map(|line| line.width).max().unwrap_or(0);
    let height = narrow(
        i64::try_from(measured.len()).map_err(|_| LayoutError::Overflow)?
            * i64::from(super::pipeline::constant(input.profile, "line_h")),
    )?;
    Ok(
        if matches!(input.direction, Direction::Lr | Direction::Rl) {
            Size {
                w: height,
                h: width,
            }
        } else {
            Size {
                w: width,
                h: height,
            }
        },
    )
}

pub fn add_nodes(
    proper: &mut Proper,
    measured: Measured<'_>,
) -> Result<Vec<(usize, usize)>, LayoutError> {
    let mut labels = Vec::new();
    for (edge_index, edge) in measured.graph.edges.iter().enumerate() {
        if edge.self_loop() {
            continue;
        }
        let declaration = usize::try_from(edge.decl).map_err(|_| LayoutError::Domain)?;
        let Some(stack) = measured.stacks.get(declaration) else {
            continue;
        };
        if stack.entries.is_empty() {
            continue;
        }
        let chain = proper.chains.get(edge_index).ok_or(LayoutError::Domain)?;
        let middle = chain.len().checked_sub(1).ok_or(LayoutError::Domain)? / 2;
        let node = *chain.get(middle).ok_or(LayoutError::Domain)?;
        proper.nodes[node].node.w = narrow(i64::from(stack.size.w) + i64::from(measured.gutter))?;
        proper.nodes[node].node.h = stack.size.h;
        proper.nodes[node].label = true;
        labels.push((declaration, node));
    }
    Ok(labels)
}

pub fn place(
    nodes: Vec<(usize, usize)>,
    placement: Placement<'_>,
    stacks: &[Stack],
) -> Result<Placed, LayoutError> {
    let mut result = Placed {
        labels: Vec::new(),
        reservations: Vec::with_capacity(nodes.len()),
    };
    for (route, node) in nodes {
        let size = &placement.proper.nodes[node].node;
        let reserved = Rect {
            x: narrow(i64::from(placement.x[node]) - i64::from(size.w) / 2)?,
            y: placement.y[node],
            w: size.w,
            h: size.h,
        };
        result.reservations.push((route, reserved));
        append(
            &stacks[route],
            Rect {
                x: narrow(i64::from(reserved.x) + i64::from(placement.gutter))?,
                w: reserved.w - placement.gutter,
                ..reserved
            },
            &mut result.labels,
        )?;
    }
    Ok(result)
}

pub fn replace(
    graph: &Graph,
    stacks: &[Stack],
    envelopes: Vec<(usize, Rect)>,
    placed: &mut Placed,
) -> Result<(), LayoutError> {
    for (edge, rect) in envelopes {
        let declaration =
            usize::try_from(graph.edges[edge].decl).map_err(|_| LayoutError::Domain)?;
        let stack = stacks.get(declaration).ok_or(LayoutError::Domain)?;
        if stack.entries.is_empty() {
            continue;
        }
        placed
            .labels
            .retain(|(existing, _)| !stack.entries.iter().any(|entry| entry.index == *existing));
        placed
            .reservations
            .retain(|(route, _)| *route != declaration);
        placed.reservations.push((declaration, rect));
        append(stack, rect, &mut placed.labels)?;
    }
    Ok(())
}

fn append(stack: &Stack, rect: Rect, labels: &mut Vec<(usize, Rect)>) -> Result<(), LayoutError> {
    for entry in &stack.entries {
        labels.push((
            entry.index,
            Rect {
                x: rect.x,
                y: narrow(i64::from(rect.y) + i64::from(entry.rank_offset))?,
                w: entry.size.w,
                h: entry.size.h,
            },
        ));
    }
    Ok(())
}
fn narrow(value: i64) -> Result<i32, LayoutError> {
    i32::try_from(value).map_err(|_| LayoutError::Overflow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::layered::graph::{Edge, Node, Params};

    #[test]
    fn layered_label_uses_floor_midpoint_rank() -> Result<(), LayoutError> {
        let graph = Graph {
            nodes: vec![Node::default(); 2],
            edges: vec![Edge {
                tail: 0,
                head: 1,
                min_len: 2,
                decl: 0,
                reversed: false,
            }],
            params: Params::for_profile("vector")?,
        };
        let stacks = [Stack {
            entries: vec![Entry {
                index: 0,
                size: Size { w: 12, h: 7 },
                rank_offset: 0,
            }],
            size: Size { w: 12, h: 7 },
        }];
        for span in 2..=5 {
            let mut proper = super::super::normalize::normalize(&graph, &[0, span])?;
            let labels = add_nodes(
                &mut proper,
                Measured {
                    graph: &graph,
                    stacks: &stacks,
                    gutter: 0,
                },
            )?;
            assert_eq!(labels.len(), 1);
            assert_eq!(proper.rank[labels[0].1], span / 2);
        }
        Ok(())
    }
}
