use super::{
    LayoutError,
    graph::Graph,
    order::{OrderKey, OrderOptions, OrderStart},
    pipeline::{self, Component, Measurements},
};
use crate::layout::input::Input;

pub(super) fn layout(
    g: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
) -> Result<Component, LayoutError> {
    let mut best = pipeline::component_layout(g, input, measurements, OrderOptions::default())?;
    let count = u8::try_from(super::pipeline::constant(input.profile, "portfolio_max"))
        .map_err(|_| LayoutError::Domain)?
        .min(input.options.thoroughness);
    if count == 0 {
        return Err(LayoutError::Domain);
    }
    if count == 1 {
        return Ok(best);
    }
    let numerator = i64::from(super::pipeline::constant(
        input.profile,
        "portfolio_replace_num",
    ));
    let denominator = i64::from(super::pipeline::constant(
        input.profile,
        "portfolio_replace_den",
    ));
    if numerator <= 0 || denominator <= 0 {
        return Err(LayoutError::Domain);
    }
    let mut score = super::cost::score(g, input, measurements, &best)?;
    for index in 2..=count {
        let mut graph;
        let candidate_graph = if index == 3 {
            graph = g.clone();
            greedy(&mut graph);
            &graph
        } else {
            g
        };
        let options = match index {
            2 => OrderOptions {
                start: OrderStart::BreadthFirst,
                key: OrderKey::Barycentre,
            },
            3 => OrderOptions::default(),
            4 => OrderOptions {
                start: OrderStart::Declaration,
                key: OrderKey::Median,
            },
            _ => OrderOptions {
                start: OrderStart::Reversed,
                key: OrderKey::Barycentre,
            },
        };
        let candidate = pipeline::component_layout(candidate_graph, input, measurements, options)?;
        let next = super::cost::score(g, input, measurements, &candidate)?;
        let weighted_new = next.checked_mul(denominator).ok_or(LayoutError::Overflow)?;
        let weighted_best = score.checked_mul(numerator).ok_or(LayoutError::Overflow)?;
        if weighted_new < weighted_best {
            best = candidate;
            score = next;
        }
    }
    Ok(best)
}

fn greedy(g: &mut Graph) {
    let mut alive = vec![true; g.nodes.len()];
    let mut left = Vec::new();
    let mut right = Vec::new();
    while alive.iter().any(|v| *v) {
        let mut incoming = vec![0i64; alive.len()];
        let mut outgoing = vec![0i64; alive.len()];
        for edge in g
            .edges
            .iter()
            .filter(|e| e.decl != i32::MAX && !e.self_loop() && alive[e.tail] && alive[e.head])
        {
            outgoing[edge.tail] += 1;
            incoming[edge.head] += 1;
        }
        let sink = (0..alive.len())
            .filter(|&v| alive[v] && outgoing[v] == 0)
            .min_by_key(|&v| (g.nodes[v].decl, v));
        if let Some(v) = sink {
            alive[v] = false;
            right.push(v);
            continue;
        }
        let source = (0..alive.len())
            .filter(|&v| alive[v] && incoming[v] == 0)
            .min_by_key(|&v| (g.nodes[v].decl, v));
        let selected = source.or_else(|| {
            (0..alive.len())
                .filter(|&v| alive[v])
                .min_by_key(|&v| (incoming[v] - outgoing[v], g.nodes[v].decl, v))
        });
        if let Some(v) = selected {
            alive[v] = false;
            left.push(v);
        }
    }
    left.extend(right.into_iter().rev());
    let mut position = vec![0; alive.len()];
    for (i, v) in left.into_iter().enumerate() {
        position[v] = i;
    }
    for edge in &mut g.edges {
        edge.reversed = edge.decl != i32::MAX && position[edge.tail] > position[edge.head];
    }
}

#[cfg(test)]
#[path = "step14_portfolio_tests.rs"]
mod step14_tests;
