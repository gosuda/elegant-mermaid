use super::*;
use crate::layout::layered::{clusters, graph::Proper, labels};

pub(super) struct Prepared {
    pub semantic: Graph,
    pub proper: Proper,
    pub clusters: Vec<clusters::Cluster>,
    pub label_nodes: Vec<(usize, usize)>,
    pub gutter: i32,
    pub paths: Vec<Vec<usize>>,
    pub boundary: Vec<i8>,
    pub budget: bool,
}

pub(super) fn prepare(
    g: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
) -> Result<Prepared, LayoutError> {
    let (mut ranked, mut clusters) = clusters::ranking(g, input);
    if !clusters.is_empty() {
        let reversed = cycles::break_cycles(&ranked)?;
        for (edge, reversed) in ranked.edges.iter_mut().zip(reversed) {
            edge.reversed = reversed;
        }
    }
    let mut semantic = ranked.clone();
    semantic.edges.retain(|edge| edge.decl != i32::MAX);
    let ranks = rank::rank(&ranked)?;
    let mut p = normalize::normalize(&semantic, &ranks.ranks)?;
    let gutter = if input.profile == Profile::Cell {
        g.params.slot
    } else {
        0
    };
    let label_nodes = labels::add_nodes(
        &mut p,
        labels::Measured {
            graph: g,
            stacks: &measurements.route_stacks,
            gutter,
        },
    )?;
    size_ports(&mut p, &mut semantic, input)?;
    let (paths, boundary) = clusters::borders(
        &mut p,
        clusters::BorderInput {
            graph: g,
            input,
            titles: &measurements.titles,
        },
        &mut clusters,
    )?;
    Ok(Prepared {
        semantic,
        proper: p,
        clusters,
        label_nodes,
        gutter,
        paths,
        boundary,
        budget: ranks.budget_exhausted,
    })
}
