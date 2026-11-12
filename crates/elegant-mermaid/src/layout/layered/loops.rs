use super::{LayoutError, graph::Graph, route::EdgeRoute};
use crate::geom::{Point, Rect};

fn narrow(value: i64) -> Result<i32, LayoutError> {
    i32::try_from(value).map_err(|_| LayoutError::Overflow)
}

pub fn bands(g: &Graph, sizes: &[(i32, i32)]) -> Vec<i32> {
    let mut bands = vec![2 * g.params.slot; g.nodes.len()];
    for (edge, size) in g.edges.iter().zip(sizes) {
        if edge.self_loop() {
            bands[edge.tail] = bands[edge.tail].max(size.1);
        }
    }
    bands
}

pub fn extents(g: &Graph, sizes: &[(i32, i32)]) -> Result<Vec<i32>, LayoutError> {
    let mut counts = vec![0i64; g.nodes.len()];
    let mut extents = vec![0i32; g.nodes.len()];
    for (edge, size) in g.edges.iter().zip(sizes).filter(|(e, _)| e.self_loop()) {
        let node = edge.tail;
        extents[node] = narrow(
            i64::from(extents[node])
                + i64::from(g.params.slot) * (counts[node] + 2)
                + i64::from(size.0),
        )?;
        counts[node] += 1;
    }
    Ok(extents)
}

pub fn size_nodes(g: &mut Graph, sizes: &[(i32, i32)]) -> Result<(), LayoutError> {
    let bands = bands(g, sizes);
    let mut counts = vec![0i64; g.nodes.len()];
    for edge in g.edges.iter().filter(|e| e.self_loop()) {
        counts[edge.tail] += 1;
    }
    for (i, node) in g.nodes.iter_mut().enumerate() {
        node.h = node.h.max(narrow(2 * counts[i] * i64::from(bands[i]))?);
    }
    Ok(())
}

pub fn reservations(
    g: &Graph,
    boxes: &[Rect],
    sizes: &[(i32, i32)],
    extents: &[i32],
) -> Result<Vec<Rect>, LayoutError> {
    let bands = bands(g, sizes);
    let mut counts = vec![0i64; g.nodes.len()];
    for edge in g.edges.iter().filter(|edge| edge.self_loop()) {
        counts[edge.tail] += 1;
    }
    boxes
        .iter()
        .enumerate()
        .filter(|(index, _)| counts[*index] > 0)
        .map(|(index, rect)| {
            Ok(Rect {
                x: narrow(i64::from(rect.x) + i64::from(rect.w))?,
                y: rect.y,
                w: extents[index],
                h: narrow(counts[index] * i64::from(bands[index]))?,
            })
        })
        .collect()
}

pub fn place(
    g: &Graph,
    boxes: &[Rect],
    sizes: &[(i32, i32)],
    routes: &mut [EdgeRoute],
) -> Result<Vec<(usize, Rect)>, LayoutError> {
    let bands = bands(g, sizes);
    let mut counts = vec![0i64; g.nodes.len()];
    let mut totals = vec![0i64; g.nodes.len()];
    for edge in g.edges.iter().filter(|edge| edge.self_loop()) {
        totals[edge.tail] += 1;
    }
    let mut labels = Vec::new();
    let slot = i64::from(g.params.slot);
    for (i, edge) in g.edges.iter().enumerate().filter(|(_, e)| e.self_loop()) {
        let rect = boxes[edge.tail];
        let k = counts[edge.tail];
        counts[edge.tail] += 1;
        let right = i64::from(rect.x) + i64::from(rect.w);
        let centre =
            i64::from(rect.y) + k * i64::from(bands[edge.tail]) + i64::from(bands[edge.tail]) / 2;
        let x = narrow(right + slot * (k + 1))?;
        let a = narrow(centre - slot)?;
        let b = narrow(centre + slot)?;
        routes[i].points = vec![
            Point {
                x: narrow(right)?,
                y: a,
            },
            Point { x, y: a },
            Point { x, y: b },
            Point {
                x: narrow(right)?,
                y: b,
            },
        ];
        labels.push((
            i,
            Rect {
                x: narrow(right + slot * (totals[edge.tail] + 1))?,
                y: narrow(centre - i64::from(sizes[i].1) / 2)?,
                w: sizes[i].0,
                h: sizes[i].1,
            },
        ));
    }
    Ok(labels)
}
