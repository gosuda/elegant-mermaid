use super::{LayoutError, graph::Graph, route::EdgeRoute};
use crate::geom::{Point, Rect};
use crate::layout::input::{Input, SizeRule};

fn exact(g: &Graph, input: &Input, index: usize) -> bool {
    usize::try_from(g.nodes[index].decl)
        .ok()
        .and_then(|decl| input.sizes.get(decl))
        .is_some_and(|rule| matches!(rule, SizeRule::Exact(_)))
}

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

pub fn extents(g: &Graph, sizes: &[(i32, i32)], input: &Input) -> Result<Vec<i32>, LayoutError> {
    let mut counts = vec![0i64; g.nodes.len()];
    let mut extents = vec![0i32; g.nodes.len()];
    for (edge, size) in g.edges.iter().zip(sizes).filter(|(e, _)| e.self_loop()) {
        let node = edge.tail;
        extents[node] = if exact(g, input, node) {
            extents[node].max(size.0)
        } else {
            narrow(
                i64::from(extents[node])
                    + i64::from(g.params.slot) * (counts[node] + 2)
                    + i64::from(size.0),
            )?
        };
        counts[node] += 1;
    }
    for (index, count) in counts.iter().copied().enumerate() {
        if count > 0 && exact(g, input, index) {
            extents[index] =
                narrow(i64::from(g.params.slot) * (2 * count + 1) + i64::from(extents[index]))?;
        }
    }
    Ok(extents)
}

pub fn size_nodes(g: &mut Graph, sizes: &[(i32, i32)], input: &Input) -> Result<(), LayoutError> {
    let bands = bands(g, sizes);
    let mut counts = vec![0i64; g.nodes.len()];
    for edge in g.edges.iter().filter(|e| e.self_loop()) {
        counts[edge.tail] += 1;
    }
    for (i, count) in counts.iter().copied().enumerate() {
        if !exact(g, input, i) {
            g.nodes[i].h = g.nodes[i].h.max(narrow(2 * count * i64::from(bands[i]))?);
        }
    }
    Ok(())
}

fn reserved_height(count: i64, band: i32, minimum: i32) -> Result<i32, LayoutError> {
    let height = count
        .checked_mul(i64::from(band))
        .ok_or(LayoutError::Overflow)?;
    Ok(minimum.max(narrow(height)?))
}

pub fn reservations(
    g: &Graph,
    boxes: &[Rect],
    sizes: &[(i32, i32)],
    extents: &[i32],
    input: &Input,
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
                h: reserved_height(
                    counts[index],
                    bands[index],
                    if exact(g, input, index) { rect.h } else { 0 },
                )?,
            })
        })
        .collect()
}

pub fn place(
    g: &Graph,
    boxes: &[Rect],
    sizes: &[(i32, i32)],
    routes: &mut [EdgeRoute],
    input: &Input,
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
        let rule = usize::try_from(g.nodes[edge.tail].decl)
            .ok()
            .and_then(|decl| input.sizes.get(decl))
            .copied()
            .unwrap_or_default();
        let (points, label) = LoopPlacement {
            rect,
            index: k,
            total: totals[edge.tail],
            band: bands[edge.tail],
            slot,
            size: sizes[i],
            rule,
        }
        .place()?;
        routes[i].points = points;
        labels.push((i, label));
    }
    Ok(labels)
}

pub(super) struct RankPlacement<'a> {
    pub proper: &'a super::graph::Proper,
    pub layers: &'a [Vec<usize>],
    pub y: &'a mut [i32],
    pub top: &'a mut [i32],
}

pub(super) fn reserve_ranks(
    g: &Graph,
    input: &Input,
    sizes: &[(i32, i32)],
    placement: RankPlacement<'_>,
) -> Result<(), LayoutError> {
    let bands = bands(g, sizes);
    let mut counts = vec![0i64; g.nodes.len()];
    for edge in g.edges.iter().filter(|edge| edge.self_loop()) {
        counts[edge.tail] += 1;
    }
    let heights = super::coords::heights(placement.proper, placement.layers);
    let mut extra = vec![0i64; placement.top.len()];
    for (index, count) in counts.into_iter().enumerate() {
        if count == 0 || !exact(g, input, index) {
            continue;
        }
        let rank =
            usize::try_from(placement.proper.rank[index]).map_err(|_| LayoutError::Domain)?;
        let reserved = reserved_height(count, bands[index], g.nodes[index].h)?;
        let end = i64::from(placement.y[index]) + i64::from(reserved);
        let rank_end = i64::from(placement.top[rank]) + i64::from(heights[rank]);
        extra[rank] = extra[rank].max(end - rank_end);
    }
    let mut shift = 0i64;
    for (rank, top) in placement.top.iter_mut().enumerate() {
        *top = narrow(i64::from(*top) + shift)?;
        let added = extra[rank];
        extra[rank] = shift;
        shift = i64::from(narrow(shift + added)?);
    }
    for (index, y) in placement.y.iter_mut().enumerate() {
        let rank =
            usize::try_from(placement.proper.rank[index]).map_err(|_| LayoutError::Domain)?;
        *y = narrow(i64::from(*y) + extra[rank])?;
    }
    Ok(())
}

struct LoopPlacement {
    rect: Rect,
    index: i64,
    total: i64,
    band: i32,
    slot: i64,
    size: (i32, i32),
    rule: SizeRule,
}

impl LoopPlacement {
    fn place(self) -> Result<(Vec<Point>, Rect), LayoutError> {
        let rect = self.rect;
        let k = self.index;
        let slot = self.slot;
        let right = i64::from(rect.x) + i64::from(rect.w);
        let centre = i64::from(rect.y) + k * i64::from(self.band) + i64::from(self.band) / 2;
        let x = narrow(right + slot * (k + 1))?;
        let a = narrow(centre - slot)?;
        let b = narrow(centre + slot)?;
        let points = if matches!(self.rule, SizeRule::Exact(_)) {
            let denominator = 2 * self.total + 1;
            let endpoint_a =
                narrow(i64::from(rect.y) + (2 * k + 1) * i64::from(rect.h) / denominator)?;
            let endpoint_b =
                narrow(i64::from(rect.y) + (2 * k + 2) * i64::from(rect.h) / denominator)?;
            let lane_a = narrow(right + slot * (2 * k + 1))?;
            let lane_b = narrow(right + slot * (2 * k + 2))?;
            vec![
                Point {
                    x: narrow(right)?,
                    y: endpoint_a,
                },
                Point {
                    x: lane_a,
                    y: endpoint_a,
                },
                Point { x: lane_a, y: b },
                Point { x: lane_b, y: b },
                Point {
                    x: lane_b,
                    y: endpoint_b,
                },
                Point {
                    x: narrow(right)?,
                    y: endpoint_b,
                },
            ]
        } else {
            vec![
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
            ]
        };
        let label = Rect {
            x: narrow(
                right
                    + slot
                        * (if matches!(self.rule, SizeRule::Exact(_)) {
                            2 * self.total + 1
                        } else {
                            self.total + 1
                        }),
            )?,
            y: narrow(centre - i64::from(self.size.1) / 2)?,
            w: self.size.0,
            h: self.size.1,
        };
        Ok((points, label))
    }
}
