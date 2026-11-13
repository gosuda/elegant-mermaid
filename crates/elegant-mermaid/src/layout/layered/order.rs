use super::{LayoutError, graph::Proper};
use std::cmp::Ordering;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OrderStart {
    #[default]
    Declaration,
    BreadthFirst,
    Reversed,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OrderKey {
    #[default]
    Barycentre,
    Median,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OrderOptions {
    pub start: OrderStart,
    pub key: OrderKey,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderResult {
    pub layers: Vec<Vec<usize>>,
    pub budget_exhausted: bool,
}

pub fn order(p: &Proper, opts: OrderOptions) -> Result<Vec<Vec<usize>>, LayoutError> {
    Ok(order_with_budget(p, opts)?.layers)
}
pub fn order_with_budget(p: &Proper, opts: OrderOptions) -> Result<OrderResult, LayoutError> {
    order_compound(p, opts, &[], &[])
}

pub fn order_compound(
    p: &Proper,
    opts: OrderOptions,
    paths: &[Vec<usize>],
    boundary: &[i8],
) -> Result<OrderResult, LayoutError> {
    let (mut g, mut layers) = OrderGraph::prepare(p)?;
    g.key = opts.key;
    g.paths = paths.to_vec();
    g.boundary = boundary.to_vec();
    let mut declaration = layers.clone();
    let declaration_positions = positions(&declaration, p.nodes.len())?;
    for layer in &mut declaration {
        g.constrain(layer, &[], &declaration_positions)?;
    }
    match opts.start {
        OrderStart::Declaration => {}
        OrderStart::Reversed => {
            for layer in &mut layers {
                layer.reverse();
            }
        }
        OrderStart::BreadthFirst => {
            let mut discovery = vec![usize::MAX; p.nodes.len()];
            let mut next = 0;
            while next < p.nodes.len() {
                let root = (0..p.nodes.len())
                    .filter(|&v| discovery[v] == usize::MAX)
                    .min_by_key(|&v| (next == 0 && !g.above[v].is_empty(), p.nodes[v].node.decl, v))
                    .ok_or(LayoutError::Domain)?;
                let mut queue = std::collections::VecDeque::from([root]);
                discovery[root] = next;
                next += 1;
                while let Some(v) = queue.pop_front() {
                    for &w in &g.below[v] {
                        if discovery[w] == usize::MAX {
                            discovery[w] = next;
                            next += 1;
                            queue.push_back(w);
                        }
                    }
                }
            }
            for layer in &mut layers {
                layer.sort_by_key(|&v| discovery[v]);
            }
        }
    }
    let initial = positions(&layers, p.nodes.len())?;
    for layer in &mut layers {
        g.constrain(layer, &[], &initial)?;
    }
    g.normalise(&mut declaration)?;
    g.normalise(&mut layers)?;
    if g.cross_count(&layers)? >= g.cross_count(&declaration)? {
        layers = declaration;
    }
    if layers.is_empty() {
        return Ok(OrderResult {
            layers,
            budget_exhausted: false,
        });
    }
    g.run(
        layers,
        constant("vector.sweep_max")?,
        constant("vector.sweep_stall")?,
    )
}
fn constant(name: &str) -> Result<usize, LayoutError> {
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|c| c.name == name)
        .and_then(|c| usize::try_from(c.value).ok())
        .filter(|n| *n > 0)
        .ok_or(LayoutError::Domain)
}
#[derive(Default)]
struct OrderGraph {
    above: Vec<Vec<usize>>,
    below: Vec<Vec<usize>>,
    key: OrderKey,
    paths: Vec<Vec<usize>>,
    boundary: Vec<i8>,
    declaration: Vec<i32>,
    movable: Vec<bool>,
}
impl OrderGraph {
    fn prepare(p: &Proper) -> Result<(Self, Vec<Vec<usize>>), LayoutError> {
        let n = p.nodes.len();
        if n != p.rank.len() || i32::try_from(n).is_err() || i32::try_from(p.edges.len()).is_err() {
            return Err(LayoutError::Domain);
        }
        for r in &p.rank {
            if usize::try_from(*r).map_err(|_| LayoutError::Domain)? > n {
                return Err(LayoutError::Domain);
            }
        }
        let mut layers = vec![
            Vec::new();
            p.rank
                .iter()
                .copied()
                .max()
                .map_or(Ok(0), |r| usize::try_from(r)
                    .map(|r| r + 1)
                    .map_err(|_| LayoutError::Domain))?
        ];
        for (v, r) in p.rank.iter().enumerate() {
            let r = usize::try_from(*r).map_err(|_| LayoutError::Domain)?;
            layers[r].push(v);
        }
        for layer in &mut layers {
            layer.sort_by_key(|v| (p.nodes[*v].node.decl, *v));
        }
        let mut g = Self {
            above: vec![Vec::new(); n],
            below: vec![Vec::new(); n],
            key: OrderKey::Barycentre,
            paths: Vec::new(),
            boundary: Vec::new(),
            declaration: p.nodes.iter().map(|n| n.node.decl).collect(),
            movable: p.nodes.iter().map(|node| node.edge >= -1).collect(),
        };
        for e in &p.edges {
            if e.tail >= n
                || e.head >= n
                || i64::from(p.rank[e.head]) - i64::from(p.rank[e.tail]) != 1
            {
                return Err(LayoutError::Domain);
            }
            g.below[e.tail].push(e.head);
            g.above[e.head].push(e.tail);
        }
        Ok((g, layers))
    }
    fn constrain(
        &self,
        layer: &mut [usize],
        neighbours: &[Vec<usize>],
        pos: &[i64],
    ) -> Result<(), LayoutError> {
        if self.paths.is_empty() {
            return Ok(());
        }
        let empty = vec![Vec::new(); self.paths.len()];
        let blocks = super::cluster_order::Blocks {
            paths: &self.paths,
            boundary: &self.boundary,
            declaration: &self.declaration,
            neighbours: if neighbours.is_empty() {
                &empty
            } else {
                neighbours
            },
            positions: pos,
        };
        if neighbours.is_empty() {
            blocks.initial(layer, 0)
        } else {
            blocks.order(layer, 0)
        }
    }
    fn normalise(&self, layers: &mut [Vec<usize>]) -> Result<(), LayoutError> {
        if self.paths.is_empty() {
            return Ok(());
        }
        let context = super::sibling_order::Context {
            paths: &self.paths,
            boundary: &self.boundary,
            declaration: &self.declaration,
        };
        super::sibling_order::normalise(&context, layers)
    }
    fn run(
        &self,
        mut best: Vec<Vec<usize>>,
        limit: usize,
        stall_limit: usize,
    ) -> Result<OrderResult, LayoutError> {
        if limit == 0 || stall_limit == 0 {
            return Err(LayoutError::Domain);
        }
        let mut score = self.cross_count(&best)?;
        let mut stall = 0;
        for sweep in 0..limit {
            let mut trial = best.clone();
            self.sweep(&mut trial, sweep)?;
            self.transpose(&mut trial)?;
            self.normalise(&mut trial)?;
            let next = self.cross_count(&trial)?;
            stall += 1;
            if next < score {
                best = trial;
                score = next;
                stall = 0;
            }
            if sweep + 1 == limit {
                return Ok(OrderResult {
                    layers: best,
                    budget_exhausted: true,
                });
            }
            if stall >= stall_limit {
                break;
            }
        }
        Ok(OrderResult {
            layers: best,
            budget_exhausted: false,
        })
    }
    fn sweep(&self, layers: &mut [Vec<usize>], sweep: usize) -> Result<(), LayoutError> {
        let mut pos = positions(layers, self.above.len())?;
        let neighbours = if sweep.is_multiple_of(2) {
            &self.above
        } else {
            &self.below
        };
        for k in 0..layers.len().saturating_sub(1) {
            let r = if sweep.is_multiple_of(2) {
                k + 1
            } else {
                layers.len() - 2 - k
            };
            if !self.paths.is_empty() {
                self.constrain(&mut layers[r], neighbours, &pos)?;
            } else if self.key == OrderKey::Median {
                let mut keys = vec![0; pos.len()];
                for &v in &layers[r] {
                    let mut values: Vec<_> = neighbours[v].iter().map(|&w| pos[w]).collect();
                    values.sort();
                    keys[v] = if values.is_empty() {
                        pos[v]
                    } else {
                        values[(values.len() - 1) / 2]
                    };
                }
                layers[r].sort_by_key(|&v| keys[v]);
            } else {
                sort_layer(&mut layers[r], neighbours, &pos)?;
            }
            for (i, v) in layers[r].iter().enumerate() {
                pos[*v] = i64::try_from(i).map_err(|_| LayoutError::Overflow)?;
            }
        }
        Ok(())
    }
    fn cross_count(&self, layers: &[Vec<usize>]) -> Result<i64, LayoutError> {
        let pos = positions(layers, self.above.len())?;
        let mut total = 0_i64;
        for pair in layers.windows(2) {
            let mut tree = vec![0_i64; pair[1].len() + 1];
            let mut seen = 0_i64;
            for v in &pair[0] {
                for u in &self.below[*v] {
                    let index = usize::try_from(pos[*u]).map_err(|_| LayoutError::Domain)?;
                    let count = seen - prefix(&tree, index + 1);
                    total = total.checked_add(count).ok_or(LayoutError::Overflow)?;
                }
                for u in &self.below[*v] {
                    let index = usize::try_from(pos[*u]).map_err(|_| LayoutError::Domain)?;
                    add(&mut tree, index + 1);
                    seen += 1;
                }
            }
        }
        Ok(total)
    }
    fn transpose(&self, layers: &mut [Vec<usize>]) -> Result<(), LayoutError> {
        let fuel = self
            .cross_count(layers)?
            .checked_add(1)
            .ok_or(LayoutError::Overflow)?;
        for _ in 0..fuel {
            if !self.transpose_pass(layers)? {
                break;
            }
        }
        Ok(())
    }
    fn transpose_pass(&self, layers: &mut [Vec<usize>]) -> Result<bool, LayoutError> {
        let mut pos = positions(layers, self.above.len())?;
        let mut changed = false;
        for layer in layers {
            for i in 1..layer.len() {
                let (a, b) = (layer[i - 1], layer[i]);
                if !self.paths.is_empty()
                    && (self.paths[a] != self.paths[b] || !self.movable[a] || !self.movable[b])
                {
                    continue;
                }
                let delta = swap_delta(&self.above[a], &self.above[b], &pos)?
                    .checked_add(swap_delta(&self.below[a], &self.below[b], &pos)?)
                    .ok_or(LayoutError::Overflow)?;
                if delta < 0 {
                    layer.swap(i - 1, i);
                    pos.swap(a, b);
                    changed = true;
                }
            }
        }
        Ok(changed)
    }
}
fn positions(layers: &[Vec<usize>], n: usize) -> Result<Vec<i64>, LayoutError> {
    let mut pos = vec![0; n];
    for layer in layers {
        for (i, v) in layer.iter().enumerate() {
            pos[*v] = i64::try_from(i).map_err(|_| LayoutError::Overflow)?;
        }
    }
    Ok(pos)
}
fn sort_layer(
    layer: &mut [usize],
    neighbours: &[Vec<usize>],
    pos: &[i64],
) -> Result<(), LayoutError> {
    let mut keys = vec![(0_i64, 1_i64); pos.len()];
    for v in layer.iter().copied() {
        if neighbours[v].is_empty() {
            keys[v] = (pos[v], 1);
            continue;
        }
        let sum = neighbours[v].iter().try_fold(0_i64, |s, u| {
            s.checked_add(pos[*u]).ok_or(LayoutError::Overflow)
        })?;
        keys[v] = (
            sum,
            i64::try_from(neighbours[v].len()).map_err(|_| LayoutError::Overflow)?,
        );
    }
    let mut error = None;
    layer.sort_by(|a, b| match compare(keys[*a], keys[*b]) {
        Ok(o) => o,
        Err(e) => {
            error = Some(e);
            Ordering::Equal
        }
    });
    error.map_or(Ok(()), Err)
}
fn compare(a: (i64, i64), b: (i64, i64)) -> Result<Ordering, LayoutError> {
    Ok(a.0
        .checked_mul(b.1)
        .ok_or(LayoutError::Overflow)?
        .cmp(&b.0.checked_mul(a.1).ok_or(LayoutError::Overflow)?))
}
fn prefix(tree: &[i64], mut i: usize) -> i64 {
    let mut sum = 0;
    while i > 0 {
        sum += tree[i];
        i &= i - 1;
    }
    sum
}
fn add(tree: &mut [i64], mut i: usize) {
    while i < tree.len() {
        tree[i] += 1;
        i += i.isolate_lowest_one();
    }
}
fn swap_delta(a: &[usize], b: &[usize], pos: &[i64]) -> Result<i64, LayoutError> {
    let mut delta = 0_i64;
    for u in a {
        for v in b {
            delta = delta
                .checked_add(match pos[*v].cmp(&pos[*u]) {
                    Ordering::Less => -1,
                    Ordering::Equal => 0,
                    Ordering::Greater => 1,
                })
                .ok_or(LayoutError::Overflow)?;
        }
    }
    Ok(delta)
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::super::{
        cycles::break_cycles,
        graph::{Edge, Graph, Node, Params},
        normalize::normalize,
        rank::rank,
    };
    use super::*;
    #[test]
    fn initial_cluster_blocks_keep_first_declaration_position() {
        let graph = OrderGraph {
            paths: vec![vec![7], vec![], vec![7]],
            boundary: vec![0; 3],
            declaration: vec![5, 0, 5],
            ..OrderGraph::default()
        };
        let mut layer = vec![0, 1, 2];
        graph.constrain(&mut layer, &[], &[0, 1, 2]).unwrap();
        assert_eq!(layer, vec![0, 2, 1]);
    }
    #[test]
    fn transpose_never_moves_cluster_title_or_anchor() {
        let graph = OrderGraph {
            above: vec![vec![], vec![], vec![1], vec![0]],
            below: vec![vec![3], vec![2], vec![], vec![]],
            paths: vec![vec![7]; 4],
            boundary: vec![0; 4],
            movable: vec![false, true, true, true],
            ..OrderGraph::default()
        };
        let mut layers = vec![vec![0, 1], vec![2, 3]];
        graph.transpose_pass(&mut layers).unwrap();
        assert_eq!(layers[0], vec![0, 1]);
    }
    #[test]
    fn equal_block_keys_keep_loose_nodes_before_child_blocks() {
        let graph = OrderGraph {
            paths: vec![vec![7], vec![], vec![7], vec![], vec![], vec![]],
            boundary: vec![0; 6],
            declaration: vec![1, 1, 2, 3, 4, 5],
            ..OrderGraph::default()
        };
        let neighbours = vec![vec![3], vec![4], vec![5], vec![], vec![], vec![]];
        let mut layer = vec![0, 1, 2];
        graph
            .constrain(&mut layer, &neighbours, &[0, 1, 2, 0, 1, 2])
            .unwrap();
        assert_eq!(layer, vec![1, 0, 2]);
    }
    fn draw(s: &mut u32, lo: usize, hi: usize) -> usize {
        *s ^= *s << 13;
        *s ^= *s >> 17;
        *s ^= *s << 5;
        lo + usize::try_from(*s).unwrap() % (hi - lo + 1)
    }
    fn case(index: usize) -> Proper {
        let mut s = u32::try_from(index).unwrap() + 1;
        let n = draw(&mut s, 2, 30);
        for _ in 0..n {
            draw(&mut s, 0, 15);
        }
        let count = draw(&mut s, 1, n);
        let mut g = Graph {
            nodes: (0..n)
                .map(|i| Node {
                    decl: i32::try_from(i).unwrap(),
                    ..Node::default()
                })
                .collect(),
            edges: Vec::new(),
            params: Params {
                slot: 768,
                pivot_factor: 50,
                node_gap: 1536,
                cluster_pad: 1024,
                rank_gap: 3072,
                port_gap: 512,
            },
        };
        for i in 0..count {
            let tail = draw(&mut s, 0, n - 2);
            let head = draw(&mut s, tail + 1, n - 1);
            g.edges.push(Edge {
                tail,
                head,
                min_len: 1,
                decl: i32::try_from(i).unwrap(),
                reversed: false,
            });
        }
        let reversed = break_cycles(&g).unwrap();
        for (e, r) in g.edges.iter_mut().zip(reversed) {
            e.reversed = r;
        }
        normalize(&g, &rank(&g).unwrap().ranks).unwrap()
    }
    fn naive(g: &OrderGraph, layers: &[Vec<usize>]) -> i64 {
        let pos = positions(layers, g.above.len()).unwrap();
        let edges: Vec<_> = g
            .below
            .iter()
            .enumerate()
            .flat_map(|(u, vs)| vs.iter().map(move |v| (u, *v)))
            .collect();
        let mut count = 0;
        for (i, (a, b)) in edges.iter().enumerate() {
            for (c, d) in &edges[i + 1..] {
                if (pos[*a] - pos[*c]) * (pos[*b] - pos[*d]) < 0
                    && layers.iter().any(|l| l.contains(a) && l.contains(c))
                {
                    count += 1;
                }
            }
        }
        count
    }
    #[test]
    fn layered_order_random_properties() {
        for index in 0..200 {
            let p = case(index);
            let (g, initial) = OrderGraph::prepare(&p).unwrap();
            let got = order(&p, OrderOptions::default()).unwrap();
            assert_eq!(got, order(&p, OrderOptions::default()).unwrap());
            assert!(naive(&g, &got) <= naive(&g, &initial));
            for (a, b) in initial.iter().zip(&got) {
                let mut a = a.clone();
                let mut b = b.clone();
                a.sort();
                b.sort();
                assert_eq!(a, b);
            }
            let mut trial = initial.clone();
            let changed = g.transpose_pass(&mut trial).unwrap();
            assert!(naive(&g, &trial) <= naive(&g, &initial));
            if !changed {
                assert_eq!(trial, initial);
            }
        }
    }
    #[test]
    fn layered_order_accumulator_oracle() {
        for seed in 1..=200 {
            let mut s = seed;
            let a = draw(&mut s, 1, 12);
            let b = draw(&mut s, 1, 12);
            let mut g = OrderGraph {
                above: vec![Vec::new(); a + b],
                below: vec![Vec::new(); a + b],
                ..OrderGraph::default()
            };
            for _ in 0..100 {
                let u = draw(&mut s, 0, a - 1);
                let v = draw(&mut s, a, a + b - 1);
                g.below[u].push(v);
                g.above[v].push(u);
            }
            let layers = vec![(0..a).collect(), (a..a + b).collect()];
            assert_eq!(g.cross_count(&layers).unwrap(), naive(&g, &layers));
        }
    }
    #[test]
    fn layered_order_twin_vectors() {
        let expected = [
            (0, vec![vec![0, 1, 3], vec![2]], 0, 0),
            (
                3,
                vec![vec![0, 2, 3, 4, 5], vec![1, 7, 6, 8], vec![9]],
                2,
                0,
            ),
            (
                6,
                vec![
                    vec![0, 1, 2, 3, 4, 5, 6, 7, 11],
                    vec![9, 10, 8, 15, 13],
                    vec![12, 14],
                ],
                5,
                0,
            ),
            (
                7,
                vec![
                    vec![0, 1, 2, 3, 4, 5, 6, 8, 12, 13],
                    vec![7, 10, 9, 14],
                    vec![11, 15, 18, 16],
                    vec![17],
                ],
                6,
                1,
            ),
            (
                9,
                vec![
                    vec![2, 1, 0, 5, 6, 11, 14, 16],
                    vec![25, 8, 3, 7, 22, 9, 15],
                    vec![4, 12, 10, 13],
                    vec![17, 18],
                    vec![23, 19],
                    vec![24, 20],
                    vec![21],
                ],
                16,
                0,
            ),
        ];
        for (i, want, before, after) in expected {
            let p = case(i);
            let (g, initial) = OrderGraph::prepare(&p).unwrap();
            let got = order(&p, OrderOptions::default()).unwrap();
            assert_eq!(got, want, "case {i}");
            assert_eq!(g.cross_count(&initial).unwrap(), before);
            assert_eq!(g.cross_count(&got).unwrap(), after);
        }
    }
    #[test]
    fn layered_order_crossing_and_budget() {
        let g = OrderGraph {
            above: vec![vec![], vec![], vec![1], vec![0]],
            below: vec![vec![3], vec![2], vec![], vec![]],
            ..OrderGraph::default()
        };
        let result = g.run(vec![vec![0, 1], vec![2, 3]], 24, 4).unwrap();
        assert_eq!(g.cross_count(&result.layers), Ok(0));
        assert!(
            g.run(vec![vec![0, 1], vec![2, 3]], 1, 4)
                .unwrap()
                .budget_exhausted
        );
        assert_eq!(compare((i64::MAX, 2), (1, 2)), Err(LayoutError::Overflow));
    }
    #[test]
    fn layered_order_complete_bipartite_minimum() {
        let mut g = OrderGraph {
            above: vec![Vec::new(); 6],
            below: vec![Vec::new(); 6],
            ..OrderGraph::default()
        };
        for a in 0..3 {
            for b in 3..6 {
                g.below[a].push(b);
                g.above[b].push(a);
            }
        }
        let result = g.run(vec![vec![0, 1, 2], vec![3, 4, 5]], 24, 4).unwrap();
        assert_eq!(g.cross_count(&result.layers), Ok(9));
    }
    #[test]
    fn layered_order_invalid_proper_and_empty() {
        let mut p = case(0);
        p.rank.pop();
        assert_eq!(order(&p, OrderOptions::default()), Err(LayoutError::Domain));
        let empty = OrderGraph {
            above: Vec::new(),
            below: Vec::new(),
            ..OrderGraph::default()
        };
        assert_eq!(empty.run(Vec::new(), 0, 4), Err(LayoutError::Domain));
    }
}

#[cfg(test)]
#[path = "step14_order_tests.rs"]
mod step14_tests;
