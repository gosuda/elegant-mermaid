use super::{
    LayoutError,
    graph::{Params, Proper, ProperEdge},
    route::Routing,
};

pub(crate) fn narrow(n: i64) -> Result<i32, LayoutError> {
    i32::try_from(n).map_err(|_| LayoutError::Overflow)
}
fn add(a: i64, b: i64) -> Result<i64, LayoutError> {
    a.checked_add(b).ok_or(LayoutError::Overflow)
}
fn sub(a: i64, b: i64) -> Result<i64, LayoutError> {
    a.checked_sub(b).ok_or(LayoutError::Overflow)
}
pub(crate) fn params(p: &Proper) -> Result<Params, LayoutError> {
    let mut d = Params::for_profile("vector")?;
    if p.params.slot != 0 {
        d.slot = p.params.slot;
    }
    if p.params.node_gap != 0 {
        d.node_gap = p.params.node_gap;
    }
    if p.params.rank_gap != 0 {
        d.rank_gap = p.params.rank_gap;
    }
    if p.params.port_gap != 0 {
        d.port_gap = p.params.port_gap;
    }
    if p.params.cluster_pad != 0 {
        d.cluster_pad = p.params.cluster_pad;
    }
    if d.slot < 1 || d.node_gap < 1 || d.rank_gap < 1 {
        return Err(LayoutError::Domain);
    }
    Ok(d)
}
pub(crate) fn positions(p: &Proper, layers: &[Vec<usize>]) -> Result<Vec<usize>, LayoutError> {
    let n = p.nodes.len();
    if p.rank.len() != n || p.nodes.iter().any(|v| v.node.w < 0 || v.node.h < 0) {
        return Err(LayoutError::Domain);
    }
    i32::try_from(n).map_err(|_| LayoutError::Overflow)?;
    let mut pos = vec![usize::MAX; n];
    for (r, l) in layers.iter().enumerate() {
        for (j, &v) in l.iter().enumerate() {
            if v >= n
                || pos[v] != usize::MAX
                || i64::from(p.rank[v]) != i64::try_from(r).map_err(|_| LayoutError::Overflow)?
            {
                return Err(LayoutError::Domain);
            }
            pos[v] = j;
        }
    }
    if pos.contains(&usize::MAX)
        || p.edges.iter().any(|e| {
            e.tail >= n || e.head >= n || i64::from(p.rank[e.head]) != i64::from(p.rank[e.tail]) + 1
        })
    {
        return Err(LayoutError::Domain);
    }
    Ok(pos)
}
struct Pass<'a> {
    p: &'a Proper,
    layers: Vec<Vec<usize>>,
    pos: Vec<usize>,
    rank: Vec<usize>,
    root: Vec<usize>,
    align: Vec<usize>,
    sink: Vec<usize>,
    x: Vec<i64>,
    shift: Vec<Option<i64>>,
    set: Vec<bool>,
    marked: &'a [bool],
    gap: i64,
    paths: &'a [Vec<usize>],
}
impl<'a> Pass<'a> {
    fn new(p: &'a Proper, layers: &[Vec<usize>], marked: &'a [bool], gap: i64, k: usize) -> Self {
        let n = p.nodes.len();
        let mut ls = layers.to_vec();
        if k >= 2 {
            ls.reverse();
        }
        if k % 2 == 1 {
            for l in &mut ls {
                l.reverse();
            }
        }
        let mut pos = vec![0; n];
        let mut rank = vec![0; n];
        for (r, l) in ls.iter().enumerate() {
            for (j, &v) in l.iter().enumerate() {
                pos[v] = j;
                rank[v] = r;
            }
        }
        Self {
            p,
            layers: ls,
            pos,
            rank,
            root: (0..n).collect(),
            align: (0..n).collect(),
            sink: (0..n).collect(),
            x: vec![0; n],
            shift: vec![None; n],
            set: vec![false; n],
            marked,
            gap,
            paths: &[],
        }
    }
    fn neighbours(&self, v: usize) -> Vec<(usize, usize)> {
        let mut es: Vec<_> = self
            .p
            .edges
            .iter()
            .enumerate()
            .filter_map(|(i, e)| {
                let w = if e.head == v {
                    e.tail
                } else if e.tail == v {
                    e.head
                } else {
                    return None;
                };
                (self.rank[w] < self.rank[v]).then_some((i, w))
            })
            .collect();
        es.sort_by_key(|&(i, w)| (self.pos[w], i));
        es
    }
    fn alignment(&mut self) {
        for r in 0..self.layers.len() {
            let mut last = None;
            for j in 0..self.layers[r].len() {
                let v = self.layers[r][j];
                let es = self.neighbours(v);
                if es.is_empty() {
                    continue;
                }
                for k in [(es.len() - 1) / 2, es.len() / 2] {
                    let (e, w) = es[k];
                    if self.align[v] == v && !self.marked[e] && last.is_none_or(|l| self.pos[w] > l)
                    {
                        self.align[w] = v;
                        self.align[v] = self.root[w];
                        self.root[v] = self.root[w];
                        last = Some(self.pos[w]);
                    }
                }
            }
        }
    }
    fn sep(&self, a: usize, b: usize) -> i64 {
        let interior = self.border_member(a, b);
        let anchor = ((self.p.nodes[a].edge == -4 && self.p.nodes[b].edge == -5)
            || (self.p.nodes[b].edge == -4 && self.p.nodes[a].edge == -5))
            && self.p.nodes[a].node.decl == self.p.nodes[b].node.decl;
        let gap = if interior {
            i64::from(self.p.params.cluster_pad)
        } else if anchor {
            0
        } else {
            self.gap
        };
        i64::from(self.p.nodes[a].node.w) / 2 + i64::from(self.p.nodes[b].node.w) / 2 + gap
    }
    fn border_member(&self, a: usize, b: usize) -> bool {
        for (border, member) in [(a, b), (b, a)] {
            if !matches!(self.p.nodes[border].edge, -2 | -3) {
                continue;
            }
            if let Some(owner) = self.paths.get(border).and_then(|path| path.last())
                && self
                    .paths
                    .get(member)
                    .is_some_and(|path| path.contains(owner))
            {
                return true;
            }
        }
        false
    }
    fn predecessor(&self, w: usize) -> Option<usize> {
        self.pos[w]
            .checked_sub(1)
            .map(|j| self.layers[self.rank[w]][j])
    }
    fn place(&mut self, v: usize, fuel: &mut usize) -> Result<(), LayoutError> {
        let mut stack = vec![(v, v)];
        self.set[v] = true;
        while let Some(&(v, w)) = stack.last() {
            *fuel = fuel.checked_sub(1).ok_or(LayoutError::Domain)?;
            if let Some(pred) = self.predecessor(w) {
                let u = self.root[pred];
                if !self.set[u] {
                    self.set[u] = true;
                    stack.push((u, u));
                    continue;
                }
                if self.sink[v] == v {
                    self.sink[v] = self.sink[u];
                }
                if self.sink[v] == self.sink[u] {
                    self.x[v] = self.x[v].max(add(self.x[u], self.sep(pred, w))?);
                }
            }
            let next = self.align[w];
            stack.pop();
            if next != v {
                stack.push((v, next));
                continue;
            }
            let mut m = self.align[v];
            while m != v {
                self.x[m] = self.x[v];
                self.sink[m] = self.sink[v];
                self.set[m] = true;
                m = self.align[m];
            }
        }
        Ok(())
    }
    fn offsets(&mut self) -> Result<(), LayoutError> {
        let mut pairs = vec![Vec::new(); self.layers.len()];
        for l in &self.layers {
            for ab in l.windows(2) {
                let (a, b) = (ab[0], ab[1]);
                if self.sink[a] != self.sink[b] {
                    pairs[self.rank[self.sink[b]]].push((a, b));
                }
            }
        }
        for (r, ps) in pairs.iter().enumerate() {
            if let Some(&s) = self.layers[r].first()
                && self.sink[s] == s
                && self.shift[s].is_none()
            {
                self.shift[s] = Some(0);
            }
            for &(a, b) in ps {
                let (sa, sb) = (self.sink[a], self.sink[b]);
                let shift = self.shift[sb].ok_or(LayoutError::Domain)?;
                let d = sub(sub(add(shift, self.x[b])?, self.x[a])?, self.sep(a, b))?;
                self.shift[sa] = Some(self.shift[sa].map_or(d, |s| s.min(d)));
            }
        }
        for v in 0..self.x.len() {
            self.x[v] = add(
                self.x[v],
                self.shift[self.sink[v]].ok_or(LayoutError::Domain)?,
            )?;
        }
        Ok(())
    }
    fn run(mut self, k: usize) -> Result<Vec<i64>, LayoutError> {
        self.alignment();
        let mut fuel = self.x.len().checked_mul(2).ok_or(LayoutError::Overflow)?;
        for r in 0..self.layers.len() {
            for j in 0..self.layers[r].len() {
                let v = self.layers[r][j];
                if self.root[v] == v && !self.set[v] {
                    self.place(v, &mut fuel)?;
                }
            }
        }
        self.offsets()?;
        if k % 2 == 1 {
            for x in &mut self.x {
                *x = sub(0, *x)?;
            }
        }
        if let Some(lo) = self.x.iter().min().copied() {
            for x in &mut self.x {
                *x = sub(*x, lo)?;
            }
        }
        Ok(self.x)
    }
}
fn border_chain(p: &Proper, e: &ProperEdge) -> bool {
    let (tail, head) = (p.nodes[e.tail].edge, p.nodes[e.head].edge);
    tail == head && matches!(tail, -2 | -3)
}
fn crosses_among(p: &Proper, pos: &[usize], e: &ProperEdge, among: &[bool]) -> bool {
    p.edges.iter().zip(among).any(|(f, &member)| {
        member
            && p.rank[e.tail] == p.rank[f.tail]
            && ((pos[e.tail] < pos[f.tail] && pos[e.head] > pos[f.head])
                || (pos[e.tail] > pos[f.tail] && pos[e.head] < pos[f.head]))
    })
}
fn conflicts(p: &Proper, pos: &[usize]) -> Vec<bool> {
    let chain: Vec<bool> = p.edges.iter().map(|e| border_chain(p, e)).collect();
    let inner: Vec<bool> = p
        .edges
        .iter()
        .map(|e| p.nodes[e.tail].dummy && p.nodes[e.head].dummy)
        .collect();
    p.edges
        .iter()
        .enumerate()
        .map(|(i, e)| {
            !chain[i]
                && (crosses_among(p, pos, e, &chain)
                    || (!inner[i] && crosses_among(p, pos, e, &inner)))
        })
        .collect()
}
pub fn cross_coords(p: &Proper, layers: &[Vec<usize>]) -> Result<Vec<i32>, LayoutError> {
    cross_coords_compound(p, layers, &[])
}

pub fn cross_coords_compound(
    p: &Proper,
    layers: &[Vec<usize>],
    paths: &[Vec<usize>],
) -> Result<Vec<i32>, LayoutError> {
    let pos = positions(p, layers)?;
    let d = params(p)?;
    if pos.is_empty() {
        return Ok(Vec::new());
    }
    let marked = conflicts(p, &pos);
    let mut passes = Vec::with_capacity(4);
    for k in 0..4 {
        let mut pass = Pass::new(p, layers, &marked, i64::from(d.node_gap), k);
        pass.paths = paths;
        passes.push(pass.run(k)?);
    }
    balance(passes)
}

pub(super) fn cross_coords_regions(
    layers: &mut [Vec<usize>],
    context: super::regions::CoordinateInput<'_>,
) -> Result<super::regions::Placement, LayoutError> {
    let tree = super::regions::CrossTree::new(&context)?;
    tree.pin(&context, layers)?;
    let desired = cross_coords_compound(context.proper, layers, context.paths)?;
    super::regions::Placement::solve(context, desired, tree)
}
fn balance(mut passes: Vec<Vec<i64>>) -> Result<Vec<i32>, LayoutError> {
    let widths: Vec<_> = passes
        .iter()
        .map(|x| x.iter().copied().max().unwrap_or(0))
        .collect();
    let best = (0..4)
        .min_by_key(|&k| (widths[k], k))
        .ok_or(LayoutError::Domain)?;
    let mut low = 0;
    for k in [1, 3] {
        let d = sub(widths[best], widths[k])?;
        low = low.min(d);
        for x in &mut passes[k] {
            *x = add(*x, d)?;
        }
    }
    (0..passes[0].len())
        .map(|i| {
            let mut v = [0; 4];
            for k in 0..4 {
                v[k] = sub(passes[k][i], low)?;
            }
            v.sort();
            narrow(add(v[1], v[2])? / 2)
        })
        .collect()
}
pub(crate) fn heights(p: &Proper, layers: &[Vec<usize>]) -> Vec<i32> {
    layers
        .iter()
        .map(|l| l.iter().map(|&v| p.nodes[v].node.h).max().unwrap_or(0))
        .collect()
}
fn label_ranks(p: &Proper, layers: &[Vec<usize>]) -> Vec<bool> {
    layers
        .iter()
        .map(|layer| {
            !layer.is_empty()
                && layer.iter().all(|&v| p.nodes[v].dummy)
                && layer.iter().any(|&v| p.nodes[v].label)
        })
        .collect()
}
fn half_gap(rank_gap: i32) -> i64 {
    (i64::from(rank_gap) + 1) / 2
}
pub fn rank_coords(
    p: &Proper,
    layers: &[Vec<usize>],
    r: &Routing,
) -> Result<(Vec<i32>, Vec<i32>), LayoutError> {
    positions(p, layers)?;
    let d = params(p)?;
    if r.gaps.len() != layers.len().saturating_sub(1) || r.gaps.iter().any(|g| g.slots < 0) {
        return Err(LayoutError::Domain);
    }
    let h = heights(p, layers);
    let label_rank = label_ranks(p, layers);
    let mut top = vec![0; layers.len()];
    for i in 1..top.len() {
        let gap = if label_rank[i - 1] || label_rank[i] {
            half_gap(d.rank_gap)
        } else {
            i64::from(d.rank_gap)
        };
        let slots = i64::from(d.slot)
            .checked_mul(i64::from(r.gaps[i - 1].slots))
            .ok_or(LayoutError::Overflow)?;
        top[i] = narrow(add(
            add(add(i64::from(top[i - 1]), i64::from(h[i - 1]))?, gap)?,
            slots,
        )?)?;
    }
    let y = p
        .nodes
        .iter()
        .enumerate()
        .map(|(v, n)| {
            let rank = usize::try_from(p.rank[v]).map_err(|_| LayoutError::Domain)?;
            narrow(i64::from(top[rank]) + i64::from(h[rank] - n.node.h) / 2)
        })
        .collect::<Result<_, _>>()?;
    Ok((y, top))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
#[path = "coords_tests.rs"]
mod tests;
