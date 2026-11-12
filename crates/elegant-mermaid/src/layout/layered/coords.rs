use super::{
    LayoutError,
    graph::{Params, Proper},
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
            if let Some(owner) = self.paths.get(border).and_then(|path| path.last()) {
                return self
                    .paths
                    .get(member)
                    .is_some_and(|path| path.contains(owner));
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
fn conflicts(p: &Proper, pos: &[usize]) -> Vec<bool> {
    p.edges
        .iter()
        .map(|e| {
            if p.nodes[e.tail].dummy && p.nodes[e.head].dummy {
                return false;
            }
            p.edges.iter().any(|f| {
                p.rank[e.tail] == p.rank[f.tail]
                    && p.nodes[f.tail].dummy
                    && p.nodes[f.head].dummy
                    && ((pos[e.tail] < pos[f.tail] && pos[e.head] > pos[f.head])
                        || (pos[e.tail] > pos[f.tail] && pos[e.head] < pos[f.head]))
            })
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
    let mut top = vec![0; layers.len()];
    for i in 1..top.len() {
        let slots = i64::from(d.slot)
            .checked_mul(i64::from(r.gaps[i - 1].slots))
            .ok_or(LayoutError::Overflow)?;
        top[i] = narrow(add(
            add(
                add(i64::from(top[i - 1]), i64::from(h[i - 1]))?,
                i64::from(d.rank_gap),
            )?,
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
mod tests {
    use super::super::{
        graph::{Edge, Graph, Node},
        normalize::normalize,
        rank::rank,
        route::{route, route_points},
    };
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn cluster_padding_requires_membership_in_border_owner() {
        let (mut p, layers) = case(0);
        p.nodes[0].edge = -2;
        p.nodes[1].edge = -3;
        let mut paths = vec![Vec::new(); p.nodes.len()];
        paths[0] = vec![10, 11];
        paths[1] = vec![10];
        let marked = vec![false; p.edges.len()];
        let mut pass = Pass::new(&p, &layers, &marked, 1536, 0);
        pass.paths = &paths;
        assert!(!pass.border_member(0, 1));
        assert!(pass.border_member(1, 0));
        assert_eq!(
            pass.sep(0, 1),
            i64::from(p.nodes[0].node.w) / 2 + i64::from(p.nodes[1].node.w) / 2 + 1536
        );
    }

    fn case(index: usize) -> (Proper, Vec<Vec<usize>>) {
        let mut s = (index + 1) as u32;
        let mut draw = |lo: usize, hi: usize| {
            s ^= s << 13;
            s ^= s >> 17;
            s ^= s << 5;
            lo + s as usize % (hi - lo + 1)
        };
        let words = [
            "amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor", "iris",
            "juniper", "kelp", "lumen", "maple", "nectar", "onyx", "pine",
        ];
        let n = draw(2, 30);
        let nodes = (0..n)
            .map(|i| {
                let line = format!("n{i}[{}{i}]", words[draw(0, 15)]);
                Node {
                    id: String::new(),
                    decl: i as i32,
                    w: 2048 + 64 * line.len() as i32,
                    h: 2304,
                }
            })
            .collect();
        let count = draw(1, n);
        let edges = (0..count)
            .map(|i| {
                let tail = draw(0, n - 2);
                let head = draw(tail + 1, n - 1);
                Edge {
                    tail,
                    head,
                    min_len: 1,
                    decl: i as i32,
                    reversed: false,
                }
            })
            .collect();
        let g = Graph {
            nodes,
            edges,
            params: Params::for_profile("vector").unwrap(),
        };
        let p = normalize(&g, &rank(&g).unwrap().ranks).unwrap();
        let mut ls = vec![Vec::new(); *p.rank.iter().max().unwrap() as usize + 1];
        for (v, &r) in p.rank.iter().enumerate() {
            ls[r as usize].push(v);
        }
        for l in &mut ls {
            l.sort_by_key(|&v| (p.nodes[v].node.decl, v));
        }
        (p, ls)
    }
    struct Oracle<'a> {
        p: &'a Proper,
        ls: Vec<Vec<usize>>,
        pos: BTreeMap<usize, i64>,
        rank: BTreeMap<usize, usize>,
        root: BTreeMap<usize, usize>,
        align: BTreeMap<usize, usize>,
        sink: BTreeMap<usize, usize>,
        x: BTreeMap<usize, i64>,
        shift: BTreeMap<usize, i64>,
    }
    impl Oracle<'_> {
        fn sep(&self, a: usize, b: usize) -> i64 {
            i64::from(self.p.nodes[a].node.w) / 2
                + i64::from(self.p.nodes[b].node.w) / 2
                + i64::from(self.p.params.node_gap)
        }
        fn place(&mut self, v: usize) {
            if self.x.contains_key(&v) {
                return;
            }
            self.x.insert(v, 0);
            let mut w = v;
            loop {
                if self.pos[&w] > 0 {
                    let pred = self.ls[self.rank[&w]][self.pos[&w] as usize - 1];
                    let u = self.root[&pred];
                    self.place(u);
                    if self.sink[&v] == v {
                        self.sink.insert(v, self.sink[&u]);
                    }
                    if self.sink[&v] == self.sink[&u] {
                        self.x
                            .insert(v, self.x[&v].max(self.x[&u] + self.sep(pred, w)));
                    }
                }
                w = self.align[&w];
                if w == v {
                    break;
                }
            }
            let mut m = self.align[&v];
            while m != v {
                self.x.insert(m, self.x[&v]);
                self.sink.insert(m, self.sink[&v]);
                m = self.align[&m];
            }
        }
    }
    fn oracle_pass(p: &Proper, layers: &[Vec<usize>], k: usize) -> Vec<i64> {
        let mut ls = layers.to_vec();
        if k >= 2 {
            ls.reverse();
        }
        if k % 2 == 1 {
            for l in &mut ls {
                l.reverse();
            }
        }
        let mut o = Oracle {
            p,
            ls,
            pos: BTreeMap::new(),
            rank: BTreeMap::new(),
            root: BTreeMap::new(),
            align: BTreeMap::new(),
            sink: BTreeMap::new(),
            x: BTreeMap::new(),
            shift: BTreeMap::new(),
        };
        for (r, l) in o.ls.iter().enumerate() {
            for (j, &v) in l.iter().enumerate() {
                o.pos.insert(v, j as i64);
                o.rank.insert(v, r);
                o.root.insert(v, v);
                o.align.insert(v, v);
                o.sink.insert(v, v);
            }
        }
        oracle_align(&mut o);
        for l in o.ls.clone() {
            for v in l {
                if o.root[&v] == v {
                    o.place(v);
                }
            }
        }
        for (r, l) in o.ls.iter().enumerate() {
            if let Some(&s) = l.first()
                && o.sink[&s] == s
            {
                o.shift.entry(s).or_insert(0);
            }
            for row in &o.ls {
                for pair in row.windows(2) {
                    let (a, b) = (pair[0], pair[1]);
                    let (sa, sb) = (o.sink[&a], o.sink[&b]);
                    if sa != sb && o.rank[&sb] == r {
                        let d = o.shift[&sb] + o.x[&b] - o.x[&a] - o.sep(a, b);
                        o.shift
                            .entry(sa)
                            .and_modify(|s| *s = (*s).min(d))
                            .or_insert(d);
                    }
                }
            }
        }
        let mut out: Vec<_> = (0..p.nodes.len())
            .map(|v| {
                let x = o.x[&v] + o.shift[&o.sink[&v]];
                if k % 2 == 1 { -x } else { x }
            })
            .collect();
        let lo = *out.iter().min().unwrap();
        for x in &mut out {
            *x -= lo;
        }
        out
    }
    fn oracle_align(o: &mut Oracle<'_>) {
        let p = o.p;
        let mut blocked = std::collections::BTreeSet::new();
        for e in &p.edges {
            if p.nodes[e.tail].dummy && p.nodes[e.head].dummy {
                continue;
            }
            for f in &p.edges {
                if p.rank[e.tail] == p.rank[f.tail]
                    && p.nodes[f.tail].dummy
                    && p.nodes[f.head].dummy
                    && (o.pos[&e.tail] - o.pos[&f.tail]) * (o.pos[&e.head] - o.pos[&f.head]) < 0
                {
                    blocked.insert((e.tail, e.head));
                    blocked.insert((e.head, e.tail));
                }
            }
        }
        for l in &o.ls {
            let mut last = -1;
            for &v in l {
                let mut ns: Vec<_> = p
                    .edges
                    .iter()
                    .filter_map(|e| {
                        let w = if e.head == v {
                            e.tail
                        } else if e.tail == v {
                            e.head
                        } else {
                            return None;
                        };
                        (o.rank[&w] < o.rank[&v]).then_some(w)
                    })
                    .collect();
                ns.sort_by_key(|w| o.pos[w]);
                if ns.is_empty() {
                    continue;
                }
                for i in [(ns.len() - 1) / 2, ns.len() / 2] {
                    let w = ns[i];
                    if o.align[&v] == v && o.pos[&w] > last && !blocked.contains(&(w, v)) {
                        o.align.insert(w, v);
                        o.align.insert(v, o.root[&w]);
                        o.root.insert(v, o.root[&w]);
                        last = o.pos[&w];
                    }
                }
            }
        }
    }
    fn oracle(p: &Proper, layers: &[Vec<usize>]) -> Vec<i32> {
        let mut passes: Vec<_> = (0..4).map(|k| oracle_pass(p, layers, k)).collect();
        let widths: Vec<_> = passes.iter().map(|p| *p.iter().max().unwrap()).collect();
        let best = (0..4).min_by_key(|&k| (widths[k], k)).unwrap();
        for k in [1, 3] {
            for x in &mut passes[k] {
                *x += widths[best] - widths[k];
            }
        }
        let lo = *passes.iter().flatten().min().unwrap();
        (0..p.nodes.len())
            .map(|v| {
                let mut xs: Vec<_> = passes.iter().map(|p| p[v] - lo).collect();
                xs.sort();
                ((xs[1] + xs[2]) / 2) as i32
            })
            .collect()
    }
    #[test]
    fn layered_coordinates_oracle() {
        for i in 0..200 {
            let (p, ls) = case(i);
            let x = cross_coords(&p, &ls).unwrap();
            assert_eq!(x, oracle(&p, &ls), "case {i}");
            for l in &ls {
                for ab in l.windows(2) {
                    assert!(
                        i64::from(x[ab[1]]) - i64::from(x[ab[0]])
                            >= i64::from(p.nodes[ab[0]].node.w) / 2
                                + i64::from(p.nodes[ab[1]].node.w) / 2
                                + 1536
                    );
                }
            }
            let r = route(&p, &ls, &x).unwrap();
            let (y, top) = rank_coords(&p, &ls, &r).unwrap();
            let (routes, _) = route_points(&p, &ls, &x, &y, &top, &r).unwrap();
            assert_slot_geometry(&p, &ls, &r, &top);
            for e in routes {
                assert!(
                    e.points
                        .windows(2)
                        .all(|p| p[0].x == p[1].x || p[0].y == p[1].y)
                );
                let chain = &p.chains[e.original];
                let a = chain[0];
                let b = chain[chain.len() - 1];
                assert_eq!(e.points[0].y, y[a] + p.nodes[a].node.h);
                assert_eq!(e.points.last().unwrap().y, y[b]);
                for (v, n) in p.nodes.iter().enumerate() {
                    if n.dummy || v == a || v == b {
                        continue;
                    }
                    let rect = crate::geom::Rect {
                        x: x[v] - n.node.w / 2,
                        y: y[v],
                        w: n.node.w,
                        h: n.node.h,
                    };
                    assert!(!crate::geom::polyline_hits_rect(&e.points, rect).unwrap());
                }
            }
        }
    }
    fn assert_slot_geometry(p: &Proper, ls: &[Vec<usize>], r: &Routing, top: &[i32]) {
        for (rank, gap) in r.gaps.iter().enumerate() {
            assert!(top[rank + 1] >= top[rank] + heights(p, ls)[rank]);
            for (j, a) in gap.segments.iter().enumerate() {
                for b in &gap.segments[j + 1..] {
                    let overlap = a.source_x.min(a.target_x).max(b.source_x.min(b.target_x))
                        <= a.source_x.max(a.target_x).min(b.source_x.max(b.target_x));
                    if overlap && a.source_x != a.target_x && b.source_x != b.target_x {
                        assert_ne!(a.slot, b.slot);
                    }
                }
            }
        }
    }
    #[test]
    fn layered_coordinate_twin_vectors() {
        let expected = [
            vec![0, 4224, 4224, 8448],
            vec![0, 4224, 8480, 2160, 6352, 6352],
            vec![0, 8512, 0, 4288, 12768, 8512, 4288, 4288, 8512],
            vec![
                8448, 4224, 12672, 16896, 21152, 25472, 16896, 21120, 25344, 21120,
            ],
            vec![
                4384, 8608, 12832, 12832, 17088, 12832, 21344, 25568, 29792, 17088, 21472, 29792,
            ],
        ];
        let tops = [
            vec![0, 5376],
            vec![0, 6144, 12288],
            vec![0, 5376, 11520, 17664],
            vec![0, 6912, 13056],
            vec![0, 7680, 13056],
        ];
        let ys = [
            vec![0, 0, 5376, 0],
            vec![0, 0, 0, 6144, 6144, 12288],
            vec![0, 0, 5376, 5376, 0, 5376, 11520, 17664, 12672],
            vec![0, 6912, 0, 0, 0, 0, 6912, 6912, 6912, 13056],
            vec![0, 0, 0, 7680, 0, 13056, 0, 0, 0, 7680, 7680, 7680],
        ];
        let go_routes: &[&[&[(i32, i32)]]] = &[
            &[&[(4224, 2304), (4224, 5376)]],
            &[
                &[(6352, 8448), (6352, 9600), (6821, 9600), (6821, 12288)],
                &[(2160, 8448), (2160, 9600), (5882, 9600), (5882, 12288)],
                &[(6352, 8448), (6352, 9600), (6821, 9600), (6821, 12288)],
                &[(4224, 2304), (4224, 3456), (5904, 3456), (5904, 6144)],
                &[(8480, 2304), (8480, 3456), (6800, 3456), (6800, 6144)],
            ],
            &[
                &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
                &[(8064, 7680), (8064, 8832), (4736, 8832), (4736, 11520)],
                &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
                &[(0, 2304), (0, 5376)],
                &[(4288, 13824), (4288, 14976), (3850, 14976), (3850, 17664)],
                &[(8512, 2304), (8512, 5376)],
                &[(4288, 7680), (4288, 8832), (3840, 8832), (3840, 11520)],
                &[
                    (8960, 7680),
                    (8960, 8832),
                    (8512, 8832),
                    (8512, 12672),
                    (8512, 14976),
                    (4725, 14976),
                    (4725, 17664),
                ],
            ],
            &[
                &[(25472, 2304), (25472, 4224), (17344, 4224), (17344, 6912)],
                &[
                    (16896, 9216),
                    (16896, 10368),
                    (20672, 10368),
                    (20672, 13056),
                ],
                &[(8896, 2304), (8896, 3456), (21120, 3456), (21120, 6912)],
                &[
                    (25344, 9216),
                    (25344, 10368),
                    (21568, 10368),
                    (21568, 13056),
                ],
                &[
                    (25344, 9216),
                    (25344, 10368),
                    (21568, 10368),
                    (21568, 13056),
                ],
                &[(16896, 2304), (16896, 4224), (16448, 4224), (16448, 6912)],
                &[(8000, 2304), (8000, 3456), (4224, 3456), (4224, 6912)],
            ],
            &[
                &[(29792, 2304), (29792, 7680)],
                &[(13280, 2304), (13280, 3456), (16629, 3456), (16629, 7680)],
                &[(16629, 2304), (16629, 4224), (17546, 4224), (17546, 7680)],
                &[(16629, 2304), (16629, 4224), (17546, 4224), (17546, 7680)],
                &[(17546, 2304), (17546, 4992), (21472, 4992), (21472, 7680)],
                &[(12832, 9984), (12832, 13056)],
                &[(12384, 2304), (12384, 3456), (12832, 3456), (12832, 7680)],
            ],
        ];
        for (i, want) in expected.iter().enumerate() {
            let (p, ls) = case(i);
            let x = cross_coords(&p, &ls).unwrap();
            assert_eq!(&x, want);
            let r = route(&p, &ls, &x).unwrap();
            let (y, top) = rank_coords(&p, &ls, &r).unwrap();
            assert_eq!(top, tops[i]);
            assert_eq!(y, ys[i]);
            let (routes, _) = route_points(&p, &ls, &x, &y, &top, &r).unwrap();
            assert_eq!(routes.len(), go_routes[i].len());
            for (edge, want) in routes.iter().zip(go_routes[i]) {
                assert_eq!(
                    edge.points.iter().map(|p| (p.x, p.y)).collect::<Vec<_>>(),
                    *want
                );
            }
            println!("case {i}: x={x:?} y={y:?} top={top:?} routes={routes:?}");
        }
    }
}
