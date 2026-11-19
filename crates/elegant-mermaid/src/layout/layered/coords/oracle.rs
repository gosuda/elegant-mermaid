use super::*;
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
    let mut o = initialise(p, ls);
    oracle_align(&mut o);
    place_roots(&mut o);
    shift_classes(&mut o);
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

fn initialise(p: &Proper, ls: Vec<Vec<usize>>) -> Oracle<'_> {
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
    o
}

fn place_roots(o: &mut Oracle<'_>) {
    for l in o.ls.clone() {
        for v in l {
            if o.root[&v] == v {
                o.place(v);
            }
        }
    }
}

fn shift_classes(o: &mut Oracle<'_>) {
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
    align_layers(o, &blocked);
}

fn align_layers(o: &mut Oracle<'_>, blocked: &std::collections::BTreeSet<(usize, usize)>) {
    let p = o.p;
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
pub(super) fn oracle(p: &Proper, layers: &[Vec<usize>]) -> Vec<i32> {
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
