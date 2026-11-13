use super::LayoutError;
use std::collections::BTreeMap;

pub(super) struct Context<'a> {
    pub paths: &'a [Vec<usize>],
    pub boundary: &'a [i8],
    pub declaration: &'a [i32],
}

struct Item {
    nodes: Vec<usize>,
    child: Option<usize>,
}

struct Siblings {
    chains: Vec<Vec<usize>>,
    parent: Vec<Option<usize>>,
    decl: Vec<i32>,
    ranks: usize,
    left: Vec<Option<usize>>,
    span: Vec<Option<(usize, usize)>>,
    key: Vec<(i64, i64)>,
    number: Vec<usize>,
}

pub(super) fn normalise(
    context: &Context<'_>,
    layers: &mut [Vec<usize>],
) -> Result<(), LayoutError> {
    let mut s = Siblings::new(context, layers)?;
    for group in s.groups() {
        s.linearise(&group)?;
    }
    for layer in layers.iter_mut() {
        let placed = s.level(layer, 0);
        layer.copy_from_slice(&placed);
    }
    Ok(())
}

impl Siblings {
    fn new(context: &Context<'_>, layers: &[Vec<usize>]) -> Result<Self, LayoutError> {
        let mut index = BTreeMap::new();
        for (v, &side) in context.boundary.iter().enumerate() {
            if let (1, Some(&cluster)) = (side, context.paths[v].last()) {
                let next = index.len();
                index.entry(cluster).or_insert(next);
            }
        }
        let n = index.len();
        let ranks = layers.len();
        let mut s = Self {
            chains: context
                .paths
                .iter()
                .map(|path| {
                    path.iter()
                        .filter_map(|id| index.get(id).copied())
                        .collect()
                })
                .collect(),
            parent: vec![None; n],
            decl: vec![0; n],
            ranks,
            left: vec![None; n * ranks],
            span: vec![None; n],
            key: vec![(0, 1); n],
            number: vec![0; n],
        };
        s.left_borders(context, layers)?;
        Ok(s)
    }

    fn left_borders(
        &mut self,
        context: &Context<'_>,
        layers: &[Vec<usize>],
    ) -> Result<(), LayoutError> {
        for (r, layer) in layers.iter().enumerate() {
            for (position, &v) in layer.iter().enumerate() {
                let chain = &self.chains[v];
                let Some((&c, outer)) = chain.split_last().filter(|_| context.boundary[v] == 1)
                else {
                    continue;
                };
                self.parent[c] = outer.last().copied();
                self.decl[c] = context.declaration[v];
                self.left[c * self.ranks + r] = Some(position);
                self.span[c] = Some(self.span[c].map_or((r, r), |(lo, hi)| (lo.min(r), hi.max(r))));
            }
        }
        self.key = (0..self.key.len())
            .map(|c| self.mean_key(c))
            .collect::<Result<_, _>>()?;
        Ok(())
    }

    fn mean_key(&self, c: usize) -> Result<(i64, i64), LayoutError> {
        let Some((lo, hi)) = self.span[c] else {
            return Ok((0, 1));
        };
        let mut sum = 0_i64;
        for r in lo..=hi {
            let position = self.at(c, r).unwrap_or(0);
            sum = sum
                .checked_add(i64::try_from(position).map_err(|_| LayoutError::Overflow)?)
                .ok_or(LayoutError::Overflow)?;
        }
        let count = i64::try_from(hi - lo + 1).map_err(|_| LayoutError::Overflow)?;
        Ok((sum, count))
    }

    fn groups(&self) -> Vec<Vec<usize>> {
        let mut by_parent = vec![Vec::new(); self.parent.len() + 1];
        for (c, parent) in self.parent.iter().enumerate() {
            by_parent[parent.map_or(0, |parent| parent + 1)].push(c);
        }
        by_parent
    }

    fn at(&self, c: usize, r: usize) -> Option<usize> {
        self.left[c * self.ranks + r]
    }

    fn votes(&self, a: usize, b: usize) -> (usize, usize) {
        let (Some((a_lo, a_hi)), Some((b_lo, b_hi))) = (self.span[a], self.span[b]) else {
            return (0, 0);
        };
        let (mut forward, mut backward) = (0, 0);
        for r in a_lo.max(b_lo)..=a_hi.min(b_hi) {
            if let (Some(pa), Some(pb)) = (self.at(a, r), self.at(b, r)) {
                if pa < pb {
                    forward += 1;
                } else {
                    backward += 1;
                }
            }
        }
        (forward, backward)
    }

    fn precedes(&self, a: usize, b: usize) -> Option<bool> {
        let (forward, backward) = self.votes(a, b);
        if forward + backward == 0 {
            return None;
        }
        Some(if forward == backward {
            self.decl[a] < self.decl[b]
        } else {
            forward > backward
        })
    }

    fn linearise(&mut self, group: &[usize]) -> Result<(), LayoutError> {
        let mut waiting = vec![0_usize; group.len()];
        let mut successors = vec![Vec::new(); group.len()];
        for i in 0..group.len() {
            for j in i + 1..group.len() {
                if let Some(first) = self.precedes(group[i], group[j]) {
                    let (from, to) = if first { (i, j) } else { (j, i) };
                    successors[from].push(to);
                    waiting[to] += 1;
                }
            }
        }
        let mut done = vec![false; group.len()];
        for number in 0..group.len() {
            let pick = self.next(group, &done, &waiting)?;
            done[pick] = true;
            self.number[group[pick]] = number;
            for &to in &successors[pick] {
                waiting[to] -= 1;
            }
        }
        Ok(())
    }

    fn next(
        &self,
        group: &[usize],
        done: &[bool],
        waiting: &[usize],
    ) -> Result<usize, LayoutError> {
        if let Some(pick) = self.smallest(group, |i| !done[i] && waiting[i] == 0)? {
            return Ok(pick);
        }
        self.smallest(group, |i| !done[i])?
            .ok_or(LayoutError::Domain)
    }

    fn smallest(
        &self,
        group: &[usize],
        eligible: impl Fn(usize) -> bool,
    ) -> Result<Option<usize>, LayoutError> {
        let mut pick: Option<usize> = None;
        for i in (0..group.len()).filter(|&i| eligible(i)) {
            pick = match pick {
                Some(best) if !self.less(group[i], group[best])? => Some(best),
                _ => Some(i),
            };
        }
        Ok(pick)
    }

    fn less(&self, a: usize, b: usize) -> Result<bool, LayoutError> {
        let ((a_sum, a_count), (b_sum, b_count)) = (self.key[a], self.key[b]);
        let left = a_sum.checked_mul(b_count).ok_or(LayoutError::Overflow)?;
        let right = b_sum.checked_mul(a_count).ok_or(LayoutError::Overflow)?;
        Ok(if left == right {
            self.decl[a] < self.decl[b]
        } else {
            left < right
        })
    }

    fn level(&self, nodes: &[usize], depth: usize) -> Vec<usize> {
        let mut items = self.items(nodes, depth);
        let slots: Vec<usize> = items
            .iter()
            .enumerate()
            .filter(|(_, item)| item.child.is_some())
            .map(|(i, _)| i)
            .collect();
        let mut blocks: Vec<(usize, Vec<usize>)> = items
            .iter()
            .filter_map(|item| Some((item.child?, self.level(&item.nodes, depth + 1))))
            .collect();
        blocks.sort_by_key(|(child, _)| self.number[*child]);
        for (slot, (child, nodes)) in slots.into_iter().zip(blocks) {
            items[slot] = Item {
                nodes,
                child: Some(child),
            };
        }
        items.into_iter().flat_map(|item| item.nodes).collect()
    }

    fn items(&self, nodes: &[usize], depth: usize) -> Vec<Item> {
        let mut items: Vec<Item> = Vec::new();
        for &v in nodes {
            let child = self.chains[v].get(depth).copied();
            match items.last_mut() {
                Some(last) if child.is_some() && last.child == child => last.nodes.push(v),
                _ => items.push(Item {
                    nodes: vec![v],
                    child,
                }),
            }
        }
        items
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Fixture {
        paths: Vec<Vec<usize>>,
        boundary: Vec<i8>,
        declaration: Vec<i32>,
    }

    impl Fixture {
        fn node(&mut self, path: &[usize], boundary: i8, decl: i32) -> usize {
            self.paths.push(path.to_vec());
            self.boundary.push(boundary);
            self.declaration.push(decl);
            self.paths.len() - 1
        }

        fn block(&mut self, path: &[usize], decl: i32) -> Vec<usize> {
            vec![self.node(path, 1, decl), self.node(path, 2, decl)]
        }

        fn normalise(&self, layers: &mut [Vec<usize>]) {
            let context = Context {
                paths: &self.paths,
                boundary: &self.boundary,
                declaration: &self.declaration,
            };
            normalise(&context, layers).unwrap();
        }
    }

    fn ranks(fixture: &mut Fixture, path: &[usize], decl: i32, count: usize) -> Vec<Vec<usize>> {
        (0..count).map(|_| fixture.block(path, decl)).collect()
    }

    fn rank(parts: &[&Vec<usize>]) -> Vec<usize> {
        parts.iter().flat_map(|part| part.iter().copied()).collect()
    }

    #[test]
    fn flips_the_minority_rank() {
        let mut f = Fixture::default();
        let (a, b) = (ranks(&mut f, &[10], 0, 3), ranks(&mut f, &[11], 1, 3));
        let mut layers = vec![
            rank(&[&a[0], &b[0]]),
            rank(&[&a[1], &b[1]]),
            rank(&[&b[2], &a[2]]),
        ];
        f.normalise(&mut layers);
        for r in 0..3 {
            assert_eq!(layers[r], rank(&[&a[r], &b[r]]), "rank {r}");
        }
    }

    #[test]
    fn a_tie_goes_to_the_lower_declaration() {
        let mut f = Fixture::default();
        let (a, b) = (ranks(&mut f, &[10], 4, 2), ranks(&mut f, &[11], 2, 2));
        let mut layers = vec![rank(&[&a[0], &b[0]]), rank(&[&b[1], &a[1]])];
        f.normalise(&mut layers);
        for r in 0..2 {
            assert_eq!(layers[r], rank(&[&b[r], &a[r]]), "rank {r}");
        }
    }

    #[test]
    fn loose_nodes_keep_their_places() {
        let mut f = Fixture::default();
        let (a, b) = (ranks(&mut f, &[10], 0, 3), ranks(&mut f, &[11], 1, 3));
        let loose = f.node(&[], 0, 7);
        let mut layers = vec![
            rank(&[&a[0], &b[0]]),
            rank(&[&a[1], &b[1]]),
            rank(&[&b[2], &vec![loose], &a[2]]),
        ];
        f.normalise(&mut layers);
        assert_eq!(layers[2], rank(&[&a[2], &vec![loose], &b[2]]));
    }

    #[test]
    fn recurses_into_parent_blocks() {
        let mut f = Fixture::default();
        let outer = ranks(&mut f, &[10], 0, 3);
        let q = ranks(&mut f, &[10, 11], 1, 3);
        let r = ranks(&mut f, &[10, 12], 2, 3);
        let inside = |rank_index: usize, first: &Vec<usize>, second: &Vec<usize>| {
            let o = &outer[rank_index];
            rank(&[&vec![o[0]], first, second, &vec![o[1]]])
        };
        let mut layers = vec![
            inside(0, &q[0], &r[0]),
            inside(1, &q[1], &r[1]),
            inside(2, &r[2], &q[2]),
        ];
        f.normalise(&mut layers);
        for k in 0..3 {
            assert_eq!(layers[k], inside(k, &q[k], &r[k]), "rank {k}");
        }
    }

    #[test]
    fn a_cycle_takes_the_smallest_key() {
        let mut f = Fixture::default();
        let a = ranks(&mut f, &[10], 0, 3);
        let b = ranks(&mut f, &[11], 1, 3);
        let c = ranks(&mut f, &[12], 2, 3);
        let mut layers = vec![
            rank(&[&a[0], &b[0], &c[0]]),
            rank(&[&b[1], &c[1], &a[1]]),
            rank(&[&c[2], &a[2], &b[2]]),
        ];
        f.normalise(&mut layers);
        for r in 0..3 {
            assert_eq!(layers[r], rank(&[&a[r], &b[r], &c[r]]), "rank {r}");
        }
    }

    #[test]
    fn a_cycle_key_outranks_the_declaration() {
        let mut f = Fixture::default();
        let a = ranks(&mut f, &[10], 5, 3);
        let b = ranks(&mut f, &[11], 1, 3);
        let c = ranks(&mut f, &[12], 0, 3);
        let loose = f.node(&[], 0, 9);
        let mut layers = vec![
            rank(&[&a[0], &vec![loose], &b[0], &c[0]]),
            rank(&[&b[1], &c[1], &a[1]]),
            rank(&[&c[2], &a[2], &b[2]]),
        ];
        f.normalise(&mut layers);
        assert_eq!(layers[0], rank(&[&a[0], &vec![loose], &b[0], &c[0]]));
        assert_eq!(layers[1], rank(&[&a[1], &b[1], &c[1]]));
        assert_eq!(layers[2], rank(&[&a[2], &b[2], &c[2]]));
    }

    #[test]
    fn a_consistent_order_is_untouched() {
        let mut f = Fixture::default();
        let (a, b) = (ranks(&mut f, &[10], 5, 2), ranks(&mut f, &[11], 1, 2));
        let mut layers = vec![rank(&[&a[0], &b[0]]), rank(&[&a[1], &b[1]])];
        let before = layers.clone();
        f.normalise(&mut layers);
        assert_eq!(layers, before);
    }

    #[test]
    fn nodes_outside_clusters_are_untouched() {
        let mut f = Fixture::default();
        let nodes = [f.node(&[], 0, 0), f.node(&[], 0, 1)];
        let mut layers = vec![vec![nodes[1], nodes[0]]];
        f.normalise(&mut layers);
        assert_eq!(layers, vec![vec![nodes[1], nodes[0]]]);
    }
}
