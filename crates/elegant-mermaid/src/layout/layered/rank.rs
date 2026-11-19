use super::{LayoutError, graph::Graph};

#[derive(Debug, PartialEq, Eq)]
pub struct Ranking {
    pub ranks: Vec<i32>,
    pub budget_exhausted: bool,
}

pub fn components(g: &Graph) -> Result<Vec<Vec<usize>>, LayoutError> {
    g.validate()?;
    let incident = g.incident_edges();
    let mut seen = vec![false; g.nodes.len()];
    let mut result = Vec::new();
    for root in 0..g.nodes.len() {
        if seen[root] {
            continue;
        }
        let mut members = vec![root];
        seen[root] = true;
        let mut cursor = 0;
        while cursor < members.len() {
            let node = members[cursor];
            cursor += 1;
            for index in &incident[node] {
                let e = g.edges[*index];
                let next = if e.tail == node { e.head } else { e.tail };
                if !seen[next] {
                    seen[next] = true;
                    members.push(next);
                }
            }
        }
        members.sort_by_key(|i| (g.nodes[*i].decl, *i));
        result.push(members);
    }
    Ok(result)
}

fn longest_path(g: &Graph) -> Result<Vec<i64>, LayoutError> {
    let mut ranks = vec![0_i64; g.nodes.len()];
    let mut degree = vec![0; g.nodes.len()];
    let mut out = vec![Vec::new(); g.nodes.len()];
    for (i, e) in g.edges.iter().enumerate().filter(|(_, e)| !e.self_loop()) {
        let (a, b) = e.chain();
        degree[b] += 1;
        out[a].push(i);
    }
    let mut done = vec![false; g.nodes.len()];
    for _ in &g.nodes {
        let node = (0..g.nodes.len())
            .find(|i| !done[*i] && degree[*i] == 0)
            .ok_or(LayoutError::Domain)?;
        done[node] = true;
        for i in &out[node] {
            let e = g.edges[*i];
            let (_, b) = e.chain();
            ranks[b] = ranks[b].max(
                ranks[node]
                    .checked_add(i64::from(e.min_len))
                    .ok_or(LayoutError::Overflow)?,
            );
            degree[b] -= 1;
        }
    }
    Ok(ranks)
}

fn slack(g: &Graph, ranks: &[i64], index: usize) -> i64 {
    let e = g.edges[index];
    let (a, b) = e.chain();
    ranks[b] - ranks[a] - i64::from(e.min_len)
}

fn shift(ranks: &mut [i64], members: &[bool], delta: i64) -> Result<(), LayoutError> {
    for (r, inside) in ranks.iter_mut().zip(members) {
        if *inside {
            *r = r.checked_add(delta).ok_or(LayoutError::Overflow)?;
        }
    }
    Ok(())
}

fn tight_tree(g: &Graph, ranks: &mut [i64], members: &[usize]) -> Result<Vec<bool>, LayoutError> {
    let mut tree = vec![false; g.edges.len()];
    let mut inside = vec![false; g.nodes.len()];
    inside[members[0]] = true;
    let incident = g.incident_edges();
    for _ in 1..members.len() {
        let crossing = crossing_edges(g, &inside);
        let tight = members
            .iter()
            .filter(|v| inside[**v])
            .flat_map(|v| incident[*v].iter().copied())
            .find(|i| crossing.contains(i) && slack(g, ranks, *i) == 0);
        let index = match tight {
            Some(i) => i,
            None => {
                let i = crossing
                    .into_iter()
                    .min_by_key(|i| (slack(g, ranks, *i), g.edges[*i].decl, *i))
                    .ok_or(LayoutError::Domain)?;
                let (a, _) = g.edges[i].chain();
                let delta = if inside[a] {
                    slack(g, ranks, i)
                } else {
                    -slack(g, ranks, i)
                };
                shift(ranks, &inside, delta)?;
                members
                    .iter()
                    .filter(|v| inside[**v])
                    .flat_map(|v| incident[*v].iter().copied())
                    .find(|i| {
                        let e = g.edges[*i];
                        inside[e.tail] != inside[e.head] && slack(g, ranks, *i) == 0
                    })
                    .ok_or(LayoutError::Domain)?
            }
        };
        tree[index] = true;
        let (a, b) = g.edges[index].chain();
        inside[a] = true;
        inside[b] = true;
    }
    Ok(tree)
}

fn crossing_edges(g: &Graph, inside: &[bool]) -> Vec<usize> {
    g.edges
        .iter()
        .enumerate()
        .filter(|(_, e)| inside[e.tail] != inside[e.head])
        .map(|(i, _)| i)
        .collect()
}

fn tail_partition(g: &Graph, tree: &[bool], removed: usize) -> Vec<bool> {
    let mut inside = vec![false; g.nodes.len()];
    let (tail, _) = g.edges[removed].chain();
    inside[tail] = true;
    let mut stack = vec![tail];
    let incident = g.incident_edges();
    while let Some(v) = stack.pop() {
        for i in incident[v]
            .iter()
            .copied()
            .filter(|i| tree[*i] && *i != removed)
        {
            let e = g.edges[i];
            let next = if e.tail == v { e.head } else { e.tail };
            if !inside[next] {
                inside[next] = true;
                stack.push(next);
            }
        }
    }
    inside
}

fn leaving(g: &Graph, tree: &[bool]) -> Option<(usize, Vec<bool>)> {
    for (i, _) in g.edges.iter().enumerate().filter(|(i, _)| tree[*i]) {
        let inside = tail_partition(g, tree, i);
        let cut: i64 = g
            .edges
            .iter()
            .filter(|e| inside[e.tail] != inside[e.head])
            .map(|e| {
                let (a, _) = e.chain();
                if inside[a] { 1 } else { -1 }
            })
            .sum();
        if cut < 0 {
            return Some((i, inside));
        }
    }
    None
}

fn optimize(
    g: &Graph,
    ranks: &mut [i64],
    members: &[usize],
    cap: usize,
) -> Result<bool, LayoutError> {
    let mut tree = tight_tree(g, ranks, members)?;
    for _ in 0..cap {
        let Some((leave, inside)) = leaving(g, &tree) else {
            return Ok(false);
        };
        let enter = g
            .edges
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                let (a, b) = e.chain();
                !inside[a] && inside[b]
            })
            .min_by_key(|(i, e)| (slack(g, ranks, *i), e.decl, *i))
            .map(|(i, _)| i)
            .ok_or(LayoutError::Domain)?;
        shift(ranks, &inside, -slack(g, ranks, enter))?;
        tree[leave] = false;
        tree[enter] = true;
    }
    Ok(true)
}

pub fn rank(g: &Graph) -> Result<Ranking, LayoutError> {
    g.validate()?;
    let mut ranks = longest_path(g)?;
    let factor = crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|c| c.name == "vector.pivot_factor")
        .ok_or(LayoutError::Domain)?
        .value;
    let cap = usize::try_from(factor)
        .map_err(|_| LayoutError::Domain)?
        .checked_mul(g.nodes.len())
        .ok_or(LayoutError::Overflow)?;
    let mut budget_exhausted = false;
    for members in components(g)? {
        budget_exhausted |= optimize(g, &mut ranks, &members, cap)?;
        let min = members.iter().map(|i| ranks[*i]).min().unwrap_or(0);
        for i in members {
            ranks[i] -= min;
        }
    }
    let ranks = ranks
        .into_iter()
        .map(|r| i32::try_from(r).map_err(|_| LayoutError::Overflow))
        .collect::<Result<_, _>>()?;
    Ok(Ranking {
        ranks,
        budget_exhausted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::layered::graph::{Edge, Node, Params};
    fn random(case: usize) -> Graph {
        let mut s = u32::try_from(case + 1).unwrap_or(1);
        let mut draw = |lo: usize, hi: usize| {
            s ^= s << 13;
            s ^= s >> 17;
            s ^= s << 5;
            lo + usize::try_from(s).unwrap_or(0) % (hi - lo + 1)
        };
        let n = draw(2, 30);
        for _ in 0..n {
            draw(0, 15);
        }
        let count = draw(1, n);
        let edges = (0..count)
            .map(|i| {
                let tail = draw(0, n - 2);
                let head = draw(tail + 1, n - 1);
                Edge {
                    tail,
                    head,
                    min_len: 1,
                    decl: i32::try_from(i).unwrap_or(0),
                    reversed: false,
                }
            })
            .collect();
        Graph {
            nodes: (0..n)
                .map(|i| Node {
                    decl: i32::try_from(i).unwrap_or(0),
                    ..Node::default()
                })
                .collect(),
            edges,
            params: Params {
                slot: 768,
                pivot_factor: 50,
                node_gap: 1536,
                cluster_pad: 1024,
                rank_gap: 3072,
                port_gap: 512,
            },
        }
    }
    fn brute(g: &Graph, values: &mut [i32], cursor: usize, best: &mut i64) {
        if cursor == values.len() {
            if g.edges
                .iter()
                .all(|e| values[e.head] - values[e.tail] >= e.min_len)
            {
                *best = (*best).min(
                    g.edges
                        .iter()
                        .map(|e| i64::from(values[e.head] - values[e.tail]))
                        .sum(),
                );
            }
            return;
        }
        for v in 0..=2 * (values.len() - 1) {
            values[cursor] = i32::try_from(v).unwrap_or(0);
            brute(g, values, cursor + 1, best);
        }
    }
    #[test]
    fn layered_rank_matches_exhaustive_oracle() -> Result<(), LayoutError> {
        let mut count = 0;
        for case in 0..2000 {
            let g = random(case);
            if g.nodes.len() > 5 {
                continue;
            }
            let result = rank(&g)?;
            assert_eq!(result.ranks.iter().min(), Some(&0));
            assert!(
                g.edges
                    .iter()
                    .all(|e| result.ranks[e.head] - result.ranks[e.tail] >= e.min_len),
                "layered_rank_matches_exhaustive_oracle: input violates g.edges .iter() .all(|e| result.ranks[e.head] - result.ranks[e.tail] >= e.min_len); observed {:?}",
                result.ranks
            );
            let mut best = i64::MAX;
            brute(&g, &mut vec![0; g.nodes.len()], 0, &mut best);
            let cost: i64 = g
                .edges
                .iter()
                .map(|e| i64::from(result.ranks[e.head] - result.ranks[e.tail]))
                .sum();
            if !result.budget_exhausted {
                assert_eq!(cost, best, "case {case}");
            }
            count += 1;
            if count == 100 {
                break;
            }
        }
        assert_eq!(count, 100);
        Ok(())
    }
    #[test]
    fn layered_rank_vectors() -> Result<(), LayoutError> {
        for case in 0..10 {
            println!("{case}: {:?}", rank(&random(case))?.ranks);
        }
        Ok(())
    }
    #[test]
    fn layered_rank_min_lengths_and_overflow() -> Result<(), LayoutError> {
        let mut g = Graph {
            nodes: (0..3)
                .map(|decl| Node {
                    decl,
                    ..Node::default()
                })
                .collect(),
            edges: vec![
                Edge {
                    tail: 0,
                    head: 1,
                    min_len: 2,
                    decl: 0,
                    reversed: false,
                },
                Edge {
                    tail: 1,
                    head: 2,
                    min_len: 3,
                    decl: 1,
                    reversed: false,
                },
            ],
            params: Params::for_profile("vector")?,
        };
        assert_eq!(rank(&g)?.ranks, vec![0, 2, 5]);
        g.edges[0].min_len = i32::MAX;
        assert_eq!(rank(&g), Err(LayoutError::Overflow));
        Ok(())
    }
}
