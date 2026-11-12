use super::{LayoutError, graph::Graph};

pub fn break_cycles(g: &Graph) -> Result<Vec<bool>, LayoutError> {
    g.validate()?;
    if g.edges.iter().any(|edge| edge.decl == i32::MAX) {
        return protected_cycles(g);
    }
    let out = g.declared_out();
    let mut state = vec![0; g.nodes.len()];
    let mut reversed = vec![false; g.edges.len()];
    for root in 0..g.nodes.len() {
        if state[root] != 0 {
            continue;
        }
        state[root] = 1;
        let mut stack = vec![(root, 0)];
        while let Some((node, cursor)) = stack.last_mut() {
            if *cursor == out[*node].len() {
                state[*node] = 2;
                stack.pop();
                continue;
            }
            let index = out[*node][*cursor];
            *cursor += 1;
            let edge = g.edges[index];
            if edge.self_loop() {
                continue;
            }
            match state[edge.head] {
                1 => reversed[index] = true,
                0 => {
                    state[edge.head] = 1;
                    stack.push((edge.head, 0));
                }
                _ => {}
            }
        }
    }
    Ok(reversed)
}

fn protected_cycles(g: &Graph) -> Result<Vec<bool>, LayoutError> {
    let mut out = vec![Vec::new(); g.nodes.len()];
    let mut reversed = vec![false; g.edges.len()];
    for edge in g
        .edges
        .iter()
        .filter(|edge| edge.decl == i32::MAX && !edge.self_loop())
    {
        if reachable(&out, edge.head, edge.tail) {
            return Err(LayoutError::Domain);
        }
        out[edge.tail].push(edge.head);
    }
    for (index, edge) in g
        .edges
        .iter()
        .enumerate()
        .filter(|(_, edge)| edge.decl != i32::MAX && !edge.self_loop())
    {
        let (tail, head) = edge.chain();
        let flip = reachable(&out, head, tail);
        reversed[index] = edge.reversed != flip;
        if flip {
            out[head].push(tail);
        } else {
            out[tail].push(head);
        }
    }
    Ok(reversed)
}

fn reachable(out: &[Vec<usize>], start: usize, target: usize) -> bool {
    let mut seen = vec![false; out.len()];
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == target {
            return true;
        }
        if seen[node] {
            continue;
        }
        seen[node] = true;
        stack.extend(out[node].iter().copied().filter(|&next| !seen[next]));
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::layered::graph::{Edge, Node, Params};
    #[test]
    fn layered_cycles_chain_and_back_edge() -> Result<(), LayoutError> {
        let mut g = Graph {
            nodes: (0..2000)
                .map(|decl| Node {
                    decl,
                    ..Node::default()
                })
                .collect(),
            edges: Vec::new(),
            params: Params::for_profile("vector")?,
        };
        for i in 0..1999 {
            g.edges.push(Edge {
                tail: i,
                head: i + 1,
                min_len: 1,
                decl: i32::try_from(i).map_err(|_| LayoutError::Overflow)?,
                reversed: false,
            });
        }
        assert!(break_cycles(&g)?.iter().all(|v| !v));
        g.edges.push(Edge {
            tail: 1999,
            head: 0,
            min_len: 1,
            decl: 1999,
            reversed: false,
        });
        let reversed = break_cycles(&g)?;
        assert_eq!(reversed.iter().filter(|v| **v).count(), 1);
        let mut degree = vec![0; 2000];
        let mut out = vec![Vec::new(); 2000];
        for (e, flip) in g.edges.iter().zip(reversed) {
            let (a, b) = if flip {
                (e.head, e.tail)
            } else {
                (e.tail, e.head)
            };
            degree[b] += 1;
            out[a].push(b);
        }
        let mut ready: Vec<_> = (0..2000).filter(|i| degree[*i] == 0).collect();
        let mut seen = 0;
        while let Some(a) = ready.pop() {
            seen += 1;
            for b in &out[a] {
                degree[*b] -= 1;
                if degree[*b] == 0 {
                    ready.push(*b);
                }
            }
        }
        assert_eq!(seen, 2000);
        Ok(())
    }
    #[test]
    fn layered_cycles_preserve_declared_multiset_and_set_aside_loops() -> Result<(), LayoutError> {
        let g = Graph {
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
                    min_len: 1,
                    decl: 0,
                    reversed: false,
                },
                Edge {
                    tail: 1,
                    head: 2,
                    min_len: 1,
                    decl: 1,
                    reversed: false,
                },
                Edge {
                    tail: 2,
                    head: 0,
                    min_len: 1,
                    decl: 2,
                    reversed: false,
                },
                Edge {
                    tail: 1,
                    head: 1,
                    min_len: 1,
                    decl: 3,
                    reversed: false,
                },
            ],
            params: Params::for_profile("vector")?,
        };
        let snapshot = g.clone();
        let reversed = break_cycles(&g)?;
        assert_eq!(g, snapshot);
        assert_eq!(reversed, vec![false, false, true, false]);
        let before: Vec<_> = g
            .edges
            .iter()
            .map(|e| (e.tail.min(e.head), e.tail.max(e.head), e.decl))
            .collect();
        let after: Vec<_> = g
            .edges
            .iter()
            .zip(reversed)
            .map(|(e, flip)| {
                let (a, b) = if flip {
                    (e.head, e.tail)
                } else {
                    (e.tail, e.head)
                };
                (a.min(b), a.max(b), e.decl)
            })
            .collect();
        assert_eq!(before, after);
        Ok(())
    }
}
