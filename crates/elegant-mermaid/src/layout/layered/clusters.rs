use super::{
    LayoutError,
    graph::{Edge, Graph, Node, Proper, ProperEdge, ProperNode},
};
use crate::{geom::Rect, layout::input::Input, scene::BoxRole};

pub struct Cluster {
    pub node: usize,
    pub bottom: usize,
    pub title: usize,
    pub left: Vec<usize>,
    pub right: Vec<usize>,
}

pub fn ancestors(input: &Input, id: &str) -> Vec<usize> {
    let mut result = Vec::new();
    let mut parent = input
        .boxes
        .iter()
        .find(|b| b.id == id)
        .map_or("", |b| b.parent.as_str());
    for _ in 0..64 {
        let Some(index) = input.boxes.iter().position(|b| b.id == parent) else {
            break;
        };
        result.push(index);
        parent = &input.boxes[index].parent;
    }
    result.reverse();
    result
}

pub fn connect(g: &mut Graph, input: &Input) {
    for child in 0..g.nodes.len() {
        let Some(parent) = input
            .boxes
            .iter()
            .find(|b| b.id == g.nodes[child].id)
            .map(|b| b.parent.as_str())
        else {
            continue;
        };
        let Some(tail) = g.nodes.iter().position(|n| n.id == parent) else {
            continue;
        };
        g.edges.push(Edge {
            tail,
            head: child,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        });
    }
}

pub fn ranking(g: &Graph, input: &Input) -> (Graph, Vec<Cluster>) {
    let mut ranked = g.clone();
    ranked.edges.retain(|edge| edge.decl != i32::MAX);
    let clusters = ranking_clusters(&mut ranked, g, input);
    redirect_cluster_edges(&mut ranked.edges, g, input, &clusters);
    for cluster in &clusters {
        let members = connect_ranked_members(&mut ranked.edges, g, input, cluster);
        let members =
            connect_ranked_clusters(&mut ranked.edges, g, input, cluster, &clusters, members);
        if members == 0 {
            ranked.edges.push(Edge {
                tail: cluster.node,
                head: cluster.bottom,
                min_len: 1,
                decl: i32::MAX,
                reversed: false,
            });
        }
    }
    (ranked, clusters)
}

fn ranking_clusters(ranked: &mut Graph, g: &Graph, input: &Input) -> Vec<Cluster> {
    let mut clusters = Vec::new();
    for (node, n) in g.nodes.iter().enumerate() {
        if !input.groups.iter().any(|group| group.id == n.id) {
            continue;
        }
        ranked.nodes[node].w = 0;
        ranked.nodes[node].h = 0;
        let bottom = ranked.nodes.len();
        ranked.nodes.push(Node {
            id: String::new(),
            decl: n.decl,
            w: 0,
            h: 0,
        });
        clusters.push(Cluster {
            node,
            bottom,
            title: usize::MAX,
            left: Vec::new(),
            right: Vec::new(),
        });
    }
    clusters
}

fn connect_ranked_members(
    edges: &mut Vec<Edge>,
    g: &Graph,
    input: &Input,
    cluster: &Cluster,
) -> i32 {
    let mut members = 0;
    for (child, other) in g.nodes.iter().enumerate() {
        if !ancestors(input, &other.id)
            .iter()
            .any(|&i| input.boxes[i].id == g.nodes[cluster.node].id)
        {
            continue;
        }
        if input
            .boxes
            .iter()
            .any(|b| b.id == other.id && b.role == BoxRole::Group)
        {
            continue;
        }
        edges.push(Edge {
            tail: cluster.node,
            head: child,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        });
        edges.push(Edge {
            tail: child,
            head: cluster.bottom,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        });
        members += 1;
    }
    members
}

fn connect_ranked_clusters(
    edges: &mut Vec<Edge>,
    g: &Graph,
    input: &Input,
    cluster: &Cluster,
    clusters: &[Cluster],
    mut members: i32,
) -> i32 {
    for child in clusters {
        if !input
            .boxes
            .iter()
            .any(|b| b.id == g.nodes[child.node].id && b.parent == g.nodes[cluster.node].id)
        {
            continue;
        }
        edges.push(Edge {
            tail: cluster.node,
            head: child.node,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        });
        edges.push(Edge {
            tail: child.bottom,
            head: cluster.bottom,
            min_len: 1,
            decl: i32::MAX,
            reversed: false,
        });
        members += 1;
    }
    members
}

fn redirect_cluster_edges(edges: &mut [Edge], g: &Graph, input: &Input, clusters: &[Cluster]) {
    for edge in edges {
        let source = edge.tail;
        let target = edge.head;
        if source == target {
            continue;
        }
        if let Some(cluster) = clusters.iter().find(|c| c.node == source) {
            let contains = ancestors(input, &g.nodes[target].id)
                .iter()
                .any(|&i| input.boxes[i].id == g.nodes[source].id);
            edge.tail = if contains {
                cluster.node
            } else {
                cluster.bottom
            };
        }
        if let Some(cluster) = clusters.iter().find(|c| c.node == target) {
            let contains = ancestors(input, &g.nodes[source].id)
                .iter()
                .any(|&i| input.boxes[i].id == g.nodes[target].id);
            edge.head = if contains {
                cluster.bottom
            } else {
                cluster.node
            };
        }
    }
}

pub struct BorderInput<'a> {
    pub graph: &'a Graph,
    pub input: &'a Input,
    pub titles: &'a [crate::geom::Size],
}

pub fn borders(
    p: &mut Proper,
    context: BorderInput<'_>,
    clusters: &mut [Cluster],
) -> Result<(Vec<Vec<usize>>, Vec<i8>), LayoutError> {
    let BorderInput {
        graph: g,
        input,
        titles,
    } = context;
    let width = super::pipeline::constant(input.profile, "cluster_border_w");
    if clusters.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    let path = |id: &str| {
        ancestors(input, id)
            .into_iter()
            .filter_map(|index| g.nodes.iter().position(|n| n.id == input.boxes[index].id))
            .collect::<Vec<_>>()
    };
    let mut borders = BorderPaths {
        paths: p.nodes.iter().map(|n| path(&n.node.id)).collect(),
        boundary: vec![0; p.nodes.len()],
    };
    for cluster in clusters {
        borders.add_cluster(
            p,
            &BorderInput {
                graph: g,
                input,
                titles,
            },
            cluster,
            width,
            &path,
        )?;
    }
    for (i, node) in p.nodes.iter().enumerate() {
        if node.edge < 0 {
            continue;
        }
        let edge = usize::try_from(node.edge).map_err(|_| LayoutError::Domain)?;
        let Some(chain) = p.chains.get(edge) else {
            continue;
        };
        let Some((&first, &last)) = chain.first().zip(chain.last()) else {
            continue;
        };
        borders.paths[i] = borders.paths[first]
            .iter()
            .zip(&borders.paths[last])
            .take_while(|(a, b)| a == b)
            .map(|(a, _)| *a)
            .collect();
    }
    p.out = vec![Vec::new(); p.nodes.len()];
    p.r#in = vec![Vec::new(); p.nodes.len()];
    for (i, e) in p.edges.iter().enumerate() {
        p.out[e.tail].push(i);
        p.r#in[e.head].push(i);
    }
    Ok((borders.paths, borders.boundary))
}

struct BorderPaths {
    paths: Vec<Vec<usize>>,
    boundary: Vec<i8>,
}

fn cluster_path(mut ancestors: Vec<usize>, node: usize) -> Vec<usize> {
    ancestors.push(node);
    ancestors
}

impl BorderPaths {
    fn add_cluster(
        &mut self,
        p: &mut Proper,
        context: &BorderInput<'_>,
        cluster: &mut Cluster,
        width: i32,
        path: &impl Fn(&str) -> Vec<usize>,
    ) -> Result<(), LayoutError> {
        let g = context.graph;
        let own = cluster_path(path(&g.nodes[cluster.node].id), cluster.node);
        self.paths[cluster.node] = own.clone();
        self.paths[cluster.bottom] = own.clone();
        self.add_title(p, context, cluster, &own)?;
        self.add_sides(p, g, cluster, width, &own);
        for side in [&cluster.left, &cluster.right] {
            for pair in side.windows(2) {
                p.edges.push(ProperEdge {
                    tail: pair[0],
                    head: pair[1],
                    decl: g.nodes[cluster.node].decl,
                    original: usize::MAX,
                });
            }
        }
        Ok(())
    }

    fn add_title(
        &mut self,
        p: &mut Proper,
        context: &BorderInput<'_>,
        cluster: &mut Cluster,
        own: &[usize],
    ) -> Result<(), LayoutError> {
        let BorderInput {
            graph: g,
            input,
            titles,
        } = context;
        p.nodes[cluster.node].edge = -4;
        p.nodes[cluster.bottom].edge = -4;
        cluster.title = p.nodes.len();
        let size = titles
            .get(usize::try_from(g.nodes[cluster.node].decl).map_err(|_| LayoutError::Domain)?)
            .ok_or(LayoutError::Domain)?;
        p.nodes.push(ProperNode {
            node: Node {
                id: String::new(),
                decl: g.nodes[cluster.node].decl,
                w: size.w,
                h: super::coords::narrow(
                    i64::from(size.h)
                        + i64::from(super::pipeline::constant(input.profile, "cluster_pad")),
                )?
                .max(if input.region_sets.is_empty() {
                    g.nodes[cluster.node].h
                } else {
                    0
                }),
            },
            dummy: false,
            label: false,
            edge: -5,
        });
        p.rank.push(p.rank[cluster.node]);
        self.paths.push(own.to_vec());
        self.boundary.push(0);
        Ok(())
    }

    fn add_sides(
        &mut self,
        p: &mut Proper,
        g: &Graph,
        cluster: &mut Cluster,
        width: i32,
        own: &[usize],
    ) {
        for rank in p.rank[cluster.node]..=p.rank[cluster.bottom] {
            let left = p.nodes.len();
            for side in [1i8, 2i8] {
                p.nodes.push(ProperNode {
                    node: Node {
                        id: String::new(),
                        decl: g.nodes[cluster.node].decl,
                        w: width,
                        h: 0,
                    },
                    dummy: false,
                    label: false,
                    edge: -i32::from(side) - 1,
                });
                p.rank.push(rank);
                self.paths.push(own.to_vec());
                self.boundary.push(side);
            }
            cluster.left.push(left);
            cluster.right.push(left + 1);
        }
    }
}

pub fn ports(clusters: &[Cluster], p: &mut Proper, x: &mut [i32]) -> Result<(), LayoutError> {
    for cluster in clusters {
        for node in [cluster.node, cluster.bottom] {
            let rank = p.rank[node];
            let left = cluster
                .left
                .iter()
                .copied()
                .find(|&v| p.rank[v] == rank)
                .ok_or(LayoutError::Domain)?;
            let right = cluster
                .right
                .iter()
                .copied()
                .find(|&v| p.rank[v] == rank)
                .ok_or(LayoutError::Domain)?;
            let lo = i64::from(x[left]) - i64::from(p.nodes[left].node.w) / 2;
            let hi = i64::from(x[right]) - i64::from(p.nodes[right].node.w) / 2
                + i64::from(p.nodes[right].node.w);
            if hi < lo {
                return Err(LayoutError::Domain);
            }
            let width = i32::try_from(hi - lo).map_err(|_| LayoutError::Overflow)?;
            p.nodes[node].node.w = width;
            x[node] =
                i32::try_from(lo + i64::from(width) / 2).map_err(|_| LayoutError::Overflow)?;
        }
    }
    Ok(())
}

pub fn anchors(
    clusters: &[Cluster],
    p: &Proper,
    layers: &[Vec<usize>],
    top: &[i32],
    y: &mut [i32],
) -> Result<(), LayoutError> {
    let heights = super::coords::heights(p, layers);
    for cluster in clusters {
        let first = usize::try_from(p.rank[cluster.node]).map_err(|_| LayoutError::Domain)?;
        let last = usize::try_from(p.rank[cluster.bottom]).map_err(|_| LayoutError::Domain)?;
        y[cluster.node] = top[first];
        y[cluster.title] = top[first];
        y[cluster.bottom] = top[last]
            .checked_add(heights[last])
            .ok_or(LayoutError::Overflow)?;
    }
    Ok(())
}

pub fn frames(
    clusters: &[Cluster],
    p: &Proper,
    x: &[i32],
    y: &[i32],
    boxes: &mut [Rect],
) -> Result<(), LayoutError> {
    for cluster in clusters {
        let left = cluster
            .left
            .iter()
            .map(|&v| i64::from(x[v]) - i64::from(p.nodes[v].node.w) / 2)
            .min()
            .ok_or(LayoutError::Domain)?;
        let right = cluster
            .right
            .iter()
            .map(|&v| {
                i64::from(x[v]) - i64::from(p.nodes[v].node.w) / 2 + i64::from(p.nodes[v].node.w)
            })
            .max()
            .ok_or(LayoutError::Domain)?;
        boxes[cluster.node] = Rect {
            x: super::coords::narrow(left)?,
            y: y[cluster.node],
            w: i32::try_from(right - left).map_err(|_| LayoutError::Overflow)?,
            h: i32::try_from(i64::from(y[cluster.bottom]) - i64::from(y[cluster.node]))
                .map_err(|_| LayoutError::Overflow)?,
        };
    }
    Ok(())
}

/// Reserves algorithmic group footprints separately from visible title nodes.
pub(super) fn reserve_footprints(
    p: &mut Proper,
    footprints: &[(usize, crate::geom::Size)],
) -> Result<(), LayoutError> {
    for &(node, size) in footprints {
        let target = p.nodes.get_mut(node).ok_or(LayoutError::Domain)?;
        if size.w < 0 || size.h < 0 {
            return Err(LayoutError::Domain);
        }
        target.node.h = target.node.h.max(size.h);
    }
    Ok(())
}

pub(super) fn reserved_ports(
    clusters: &[Cluster],
    p: &mut Proper,
    placement: &mut super::regions::Placement,
) -> Result<(), LayoutError> {
    ports(clusters, p, &mut placement.x)?;
    for (&(node, left, right), &(band_node, band_left, band_right)) in
        placement.frames.iter().zip(&placement.bands)
    {
        if node != band_node || left < band_left || right > band_right {
            return Err(LayoutError::Domain);
        }
        let width = p.nodes[node].node.w;
        let actual_left = placement.x[node]
            .checked_sub(width / 2)
            .ok_or(LayoutError::Overflow)?;
        if actual_left != left
            || actual_left
                .checked_add(width)
                .ok_or(LayoutError::Overflow)?
                != right
        {
            return Err(LayoutError::Domain);
        }
    }
    reserve_footprints(p, &placement.group_footprints)
}
