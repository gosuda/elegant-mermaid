use crate::geom::GeomError;
use crate::model::sankey::{Model, ValueKind};

const Q: i64 = 65536;

#[derive(Clone, Copy)]
enum Pass {
    Forward,
    Backward,
}

impl Pass {
    fn adjacent(self, node: &Node) -> &[usize] {
        match self {
            Self::Forward => &node.out,
            Self::Backward => &node.incoming,
        }
    }
    fn far(self, link: &Link) -> usize {
        match self {
            Self::Forward => link.target,
            Self::Backward => link.source,
        }
    }
}

#[derive(Default)]
pub(super) struct Node {
    pub value: i64,
    pub depth: usize,
    pub layer: usize,
    pub y0: i64,
    pub y1: i64,
    out: Vec<usize>,
    incoming: Vec<usize>,
}

pub(super) struct Link {
    pub source: usize,
    pub target: usize,
    value: i64,
    pub width: i64,
    pub y0: i64,
    pub y1: i64,
}

pub(super) struct Flow {
    pub nodes: Vec<Node>,
    pub links: Vec<Link>,
    columns: Vec<Vec<usize>>,
    extent: i64,
    padding: i64,
    py: i64,
    iterations: u32,
}

fn add(a: i64, b: i64) -> Result<i64, GeomError> {
    a.checked_add(b).ok_or(GeomError::Overflow)
}
fn mul(a: i64, b: i64) -> Result<i64, GeomError> {
    a.checked_mul(b).ok_or(GeomError::Overflow)
}
fn round(n: i64, d: i64) -> Result<i64, GeomError> {
    Ok(add(mul(2, n)?, d)?.div_euclid(mul(2, d)?))
}

impl Flow {
    pub fn new(
        model: &Model,
        extent: i64,
        padding: i64,
        iterations: u32,
    ) -> Result<Self, GeomError> {
        let mut nodes: Vec<Node> = (0..model.nodes.len()).map(|_| Node::default()).collect();
        let mut links = Vec::with_capacity(model.links.len());
        for (i, link) in model.links.iter().enumerate() {
            match link.value.kind {
                ValueKind::Overflow => return Err(GeomError::Overflow),
                ValueKind::NonFinite => return Err(GeomError::Domain),
                ValueKind::Finite => {}
            }
            if link.value.thousandths < 0
                || link.source >= nodes.len()
                || link.target >= nodes.len()
            {
                return Err(GeomError::Domain);
            }
            nodes[link.source].out.push(i);
            nodes[link.target].incoming.push(i);
            links.push(Link {
                source: link.source,
                target: link.target,
                value: link.value.thousandths,
                width: 0,
                y0: 0,
                y1: 0,
            });
        }
        for node in &mut nodes {
            let outgoing = node
                .out
                .iter()
                .try_fold(0, |sum, &i| add(sum, links[i].value))?;
            let incoming = node
                .incoming
                .iter()
                .try_fold(0, |sum, &i| add(sum, links[i].value))?;
            node.value = outgoing.max(incoming);
        }
        Ok(Self {
            nodes,
            links,
            columns: Vec::new(),
            extent,
            padding,
            py: 0,
            iterations,
        })
    }

    fn levels(&self, pass: Pass) -> Result<Vec<usize>, GeomError> {
        let mut levels = vec![0; self.nodes.len()];
        let mut current: Vec<usize> = (0..self.nodes.len()).collect();
        let mut marked = vec![false; self.nodes.len()];
        let mut level = 0;
        while !current.is_empty() {
            for &node in &current {
                levels[node] = level;
                let adjacent = pass.adjacent(&self.nodes[node]);
                for &li in adjacent {
                    let link = &self.links[li];
                    marked[pass.far(link)] = true;
                }
            }
            level += 1;
            if level > self.nodes.len() {
                return Err(GeomError::Domain);
            }
            current.clear();
            current.extend(marked.iter_mut().enumerate().filter_map(|(i, found)| {
                if *found {
                    *found = false;
                    Some(i)
                } else {
                    None
                }
            }));
        }
        Ok(levels)
    }

    fn place(&mut self, alignment: &str) -> Result<(), GeomError> {
        let depths = self.levels(Pass::Forward)?;
        let heights = self.levels(Pass::Backward)?;
        let count = depths.iter().copied().max().map_or(1, |depth| depth + 1);
        self.columns = vec![Vec::new(); count];
        for i in 0..self.nodes.len() {
            let node = &self.nodes[i];
            let layer = match alignment {
                "left" => depths[i],
                "right" => count - 1 - heights[i],
                "center" if !node.incoming.is_empty() => depths[i],
                "center" => node
                    .out
                    .iter()
                    .map(|&li| depths[self.links[li].target])
                    .min()
                    .map_or(0, |depth| depth.saturating_sub(1)),
                _ if !node.out.is_empty() => depths[i],
                _ => count - 1,
            }
            .min(count - 1);
            let node = &mut self.nodes[i];
            node.depth = depths[i];
            node.layer = layer;
            self.columns[layer].push(i);
        }
        Ok(())
    }

    fn initialise(&mut self) -> Result<(), GeomError> {
        let widest = self.columns.iter().map(Vec::len).max().unwrap_or(0);
        self.py = if widest > 1 {
            self.padding.min(
                self.extent
                    .div_euclid(i64::try_from(widest - 1).map_err(|_| GeomError::Overflow)?),
            )
        } else {
            self.padding
        };
        let mut ky = None;
        for column in &self.columns {
            if column.is_empty() {
                continue;
            }
            let gaps = i64::try_from(column.len() - 1).map_err(|_| GeomError::Overflow)?;
            let room = self.extent - mul(gaps, self.py)?;
            if room < 0 {
                return Err(GeomError::Domain);
            }
            let sum = column
                .iter()
                .try_fold(0, |sum, &i| add(sum, self.nodes[i].value))?;
            if sum > 0 {
                let candidate = mul(room, Q)?.div_euclid(sum);
                ky = Some(ky.map_or(candidate, |old: i64| old.min(candidate)));
            }
        }
        let ky = ky.unwrap_or(0);
        for c in 0..self.columns.len() {
            let mut y = 0;
            for &ni in &self.columns[c] {
                let node = &mut self.nodes[ni];
                node.y0 = y;
                node.y1 = add(y, mul(node.value, ky)?.div_euclid(Q))?;
                y = add(node.y1, self.py)?;
                for &li in &node.out {
                    self.links[li].width = mul(self.links[li].value, ky)?.div_euclid(Q);
                }
            }
            let count = i64::try_from(self.columns[c].len()).map_err(|_| GeomError::Overflow)?;
            let free = self.extent - (y - self.py);
            for (k, &ni) in self.columns[c].iter().enumerate() {
                let shift = mul(i64::try_from(k + 1).map_err(|_| GeomError::Overflow)?, free)?
                    .div_euclid(count + 1);
                self.nodes[ni].y0 = add(self.nodes[ni].y0, shift)?;
                self.nodes[ni].y1 = add(self.nodes[ni].y1, shift)?;
            }
            for k in 0..self.columns[c].len() {
                self.sort_links(self.columns[c][k]);
            }
        }
        Ok(())
    }

    fn sort_links(&mut self, ni: usize) {
        let mut outgoing = std::mem::take(&mut self.nodes[ni].out);
        let mut incoming = std::mem::take(&mut self.nodes[ni].incoming);
        let nodes = &self.nodes;
        let links = &self.links;
        outgoing.sort_by_key(|&li| (nodes[links[li].target].y0, li));
        incoming.sort_by_key(|&li| (nodes[links[li].source].y0, li));
        self.nodes[ni].out = outgoing;
        self.nodes[ni].incoming = incoming;
    }

    fn reorder_node_links(&mut self, ni: usize) {
        for k in 0..self.nodes[ni].incoming.len() {
            let source = self.links[self.nodes[ni].incoming[k]].source;
            let mut outgoing = std::mem::take(&mut self.nodes[source].out);
            let nodes = &self.nodes;
            let links = &self.links;
            outgoing.sort_by_key(|&li| (nodes[links[li].target].y0, li));
            self.nodes[source].out = outgoing;
        }
        for k in 0..self.nodes[ni].out.len() {
            let target = self.links[self.nodes[ni].out[k]].target;
            let mut incoming = std::mem::take(&mut self.nodes[target].incoming);
            let nodes = &self.nodes;
            let links = &self.links;
            incoming.sort_by_key(|&li| (nodes[links[li].source].y0, li));
            self.nodes[target].incoming = incoming;
        }
    }

    fn top(&self, source: usize, target: usize, pass: Pass) -> Result<i64, GeomError> {
        let (node, list, other) = match pass {
            Pass::Backward => (
                &self.nodes[target],
                &self.nodes[target].incoming,
                &self.nodes[source].out,
            ),
            Pass::Forward => (
                &self.nodes[source],
                &self.nodes[source].out,
                &self.nodes[target].incoming,
            ),
        };
        let mut a = 0;
        for &li in list {
            let link = &self.links[li];
            if pass.far(link)
                == match pass {
                    Pass::Backward => source,
                    Pass::Forward => target,
                }
            {
                break;
            }
            a = add(a, add(link.width, self.py)?)?;
        }
        let mut b = 0;
        for &li in other {
            let link = &self.links[li];
            if match pass {
                Pass::Backward => link.target == target,
                Pass::Forward => link.source == source,
            } {
                break;
            }
            b = add(b, link.width)?;
        }
        let gaps = i64::try_from(list.len()).map_err(|_| GeomError::Overflow)? - 1;
        let n = add(mul(2, node.y0)?, -mul(gaps, self.py)?)?;
        Ok(add(n, add(mul(2, a)?, -mul(2, b)?)?)?.div_euclid(2))
    }

    fn pull(&mut self, ni: usize, alpha: i64, pass: Pass) -> Result<(), GeomError> {
        let list = match pass {
            Pass::Backward => &self.nodes[ni].out,
            Pass::Forward => &self.nodes[ni].incoming,
        };
        let mut y = 0;
        let mut weight = 0;
        for &li in list {
            let link = &self.links[li];
            let distance = self.nodes[link.target].layer - self.nodes[link.source].layer;
            let value = mul(
                link.value,
                i64::try_from(distance).map_err(|_| GeomError::Overflow)?,
            )?;
            y = add(y, mul(self.top(link.source, link.target, pass)?, value)?)?;
            weight = add(weight, value)?;
        }
        if weight <= 0 {
            return Ok(());
        }
        let dy = round(mul(round(y, weight)? - self.nodes[ni].y0, alpha)?, Q)?;
        self.nodes[ni].y0 = add(self.nodes[ni].y0, dy)?;
        self.nodes[ni].y1 = add(self.nodes[ni].y1, dy)?;
        self.reorder_node_links(ni);
        Ok(())
    }

    fn push_down(
        &mut self,
        column: &[usize],
        mut y: i64,
        from: usize,
        beta: i64,
    ) -> Result<(), GeomError> {
        for &ni in &column[from..] {
            let node = &mut self.nodes[ni];
            let dy = round(mul(y - node.y0, beta)?, Q)?;
            if dy > 0 {
                node.y0 = add(node.y0, dy)?;
                node.y1 = add(node.y1, dy)?;
            }
            y = add(node.y1, self.py)?;
        }
        Ok(())
    }

    fn push_up(
        &mut self,
        column: &[usize],
        mut y: i64,
        count: usize,
        beta: i64,
    ) -> Result<(), GeomError> {
        for &ni in column[..count].iter().rev() {
            let node = &mut self.nodes[ni];
            let dy = round(mul(node.y1 - y, beta)?, Q)?;
            if dy > 0 {
                node.y0 = add(node.y0, -dy)?;
                node.y1 = add(node.y1, -dy)?;
            }
            y = add(node.y0, -self.py)?;
        }
        Ok(())
    }

    fn settle(&mut self, c: usize, beta: i64) -> Result<(), GeomError> {
        let mut column = std::mem::take(&mut self.columns[c]);
        column.sort_by_key(|&ni| self.nodes[ni].y0);
        if !column.is_empty() {
            let k = column.len() / 2;
            let y0 = self.nodes[column[k]].y0;
            let y1 = self.nodes[column[k]].y1;
            self.push_up(&column, y0 - self.py, k, beta)?;
            self.push_down(&column, y1 + self.py, k + 1, beta)?;
            self.push_up(&column, self.extent, column.len(), beta)?;
            self.push_down(&column, 0, 0, beta)?;
        }
        self.columns[c] = column;
        Ok(())
    }

    pub fn run(&mut self, alignment: &str) -> Result<(), GeomError> {
        self.place(alignment)?;
        self.initialise()?;
        for i in 0..self.iterations {
            let alpha = mul(Q, 99_i64.checked_pow(i).ok_or(GeomError::Overflow)?)?
                .div_euclid(100_i64.checked_pow(i).ok_or(GeomError::Overflow)?);
            let beta =
                (Q - alpha).max((i64::from(i + 1) * Q).div_euclid(i64::from(self.iterations)));
            for c in (0..self.columns.len().saturating_sub(1)).rev() {
                for k in 0..self.columns[c].len() {
                    self.pull(self.columns[c][k], alpha, Pass::Backward)?;
                }
                self.settle(c, beta)?;
            }
            for c in 1..self.columns.len() {
                for k in 0..self.columns[c].len() {
                    self.pull(self.columns[c][k], alpha, Pass::Forward)?;
                }
                self.settle(c, beta)?;
            }
        }
        for node in &self.nodes {
            let mut y = node.y0;
            for &li in &node.out {
                self.links[li].y0 = add(y, self.links[li].width.div_euclid(2))?;
                y = add(y, self.links[li].width)?;
            }
            y = node.y0;
            for &li in &node.incoming {
                self.links[li].y1 = add(y, self.links[li].width.div_euclid(2))?;
                y = add(y, self.links[li].width)?;
            }
        }
        Ok(())
    }
}
