use super::*;

pub(super) struct Fragment {
    pub members: Vec<usize>,
    pub edges: Vec<usize>,
    pub layout: Component,
    pub size: Size,
}

pub(super) struct FrameGrowth<'a> {
    pub root: usize,
    pub amount: Size,
    pub graph: &'a Graph,
    pub input: &'a Input,
}

impl Fragment {
    pub fn grow_root(&mut self, growth: FrameGrowth<'_>) -> Result<(), LayoutError> {
        if growth.amount.w == 0 && growth.amount.h == 0 {
            return Ok(());
        }
        let root = self
            .members
            .iter()
            .position(|&member| member == growth.root)
            .ok_or(LayoutError::Domain)?;
        let frame = &mut self.layout.boxes[root];
        frame.w = narrow(i64::from(frame.w) + i64::from(growth.amount.w))?;
        frame.h = narrow(i64::from(frame.h) + i64::from(growth.amount.h))?;
        for (node, title) in &mut self.layout.titles {
            if *node == root {
                title.x = narrow(i64::from(title.x) + i64::from(growth.amount.w) / 2)?;
            }
        }
        for (&edge, route) in self.edges.iter().zip(&mut self.layout.routes) {
            let edge = &growth.graph.edges[edge];
            if edge.tail == growth.root && edge.head == growth.root {
                for point in &mut route.points {
                    point.x = narrow(i64::from(point.x) + i64::from(growth.amount.w))?;
                }
            }
        }
        self.move_root_loop_labels(&growth)?;
        self.size.w = narrow(i64::from(self.size.w) + i64::from(growth.amount.w))?;
        self.size.h = narrow(i64::from(self.size.h) + i64::from(growth.amount.h))?;
        Ok(())
    }

    fn move_root_loop_labels(&mut self, growth: &FrameGrowth<'_>) -> Result<(), LayoutError> {
        let loops: std::collections::BTreeSet<_> = growth
            .graph
            .edges
            .iter()
            .filter(|edge| edge.tail == growth.root && edge.head == growth.root)
            .filter_map(|edge| usize::try_from(edge.decl).ok())
            .filter_map(|declaration| growth.input.routes.get(declaration))
            .map(|route| route.id.as_str())
            .collect();
        for (label, rect) in &mut self.layout.labels {
            let label = growth.input.labels.get(*label).ok_or(LayoutError::Domain)?;
            if loops.contains(label.owner.as_str()) {
                rect.x = narrow(i64::from(rect.x) + i64::from(growth.amount.w))?;
            }
        }
        for (route, rect) in &mut self.layout.label_reservations {
            let route = growth.input.routes.get(*route).ok_or(LayoutError::Domain)?;
            if loops.contains(route.id.as_str()) {
                rect.x = narrow(i64::from(rect.x) + i64::from(growth.amount.w))?;
            }
        }
        Ok(())
    }
}

pub(super) struct FragmentInput<'a, 'text, 'scene> {
    pub graph: &'a Graph,
    pub input: &'a Input,
    pub measurements: &'a Measurements<'text, 'scene>,
    pub options: order::OrderOptions,
}

impl FragmentInput<'_, '_, '_> {
    pub fn build(&self, members: Vec<usize>, excluded: usize) -> Result<Fragment, LayoutError> {
        let mut graph = component(self.graph, &members);
        let reversed = cycles::break_cycles(&graph)?;
        for (edge, reversed) in graph.edges.iter_mut().zip(reversed) {
            edge.reversed = reversed;
        }
        let mut input = self.input.clone();
        input
            .attachments
            .retain(|attachment| attachment.target != excluded);
        let mut layout =
            super::attachments::layout(&graph, &input, self.measurements, self.options)?;
        let bounds = bounds(layout.packing_rects(), &layout.routes)?;
        let size = Size {
            w: narrow(i64::from(bounds.2) - i64::from(bounds.0))?,
            h: narrow(i64::from(bounds.3) - i64::from(bounds.1))?,
        };
        let offset = Point {
            x: narrow(-i64::from(bounds.0))?,
            y: narrow(-i64::from(bounds.1))?,
        };
        translate(&mut layout, offset)?;
        let edges = self
            .graph
            .edges
            .iter()
            .enumerate()
            .filter_map(|(index, edge)| {
                (members.contains(&edge.tail) && members.contains(&edge.head)).then_some(index)
            })
            .collect();
        Ok(Fragment {
            members,
            edges,
            layout,
            size,
        })
    }
}

pub(super) fn translate(layout: &mut Component, offset: Point) -> Result<(), LayoutError> {
    for rect in &mut layout.boxes {
        *rect = super::attachment_geometry::translated(*rect, offset)?;
    }
    for (_, rect) in layout
        .labels
        .iter_mut()
        .chain(&mut layout.titles)
        .chain(&mut layout.label_reservations)
    {
        *rect = super::attachment_geometry::translated(*rect, offset)?;
    }
    for rect in &mut layout.loop_extents {
        *rect = super::attachment_geometry::translated(*rect, offset)?;
    }
    for route in &mut layout.routes {
        for point in &mut route.points {
            point.x = narrow(i64::from(point.x) + i64::from(offset.x))?;
            point.y = narrow(i64::from(point.y) + i64::from(offset.y))?;
        }
    }
    Ok(())
}

pub(super) fn subtree(graph: &Graph, input: &Input, root: usize) -> Vec<usize> {
    let id = &graph.nodes[root].id;
    graph
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let inside = index == root
                || super::super::clusters::ancestors(input, &node.id)
                    .iter()
                    .any(|&ancestor| input.boxes[ancestor].id == *id);
            inside.then_some(index)
        })
        .collect()
}
