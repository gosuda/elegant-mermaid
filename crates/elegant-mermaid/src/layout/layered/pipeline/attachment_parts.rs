use super::*;

pub(super) struct Fragment {
    pub members: Vec<usize>,
    pub edges: Vec<usize>,
    pub layout: Component,
    pub size: Size,
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
