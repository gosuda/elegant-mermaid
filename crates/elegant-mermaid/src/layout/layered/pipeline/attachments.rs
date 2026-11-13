use std::collections::BTreeMap;

use super::attachment_geometry::{self as geometry, Footprint, FootprintInput, NoteSize};
use super::attachment_parts::{Fragment, FragmentInput};
use super::*;

struct Bundle {
    target: usize,
    target_part: Fragment,
    notes: Vec<(usize, Fragment)>,
    footprint: Footprint,
}

struct Contraction {
    graph: Graph,
    input: Input,
    kept: Vec<usize>,
    mapping: Vec<usize>,
    edges: Vec<usize>,
}

pub(super) fn layout(
    graph: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
    options: order::OrderOptions,
) -> Result<Component, LayoutError> {
    if input.attachments.is_empty() {
        return component_core(graph, input, measurements, options);
    }
    let fragments = FragmentInput {
        graph,
        input,
        measurements,
        options,
    };
    let bundles = bundles(&fragments)?;
    if bundles.is_empty() {
        return component_core(graph, input, measurements, options);
    }
    let contraction = contract(graph, input, &bundles)?;
    let result = component_core(
        &contraction.graph,
        &contraction.input,
        measurements,
        options,
    )?;
    Expansion {
        graph,
        input,
        contraction,
        bundles,
    }
    .expand(result)
}

fn bundles(context: &FragmentInput<'_, '_, '_>) -> Result<Vec<Bundle>, LayoutError> {
    let declarations: BTreeMap<_, _> = context
        .graph
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| (node.decl, index))
        .collect();
    let mut bundles: Vec<Bundle> = Vec::new();
    for attachment in &context.input.attachments {
        let declaration = i32::try_from(attachment.target).map_err(|_| LayoutError::Overflow)?;
        let Some(&target) = declarations.get(&declaration) else {
            continue;
        };
        if nested(context, target, &declarations)
            || bundles.iter().any(|bundle| bundle.target == target)
        {
            continue;
        }
        bundles.push(build_bundle(context, target, &declarations)?);
    }
    Ok(bundles)
}

fn build_bundle(
    context: &FragmentInput<'_, '_, '_>,
    target: usize,
    declarations: &BTreeMap<i32, usize>,
) -> Result<Bundle, LayoutError> {
    let declaration =
        usize::try_from(context.graph.nodes[target].decl).map_err(|_| LayoutError::Domain)?;
    let members = super::attachment_parts::subtree(context.graph, context.input, target);
    let target_part = context.build(members, declaration)?;
    let mut notes = Vec::new();
    let mut sizes = Vec::new();
    for attachment in context
        .input
        .attachments
        .iter()
        .filter(|item| item.target == declaration)
    {
        let note_decl = i32::try_from(attachment.note).map_err(|_| LayoutError::Overflow)?;
        let note = *declarations.get(&note_decl).ok_or(LayoutError::Domain)?;
        let fragment = context.build(vec![note], declaration)?;
        sizes.push(NoteSize {
            size: fragment.size,
            side: attachment.side,
        });
        notes.push((note, fragment));
    }
    let footprint = geometry::footprint(FootprintInput {
        target: target_part.size,
        notes: &sizes,
        direction: context.input.direction,
        gap: narrow(2 * i64::from(context.graph.params.slot) + 2)?,
    })?;
    Ok(Bundle {
        target,
        target_part,
        notes,
        footprint,
    })
}

fn nested(
    context: &FragmentInput<'_, '_, '_>,
    target: usize,
    declarations: &BTreeMap<i32, usize>,
) -> bool {
    let ancestors =
        super::super::clusters::ancestors(context.input, &context.graph.nodes[target].id);
    context.input.attachments.iter().any(|attachment| {
        let Ok(declaration) = i32::try_from(attachment.target) else {
            return false;
        };
        declarations.contains_key(&declaration) && ancestors.contains(&attachment.target)
    })
}

fn contract(graph: &Graph, input: &Input, bundles: &[Bundle]) -> Result<Contraction, LayoutError> {
    let mut projected = input.clone();
    projected
        .sizes
        .resize(input.boxes.len(), SizeRule::Measured);
    let mut representative: Vec<_> = (0..graph.nodes.len()).collect();
    for bundle in bundles {
        let members = bundle
            .target_part
            .members
            .iter()
            .copied()
            .chain(bundle.notes.iter().map(|(index, _)| *index));
        for member in members {
            representative[member] = bundle.target;
            let id = &graph.nodes[member].id;
            projected.groups.retain(|group| group.id != *id);
        }
        let node = &graph.nodes[bundle.target];
        let declaration = usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?;
        let mut size = bundle.footprint.size;
        if matches!(input.direction, Direction::Lr | Direction::Rl) {
            std::mem::swap(&mut size.w, &mut size.h);
        }
        projected.sizes[declaration] = SizeRule::Exact(size);
        projected.boxes[declaration].role = BoxRole::Node;
    }
    let kept: Vec<_> = representative
        .iter()
        .enumerate()
        .filter_map(|(index, &owner)| (index == owner).then_some(index))
        .collect();
    let mut mapping = vec![0; graph.nodes.len()];
    for (new, &old) in kept.iter().enumerate() {
        mapping[old] = new;
    }
    for (index, &owner) in representative.iter().enumerate() {
        mapping[index] = mapping[owner];
    }
    let mut edges = Vec::new();
    let projected_edges = graph
        .edges
        .iter()
        .enumerate()
        .filter_map(|(index, edge)| {
            if representative[edge.tail] == representative[edge.head]
                && bundles
                    .iter()
                    .any(|bundle| bundle.target == representative[edge.tail])
            {
                return None;
            }
            edges.push(index);
            Some(Edge {
                tail: mapping[edge.tail],
                head: mapping[edge.head],
                ..*edge
            })
        })
        .collect();
    let nodes = kept
        .iter()
        .map(|&index| {
            let mut node = graph.nodes[index].clone();
            if let Some(bundle) = bundles.iter().find(|bundle| bundle.target == index) {
                node.w = bundle.footprint.size.w;
                node.h = bundle.footprint.size.h;
            }
            node
        })
        .collect();
    let mut graph = Graph {
        nodes,
        edges: projected_edges,
        params: graph.params,
    };
    let reversed = cycles::break_cycles(&graph)?;
    for (edge, reversed) in graph.edges.iter_mut().zip(reversed) {
        edge.reversed = reversed;
    }
    Ok(Contraction {
        graph,
        input: projected,
        kept,
        mapping,
        edges,
    })
}

struct Expansion<'a> {
    graph: &'a Graph,
    input: &'a Input,
    contraction: Contraction,
    bundles: Vec<Bundle>,
}

impl Expansion<'_> {
    fn expand(mut self, mut result: Component) -> Result<Component, LayoutError> {
        let envelopes = std::mem::take(&mut result.boxes);
        result.boxes = self
            .contraction
            .mapping
            .iter()
            .map(|&index| envelopes[index])
            .collect();
        for (node, _) in &mut result.titles {
            *node = self.contraction.kept[*node];
        }
        let outer_routes = std::mem::take(&mut result.routes);
        result.routes = self
            .graph
            .edges
            .iter()
            .enumerate()
            .map(|(original, _)| route::EdgeRoute {
                original,
                points: Vec::new(),
            })
            .collect();
        for (mut route, &original) in outer_routes.into_iter().zip(&self.contraction.edges) {
            route.original = original;
            result.routes[original] = route;
        }
        for bundle in &mut self.bundles {
            let envelope = envelopes[self.contraction.mapping[bundle.target]];
            place_fragment(
                &mut result,
                &mut bundle.target_part,
                geometry::translated(
                    bundle.footprint.target,
                    Point {
                        x: envelope.x,
                        y: envelope.y,
                    },
                )?,
            )?;
            for ((_, fragment), &rect) in bundle.notes.iter_mut().zip(&bundle.footprint.notes) {
                place_fragment(
                    &mut result,
                    fragment,
                    geometry::translated(
                        rect,
                        Point {
                            x: envelope.x,
                            y: envelope.y,
                        },
                    )?,
                )?;
            }
            result.loop_extents.push(envelope);
        }
        self.reconnect(&mut result)?;
        Ok(result)
    }

    fn reconnect(&self, result: &mut Component) -> Result<(), LayoutError> {
        let obstacles: Vec<_> = result
            .labels
            .iter()
            .chain(&result.titles)
            .copied()
            .collect();
        let routing = super::attachment_routes::EndpointRouting {
            graph: self.graph,
            input: self.input,
            boxes: &result.boxes,
            labels: &obstacles,
        };
        for &index in &self.contraction.edges {
            let edge = &self.graph.edges[index];
            if edge.decl == i32::MAX || !self.affected(edge) {
                continue;
            }
            result.routes[index].points = routing.route(edge)?;
        }
        for (index, edge) in self.graph.edges.iter().enumerate() {
            if edge.decl != i32::MAX && result.routes[index].points.is_empty() {
                result.routes[index].points = routing.route(edge)?;
            }
        }
        Ok(())
    }

    fn affected(&self, edge: &Edge) -> bool {
        self.bundles.iter().any(|bundle| {
            bundle.target_part.members.contains(&edge.tail)
                || bundle.target_part.members.contains(&edge.head)
                || bundle
                    .notes
                    .iter()
                    .any(|(note, _)| *note == edge.tail || *note == edge.head)
        })
    }
}

fn place_fragment(
    result: &mut Component,
    fragment: &mut Fragment,
    position: Rect,
) -> Result<(), LayoutError> {
    super::attachment_parts::translate(
        &mut fragment.layout,
        Point {
            x: position.x,
            y: position.y,
        },
    )?;
    for (&original, &rect) in fragment.members.iter().zip(&fragment.layout.boxes) {
        result.boxes[original] = rect;
    }
    for (route, &original) in fragment.layout.routes.drain(..).zip(&fragment.edges) {
        result.routes[original] = route::EdgeRoute {
            original,
            points: route.points,
        };
    }
    result.labels.append(&mut fragment.layout.labels);
    result
        .label_reservations
        .append(&mut fragment.layout.label_reservations);
    result
        .loop_extents
        .append(&mut fragment.layout.loop_extents);
    result.titles.extend(
        fragment
            .layout
            .titles
            .drain(..)
            .map(|(index, rect)| (fragment.members[index], rect)),
    );
    result.budget |= fragment.layout.budget;
    Ok(())
}
