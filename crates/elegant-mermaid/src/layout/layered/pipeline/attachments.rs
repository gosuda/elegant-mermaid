use std::collections::BTreeMap;

use super::attachment_geometry::{self as geometry, Footprint, FootprintInput, NoteSize};
use super::attachment_parts::{Fragment, FragmentInput};
use super::*;

struct AttachedNote {
    node: usize,
    fragment: Fragment,
    side: crate::layout::input::AttachmentSide,
}

struct Bundle {
    target: usize,
    target_part: Fragment,
    notes: Vec<AttachedNote>,
    footprint: Footprint,
    growth: Size,
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
    for attachment in context
        .input
        .attachments
        .iter()
        .filter(|item| item.target == declaration)
    {
        let note_decl = i32::try_from(attachment.note).map_err(|_| LayoutError::Overflow)?;
        let note = *declarations.get(&note_decl).ok_or(LayoutError::Domain)?;
        let fragment = context.build(vec![note], declaration)?;
        notes.push(AttachedNote {
            node: note,
            fragment,
            side: attachment.side,
        });
    }
    let sizes: Vec<_> = notes
        .iter()
        .map(|note| NoteSize {
            size: note.fragment.size,
            side: note.side,
        })
        .collect();
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
        growth: Size { w: 0, h: 0 },
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

fn project_groups(
    input: &Input,
    graph: &Graph,
    bundles: &[Bundle],
) -> Result<
    (
        Vec<crate::layout::input::Group>,
        Vec<crate::layout::input::RegionSet>,
    ),
    LayoutError,
> {
    let metadata = super::super::regions::Metadata::validate(input)?;
    let absorbed: Vec<_> = input
        .groups
        .iter()
        .map(|group| {
            bundles.iter().any(|bundle| {
                bundle
                    .target_part
                    .members
                    .iter()
                    .any(|&member| graph.nodes[member].id == group.id)
            })
        })
        .collect();
    let scoped = super::super::regions::Metadata {
        parents: metadata.parents,
        sets: metadata
            .sets
            .into_iter()
            .filter(|set| !absorbed[set.parent])
            .collect(),
    };
    let mut retained: Vec<_> = absorbed.iter().map(|absorbed| !absorbed).collect();
    for set in &scoped.sets {
        for &region in &set.regions {
            retained[region] = true;
        }
    }
    let sets = scoped.project(&retained)?;
    let groups = input
        .groups
        .iter()
        .zip(retained)
        .filter(|(_, retained)| *retained)
        .map(|(group, _)| group.clone())
        .collect();
    Ok((groups, sets))
}

impl Bundle {
    fn fit_final_frame(
        &mut self,
        reservation: Rect,
        graph: &Graph,
        input: &Input,
    ) -> Result<(), LayoutError> {
        let growth = self.target_growth(reservation, input.direction)?;
        self.target_part
            .grow_root(super::attachment_parts::FrameGrowth {
                root: self.target,
                amount: growth,
                graph,
                input,
            })?;
        let notes: Vec<_> = self
            .notes
            .iter()
            .map(|note| NoteSize {
                size: note.fragment.size,
                side: note.side,
            })
            .collect();
        self.footprint = geometry::footprint(FootprintInput {
            target: self.target_part.size,
            notes: &notes,
            direction: input.direction,
            gap: narrow(2 * i64::from(graph.params.slot) + 2)?,
        })?;
        if self.footprint.size.w != reservation.w || self.footprint.size.h != reservation.h {
            return Err(LayoutError::Domain);
        }
        self.growth = growth;
        Ok(())
    }

    fn target_growth(&self, reservation: Rect, direction: Direction) -> Result<Size, LayoutError> {
        let mut growth = Size {
            w: narrow(i64::from(reservation.w) - i64::from(self.footprint.size.w))?,
            h: narrow(i64::from(reservation.h) - i64::from(self.footprint.size.h))?,
        };
        if growth.w < 0 || growth.h < 0 {
            return Err(LayoutError::Domain);
        }
        let (height_growth, target_height, note_height) = match direction {
            Direction::Lr | Direction::Rl => (
                &mut growth.w,
                self.target_part.size.w,
                self.notes
                    .iter()
                    .map(|note| note.fragment.size.w)
                    .max()
                    .unwrap_or(0),
            ),
            Direction::Tb | Direction::Bt => (
                &mut growth.h,
                self.target_part.size.h,
                self.notes
                    .iter()
                    .map(|note| note.fragment.size.h)
                    .max()
                    .unwrap_or(0),
            ),
        };
        if *height_growth > 0 {
            *height_growth = narrow(
                i64::from(*height_growth) + i64::from((note_height - target_height).max(0)),
            )?;
        }
        Ok(growth)
    }
}

fn absorb_members(
    representative: &mut [usize],
    projected: &mut Input,
    input: &Input,
    graph: &Graph,
    bundles: &[Bundle],
) -> Result<(), LayoutError> {
    for bundle in bundles {
        let target =
            usize::try_from(graph.nodes[bundle.target].decl).map_err(|_| LayoutError::Domain)?;
        let members = bundle
            .target_part
            .members
            .iter()
            .copied()
            .chain(bundle.notes.iter().map(|note| note.node));
        for member in members {
            representative[member] = bundle.target;
            let declaration =
                usize::try_from(graph.nodes[member].decl).map_err(|_| LayoutError::Domain)?;
            projected.boxes[declaration].parent = input.boxes[target].parent.clone();
        }
    }
    Ok(())
}

fn pin_targets(
    projected: &mut Input,
    input: &Input,
    graph: &Graph,
    bundles: &[Bundle],
    groups: &[crate::layout::input::Group],
) -> Result<(), LayoutError> {
    for bundle in bundles {
        let node = &graph.nodes[bundle.target];
        let declaration = usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?;
        let mut size = bundle.footprint.size;
        if matches!(input.direction, Direction::Lr | Direction::Rl) {
            std::mem::swap(&mut size.w, &mut size.h);
        }
        projected.sizes[declaration] = SizeRule::Exact(size);
        projected.boxes[declaration].role = if groups.iter().any(|group| group.id == node.id) {
            BoxRole::Group
        } else {
            BoxRole::Node
        };
    }
    Ok(())
}

fn projection_mapping(representative: &[usize], kept: &[usize]) -> Vec<usize> {
    let mut mapping = vec![0; representative.len()];
    for (new, &old) in kept.iter().enumerate() {
        mapping[old] = new;
    }
    for (index, &owner) in representative.iter().enumerate() {
        mapping[index] = mapping[owner];
    }
    mapping
}

fn contract(graph: &Graph, input: &Input, bundles: &[Bundle]) -> Result<Contraction, LayoutError> {
    let (groups, region_sets) = project_groups(input, graph, bundles)?;
    let mut projected = input.clone();
    projected
        .sizes
        .resize(input.boxes.len(), SizeRule::Measured);
    let mut representative: Vec<_> = (0..graph.nodes.len()).collect();
    absorb_members(&mut representative, &mut projected, input, graph, bundles)?;
    pin_targets(&mut projected, input, graph, bundles, &groups)?;
    projected.region_sets = region_sets;
    projected.groups = groups;
    let kept: Vec<_> = representative
        .iter()
        .enumerate()
        .filter_map(|(index, &owner)| (index == owner).then_some(index))
        .collect();
    let mapping = projection_mapping(&representative, &kept);
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
        result.titles.retain(|(node, _)| {
            !self
                .bundles
                .iter()
                .any(|bundle| bundle.target == self.contraction.kept[*node])
        });
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
            bundle.fit_final_frame(envelope, self.graph, self.input)?;
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
            for (note, &rect) in bundle.notes.iter_mut().zip(&bundle.footprint.notes) {
                place_fragment(
                    &mut result,
                    &mut note.fragment,
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
        let regions = super::super::regions::ComponentSets::new(self.input, self.graph)?;
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
            regions: &regions,
        };
        for &index in &self.contraction.edges {
            let edge = &self.graph.edges[index];
            if edge.decl == i32::MAX || !self.affected(edge) {
                continue;
            }
            result.routes[index].points = routing.route(edge)?;
        }
        for (index, edge) in self.graph.edges.iter().enumerate() {
            if edge.decl != i32::MAX
                && (result.routes[index].points.is_empty() || self.resized_endpoint(edge))
            {
                result.routes[index].points = routing.route(edge)?;
            }
        }
        Ok(())
    }

    fn resized_endpoint(&self, edge: &Edge) -> bool {
        edge.tail != edge.head
            && self.bundles.iter().any(|bundle| {
                (bundle.growth.w > 0 || bundle.growth.h > 0)
                    && (edge.tail == bundle.target || edge.head == bundle.target)
            })
    }

    fn affected(&self, edge: &Edge) -> bool {
        self.bundles.iter().any(|bundle| {
            bundle.target_part.members.contains(&edge.tail)
                || bundle.target_part.members.contains(&edge.head)
                || bundle
                    .notes
                    .iter()
                    .any(|note| note.node == edge.tail || note.node == edge.head)
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
