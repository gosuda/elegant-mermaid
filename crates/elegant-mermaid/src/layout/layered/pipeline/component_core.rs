use super::{constant, edge_sizes, fixed_geometry, narrow};
use crate::geom::{Rect, Size};
use crate::layout::input::Input;
use crate::layout::layered::{
    LayoutError, clusters, coords,
    graph::{Graph, Proper},
    gutters, isolate, labels, lanes, loops, order, regions, route,
};
use crate::measure;
use crate::scene::BoxRole;

pub(in crate::layout::layered) struct Measurements<'text, 'scene> {
    pub route_lines: Vec<Vec<measure::Line<'text>>>,
    pub titles: Vec<Size>,
    pub route_stacks: Vec<labels::Stack>,
    pub fixed: &'scene [isolate::Fixed<'scene>],
}

pub(in crate::layout::layered) struct Component {
    pub boxes: Vec<Rect>,
    pub routes: Vec<route::EdgeRoute>,
    pub labels: Vec<(usize, Rect)>,
    pub titles: Vec<(usize, Rect)>,
    pub loop_extents: Vec<Rect>,
    pub label_reservations: Vec<(usize, Rect)>,
    pub budget: bool,
}

impl Component {
    pub(super) fn packing_rects(&self) -> impl Iterator<Item = &Rect> {
        self.boxes
            .iter()
            .chain(self.label_reservations.iter().map(|(_, rect)| rect))
            .chain(self.titles.iter().map(|(_, rect)| rect))
            .chain(self.loop_extents.iter())
    }
}

pub(super) fn component_core(
    g: &Graph,
    input: &Input,
    measurements: &Measurements<'_, '_>,
    options: order::OrderOptions,
) -> Result<Component, LayoutError> {
    let sizes = edge_sizes(g, &measurements.route_stacks)?;
    let extents = loops::extents(g, &sizes, input)?;
    let super::component_input::Prepared {
        semantic,
        proper: p,
        clusters,
        label_nodes,
        gutter,
        paths,
        boundary,
        budget,
        region_sets,
        region_constraints,
    } = super::component_input::prepare(g, input, measurements)?;
    let mut proper_extents = extents.clone();
    proper_extents.resize(p.nodes.len(), 0);
    for cluster in &clusters {
        let extent = proper_extents[cluster.node];
        proper_extents[cluster.node] = 0;
        for &border in &cluster.right {
            proper_extents[border] = extent;
        }
    }
    let mut separated = p.clone();
    for (node, extent) in separated.nodes.iter_mut().zip(&proper_extents) {
        node.node.w = narrow(i64::from(node.node.w) + 2 * i64::from(*extent))?;
    }
    let CrossPlacement {
        proper: p,
        ordered,
        x,
        reserved_lanes,
    } = place_cross(
        p,
        options,
        CrossContext {
            separated: &separated,
            clusters: &clusters,
            region_sets: &region_sets,
            region_constraints: &region_constraints,
            semantic: &semantic,
            footprints: g,
            input,
            paths: &paths,
            boundary: &boundary,
            extents: &extents,
            label_sizes: &sizes,
        },
    )?;
    let mut drawn = p.clone();
    drawn
        .edges
        .retain(|e| semantic.edges.get(e.original).is_some());
    let all = route::route(&drawn, &ordered.layers, &x)?;
    let reversed: Vec<_> = semantic.edges.iter().map(|edge| edge.reversed).collect();
    let mut r = route::route_selected(&drawn, &ordered.layers, &x, &reversed)?;
    gutters::number(&clusters, &drawn, &x, &mut r)?;
    let lanes = lanes::number(
        lanes::LaneInput {
            graph: &semantic,
            proper: &drawn,
            x: &x,
            extents: &proper_extents,
            sizes: &sizes,
            reserved_x: reserved_lanes.as_deref(),
        },
        &mut r,
        &all,
    )?;
    let (mut y, mut top) = coords::rank_coords(&p, &ordered.layers, &r)?;
    loops::reserve_ranks(
        g,
        input,
        &sizes,
        loops::RankPlacement {
            proper: &p,
            layers: &ordered.layers,
            y: &mut y,
            top: &mut top,
        },
    )?;
    clusters::anchors(&clusters, &p, &ordered.layers, &top, &mut y)?;
    let node_placement = labels::Placement {
        proper: &p,
        x: &x,
        y: &y,
        gutter,
    };
    let (mut routes, _) = route::route_points(&drawn, &ordered.layers, &x, &y, &top, &r)?;
    let mut placed = labels::place(
        label_nodes,
        labels::Placement {
            proper: &p,
            x: &x,
            y: &y,
            gutter,
        },
        &measurements.route_stacks,
    )?;
    let boxes = component_boxes(g, node_placement, &clusters)?;
    routes.truncate(g.edges.len());
    let reversed_labels = lanes::place(
        lanes::LanePlacement {
            graph: &semantic,
            proper: &p,
            layers: &ordered.layers,
            y: &y,
            top: &top,
            routing: &r,
            sizes: &sizes,
        },
        &lanes,
        &mut routes,
    )?;
    labels::replace(g, &measurements.route_stacks, reversed_labels, &mut placed)?;
    let loop_labels = loops::place(g, &boxes, &sizes, &mut routes, input)?;
    labels::replace(g, &measurements.route_stacks, loop_labels, &mut placed)?;
    let labels::Placed {
        labels,
        reservations: label_reservations,
    } = placed;
    gutters::place(&clusters, &semantic, &boxes, &mut routes);
    let pad = constant(input.profile, "cluster_pad");
    let mut titles = Vec::new();
    for (index, node) in g.nodes.iter().enumerate() {
        let declaration = usize::try_from(node.decl).map_err(|_| LayoutError::Domain)?;
        if input.boxes[declaration].role != BoxRole::Group {
            continue;
        }
        let size = measurements.titles[declaration];
        if let Some(fixed) = measurements.fixed.iter().find(|fixed| fixed.id == node.id) {
            let (_, mut title) = fixed_geometry(fixed, size, input.direction, pad)?;
            title.x = narrow(i64::from(title.x) + i64::from(boxes[index].x))?;
            title.y = narrow(i64::from(title.y) + i64::from(boxes[index].y))?;
            titles.push((index, title));
            continue;
        }
        let cluster = clusters.iter().find(|cluster| cluster.node == index);
        let origin_x = if let Some(cluster) = cluster {
            i64::from(x[cluster.title]) - i64::from(size.w) / 2
        } else {
            i64::from(boxes[index].x)
                + crate::geom::floor_div(i64::from(boxes[index].w) - i64::from(size.w), 2)
        };
        let origin_y = cluster.map_or(boxes[index].y, |cluster| y[cluster.title]);
        titles.push((
            index,
            Rect {
                x: narrow(origin_x)?,
                y: narrow(i64::from(origin_y) + i64::from(pad))?,
                w: size.w,
                h: size.h,
            },
        ));
    }
    let loop_extents = loops::reservations(g, &boxes, &sizes, &extents, input)?;
    Ok(Component {
        boxes,
        routes,
        labels,
        titles,
        loop_extents,
        label_reservations,
        budget: budget || ordered.budget_exhausted,
    })
}

struct CrossContext<'a> {
    separated: &'a Proper,
    clusters: &'a [clusters::Cluster],
    region_sets: &'a regions::ComponentSets,
    region_constraints: &'a regions::Constraints,
    semantic: &'a Graph,
    footprints: &'a Graph,
    input: &'a Input,
    paths: &'a [Vec<usize>],
    boundary: &'a [i8],
    extents: &'a [i32],
    label_sizes: &'a [(i32, i32)],
}

struct CrossPlacement {
    proper: Proper,
    ordered: order::OrderResult,
    x: Vec<i32>,
    reserved_lanes: Option<Vec<Option<i32>>>,
}

fn place_cross(
    proper: Proper,
    options: order::OrderOptions,
    context: CrossContext<'_>,
) -> Result<CrossPlacement, LayoutError> {
    let CrossContext {
        separated,
        clusters,
        region_sets,
        region_constraints,
        semantic,
        footprints,
        input,
        paths,
        boundary,
        extents,
        label_sizes,
    } = context;
    let mut proper = proper;
    let mut ordered = order::order_compound(&proper, options, paths, boundary)?;
    let (x, reserved_lanes) = if region_sets.sets.is_empty() {
        let mut x = coords::cross_coords_compound(separated, &ordered.layers, paths)?;
        clusters::ports(clusters, &mut proper, &mut x)?;
        (x, None)
    } else {
        let mut placement = coords::cross_coords_regions(
            &mut ordered.layers,
            regions::CoordinateInput {
                input,
                sets: region_sets,
                minimum: region_constraints,
                graph: semantic,
                proper: separated,
                footprints,
                clusters,
                paths,
                loop_extents: extents,
                label_sizes,
            },
        )?;
        clusters::reserved_ports(clusters, &mut proper, &mut placement)?;
        (placement.x, Some(placement.lane_x))
    };
    Ok(CrossPlacement {
        proper,
        ordered,
        x,
        reserved_lanes,
    })
}

fn component_boxes(
    g: &Graph,
    placement: labels::Placement<'_>,
    clusters: &[clusters::Cluster],
) -> Result<Vec<Rect>, LayoutError> {
    let labels::Placement {
        proper: p, x, y, ..
    } = placement;
    let mut boxes: Vec<_> = g
        .nodes
        .iter()
        .enumerate()
        .map(|(i, _)| Rect {
            x: x[i] - p.nodes[i].node.w / 2,
            y: y[i],
            w: p.nodes[i].node.w,
            h: p.nodes[i].node.h,
        })
        .collect();
    clusters::frames(clusters, p, x, y, &mut boxes)?;
    Ok(boxes)
}
