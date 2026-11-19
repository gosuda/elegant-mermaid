use super::attachment_routes::EndpointRouting;
use super::*;

pub(crate) fn reroute_endpoints(
    input: &Input,
    scene: Scene,
    edges: &[EdgeOptions<'_>],
) -> Result<Scene, LayoutError> {
    if !input
        .routes
        .iter()
        .any(|route| route.from_side.is_some() || route.to_side.is_some())
    {
        return Ok(scene);
    }
    let (graph, _) = measured(input, edges)?;
    let boxes = graph
        .nodes
        .iter()
        .map(|node| {
            scene
                .boxes()
                .iter()
                .find(|item| item.id == node.id)
                .map(|item| item.rect)
                .ok_or(LayoutError::Domain)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let labels = scene
        .items()
        .iter()
        .flat_map(|group| &group.items)
        .filter_map(|item| match item {
            Item::Text(text) => Some((0, text.rect)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let regions = super::super::regions::ComponentSets {
        groups: Vec::new(),
        sets: Vec::new(),
        parents: Vec::new(),
    };
    let routing = EndpointRouting {
        graph: &graph,
        input,
        boxes: &boxes,
        labels: &labels,
        regions: &regions,
    };
    let canvas = scene.canvas();
    let bounds = Rect {
        x: 0,
        y: 0,
        w: canvas.w,
        h: canvas.h,
    };
    let mut dump = scene.dump_part().clone();
    let mut groups = scene.items().to_vec();
    for (index, route) in input.routes.iter().enumerate() {
        if route.from_side.is_none() && route.to_side.is_none() {
            continue;
        }
        let edge = graph.edges.get(index).ok_or(LayoutError::Domain)?;
        let points = routing.route_forced(edge, route.from_side, route.to_side, bounds)?;
        let group = groups
            .iter_mut()
            .find(|group| group.role == GroupRole::Edge && group.owner == route.id)
            .ok_or(LayoutError::Domain)?;
        update_edge_group(group, &points, &edges[index])?;
        dump.routes[index].points = points;
    }
    let fitted = if scene.profile() == Profile::Cell {
        cell_canvas_fitting(canvas, &dump.routes)?
    } else {
        canvas
    };
    Ok(Scene::new(fitted, dump, groups))
}

fn cell_canvas_fitting(canvas: Size, routes: &[SceneRoute]) -> Result<Size, LayoutError> {
    routes
        .iter()
        .flat_map(|route| route.points.iter())
        .try_fold(canvas, |fit, p| {
            Ok(Size {
                w: fit.w.max(p.x.checked_add(1).ok_or(LayoutError::Overflow)?),
                h: fit.h.max(p.y.checked_add(1).ok_or(LayoutError::Overflow)?),
            })
        })
}

fn update_edge_group(
    group: &mut Group,
    points: &[Point],
    edge: &EdgeOptions<'_>,
) -> Result<(), LayoutError> {
    let end = points.len().checked_sub(1).ok_or(LayoutError::Domain)?;
    let mut marker_index = 0_usize;
    for item in &mut group.items {
        match item {
            Item::Polyline(line) => {
                line.points.clear();
                line.points.extend_from_slice(points);
            }
            Item::MarkerRef(marker) => {
                let start = marker_index == 0 && edge.marker_start.is_some();
                let (a, b) = if start {
                    (*points.get(1).ok_or(LayoutError::Domain)?, points[0])
                } else {
                    (
                        points[end.checked_sub(1).ok_or(LayoutError::Domain)?],
                        points[end],
                    )
                };
                marker.at = b;
                marker.axis = axis(a, b);
                marker_index = marker_index.checked_add(1).ok_or(LayoutError::Overflow)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn axis(a: Point, b: Point) -> MarkerAxis {
    match (b.x.cmp(&a.x), b.y.cmp(&a.y)) {
        (std::cmp::Ordering::Less, _) => MarkerAxis::MinusX,
        (std::cmp::Ordering::Greater, _) => MarkerAxis::PlusX,
        (_, std::cmp::Ordering::Less) => MarkerAxis::MinusY,
        _ => MarkerAxis::PlusY,
    }
}

#[cfg(test)]
#[path = "endpoint_sides_tests.rs"]
mod tests;
