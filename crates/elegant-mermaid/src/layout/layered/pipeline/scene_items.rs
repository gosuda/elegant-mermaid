use super::*;
pub(super) fn assemble(
    dump: &Dump,
    placed_titles: &[(usize, Rect)],
    lines: &[Vec<measure::Line<'_>>],
    edges: &[EdgeOptions<'_>],
) -> Vec<Group> {
    let mut groups = Vec::new();
    append_edges(&mut groups, dump, edges);
    append_boxes(&mut groups, dump, placed_titles, lines);
    groups.sort_by_key(|group| match group.role {
        GroupRole::Group => 0,
        GroupRole::Edge => 1,
        GroupRole::Node => 2,
        GroupRole::Decor => 3,
    });
    groups
}

fn append_edges(groups: &mut Vec<Group>, dump: &Dump, edges: &[EdgeOptions<'_>]) {
    for (r, edge) in dump.routes.iter().zip(edges) {
        groups.push(Group {
            role: GroupRole::Edge,
            owner: r.id.clone(),
            items: {
                let mut items = edge_items(r, edge, dump.options.profile);
                for label in dump.labels.iter().filter(|l| l.owner == r.id) {
                    items.push(Item::Text(TextItem {
                        rect: label.rect,
                        role: TextRole::Label,
                        size: 14,
                        align: Align::Middle,
                        style: TextStyle::Text,
                        series: 0,
                        lines: label
                            .lines
                            .iter()
                            .map(|line| vec![Run::plain(line)])
                            .collect(),
                    }));
                }
                items
            },
        });
    }
}

fn append_boxes(
    groups: &mut Vec<Group>,
    dump: &Dump,
    placed_titles: &[(usize, Rect)],
    lines: &[Vec<measure::Line<'_>>],
) {
    for (i, b) in dump.boxes.iter().enumerate() {
        let lh = constant(dump.options.profile, "line_h");
        let height = lines[i].iter().fold(0, |height, _| height + lh);
        let rect = Rect {
            y: b.rect.y + (b.rect.h - height) / 2,
            h: height,
            ..b.rect
        };
        groups.push(Group {
            role: if b.role == BoxRole::Group {
                GroupRole::Group
            } else {
                GroupRole::Node
            },
            owner: b.id.clone(),
            items: vec![
                Item::Rect(RectItem {
                    shape: Shape::plain(if b.role == BoxRole::Group {
                        ShapeStyle::Group
                    } else {
                        ShapeStyle::Node
                    }),
                    rect: b.rect,
                }),
                Item::Text(TextItem {
                    rect: placed_titles
                        .iter()
                        .find(|(index, _)| *index == i)
                        .map_or(rect, |(_, rect)| *rect),
                    role: TextRole::Label,
                    size: 14,
                    align: Align::Middle,
                    style: TextStyle::Text,
                    series: 0,
                    lines: lines[i].iter().map(|l| vec![Run::plain(l.text)]).collect(),
                }),
            ],
        });
    }
}
fn marker_axis(a: Point, b: Point) -> MarkerAxis {
    let dx = i64::from(b.x) - i64::from(a.x);
    let dy = i64::from(b.y) - i64::from(a.y);
    match (dx.abs() >= dy.abs(), dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

fn edge_items(route: &SceneRoute, edge: &EdgeOptions<'_>, profile: Profile) -> Vec<Item> {
    if edge.stroke == "invisible" {
        return Vec::new();
    }
    let mut shape = Shape::plain(ShapeStyle::Edge);
    match edge.stroke {
        "thick" => shape.width = Width::Emphasis,
        "dotted" => shape.line = Line::Dotted,
        "dashed" => shape.line = Line::Dashed,
        _ => {}
    }
    let mut items = vec![Item::Polyline(PolylineItem {
        shape,
        points: route.points.clone(),
        corner: constant(profile, "corner_radius"),
    })];
    if route.points.len() < 2 {
        return items;
    }
    let end = route.points.len() - 1;
    if let Some(marker) = edge.marker_start {
        items.push(Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[0],
            axis: marker_axis(route.points[1], route.points[0]),
        }));
    }
    if let Some(marker) = edge.marker_end {
        items.push(Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[end],
            axis: marker_axis(route.points[end - 1], route.points[end]),
        }));
    }
    items
}
