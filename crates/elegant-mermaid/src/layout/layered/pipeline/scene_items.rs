use super::*;
use crate::geom::GeomError;
use crate::math::vector::scene::{LabelText, label_items};

pub(super) fn assemble(
    dump: &Dump,
    input: &Input,
    placed_titles: &[(usize, Rect)],
    lines: &[Vec<measure::StyledLine<'_>>],
    route_lines: &[Vec<measure::StyledLine<'_>>],
    edges: &[EdgeOptions<'_>],
) -> Result<Vec<Group>, GeomError> {
    let mut groups = Vec::new();
    let mut measured = input.labels.iter().zip(route_lines).peekable();
    let route_lines = dump
        .labels
        .iter()
        .map(|label| {
            while let Some((source, _)) = measured.peek() {
                if source.id == label.id {
                    return measured.next().map(|(_, lines)| lines.as_slice());
                }
                measured.next();
            }
            None
        })
        .collect::<Vec<_>>();
    append_edges(&mut groups, dump, &route_lines, edges)?;
    append_boxes(&mut groups, dump, placed_titles, lines)?;
    groups.sort_by_key(|group| match group.role {
        GroupRole::Group => 0,
        GroupRole::Edge => 1,
        GroupRole::Node => 2,
        GroupRole::Decor => 3,
    });
    Ok(groups)
}

fn label_text<'a>(rect: Rect, lines: &'a [measure::StyledLine<'a>]) -> LabelText<'a> {
    LabelText {
        rect,
        role: TextRole::Label,
        size: 14,
        align: Align::Middle,
        style: TextStyle::Text,
        series: 0,
        lines,
    }
}

fn split_classes(items: Vec<Item>) -> (Vec<Item>, Vec<Item>) {
    let is_text = |item: &Item| matches!(item, Item::Text(_));
    let (texts, shapes): (Vec<_>, Vec<_>) = items.into_iter().partition(is_text);
    (shapes, texts)
}

fn append_edges(
    groups: &mut Vec<Group>,
    dump: &Dump,
    route_lines: &[Option<&[measure::StyledLine<'_>]>],
    edges: &[EdgeOptions<'_>],
) -> Result<(), GeomError> {
    for (r, edge) in dump.routes.iter().zip(edges) {
        let mut shapes = Vec::new();
        let mut texts = Vec::new();
        for (label, lines) in dump.labels.iter().zip(route_lines) {
            if label.owner != r.id {
                continue;
            }
            let empty: Vec<measure::StyledLine<'_>> = Vec::new();
            let lines = lines.unwrap_or(&empty);
            let (label_shapes, label_texts) =
                split_classes(label_items(label_text(label.rect, lines))?);
            shapes.extend(label_shapes);
            texts.extend(label_texts);
        }
        let invisible = edge.stroke == "invisible";
        groups.push(Group {
            role: GroupRole::Edge,
            owner: r.id.clone(),
            items: {
                let mut items = shapes;
                if !invisible {
                    items.push(route_polyline(r, edge, dump.options.profile));
                    items.extend(route_markers(r, edge));
                }
                items.extend(texts);
                items
            },
        });
    }
    Ok(())
}

fn append_boxes(
    groups: &mut Vec<Group>,
    dump: &Dump,
    placed_titles: &[(usize, Rect)],
    lines: &[Vec<measure::StyledLine<'_>>],
) -> Result<(), GeomError> {
    for (i, b) in dump.boxes.iter().enumerate() {
        let lh = constant(dump.options.profile, "line_h");
        let height = lines[i].iter().fold(0, |height, _| height + lh);
        let rect = Rect {
            y: b.rect.y + (b.rect.h - height) / 2,
            h: height,
            ..b.rect
        };
        let text_rect = placed_titles
            .iter()
            .find(|(index, _)| *index == i)
            .map_or(rect, |(_, rect)| *rect);
        let text = label_items(label_text(text_rect, &lines[i]))?;
        groups.push(Group {
            role: if b.role == BoxRole::Group {
                GroupRole::Group
            } else {
                GroupRole::Node
            },
            owner: b.id.clone(),
            items: vec![Item::Rect(RectItem {
                shape: Shape::plain(if b.role == BoxRole::Group {
                    ShapeStyle::Group
                } else {
                    ShapeStyle::Node
                }),
                rect: b.rect,
            })]
            .into_iter()
            .chain(text)
            .collect(),
        });
    }
    Ok(())
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

fn route_style(edge: &EdgeOptions<'_>) -> Shape {
    let mut shape = Shape::plain(ShapeStyle::Edge);
    match edge.stroke {
        "thick" => shape.width = Width::Emphasis,
        "dotted" => shape.line = Line::Dotted,
        "dashed" => shape.line = Line::Dashed,
        _ => {}
    }
    shape
}

fn route_polyline(route: &SceneRoute, edge: &EdgeOptions<'_>, profile: Profile) -> Item {
    Item::Polyline(PolylineItem {
        shape: route_style(edge),
        points: route.points.clone(),
        corner: constant(profile, "corner_radius"),
    })
}

fn route_markers(route: &SceneRoute, edge: &EdgeOptions<'_>) -> Vec<Item> {
    if route.points.len() < 2 {
        return Vec::new();
    }
    let end = route.points.len() - 1;
    let start_marker = edge.marker_start.map(|marker| {
        Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[0],
            axis: marker_axis(route.points[1], route.points[0]),
        })
    });
    let end_marker = edge.marker_end.map(|marker| {
        Item::MarkerRef(MarkerRefItem {
            marker,
            at: route.points[end],
            axis: marker_axis(route.points[end - 1], route.points[end]),
        })
    });
    start_marker.into_iter().chain(end_marker).collect()
}
