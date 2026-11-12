use std::borrow::Cow;

use super::*;

pub(crate) fn project_cell_attachments(scene: &mut Scene) {
    if scene.profile() != Profile::Cell {
        return;
    }
    for group in &mut scene.items {
        if group.role != GroupRole::Edge {
            continue;
        }
        let mut marker_index = 0;
        for item in &mut group.items {
            let is_marker = matches!(item, Item::MarkerRef(_));
            if let Cow::Owned(projected) = primitive(&scene.dump, &group.owner, item, marker_index)
            {
                *item = projected;
            }
            if is_marker {
                marker_index += 1;
            }
        }
    }
}

fn attachment(dump: &Dump, id: &str, mut point: Point) -> Point {
    let Some(b) = dump.boxes.iter().find(|b| b.id == id) else {
        return point;
    };
    let r = b.rect;
    let (x, y) = (i64::from(point.x), i64::from(point.y));
    let right = i64::from(r.x) + i64::from(r.w);
    let bottom = i64::from(r.y) + i64::from(r.h);
    if r.w <= 0 || r.h <= 0 || x < i64::from(r.x) || x > right || y < i64::from(r.y) || y > bottom {
        return point;
    }
    if x == right {
        point.x -= 1;
    }
    if y == bottom {
        point.y -= 1;
    }
    point
}

fn primitive<'a>(dump: &Dump, owner: &str, item: &'a Item, marker_index: usize) -> Cow<'a, Item> {
    let Some(route) = dump
        .routes
        .iter()
        .find(|r| r.id == owner && !r.points.is_empty())
    else {
        return Cow::Borrowed(item);
    };
    let (Some(&first), Some(&last)) = (route.points.first(), route.points.last()) else {
        return Cow::Borrowed(item);
    };
    let a = attachment(dump, &route.from, first);
    let b = attachment(dump, &route.to, last);
    match item {
        Item::MarkerRef(marker) => {
            let at = if marker.at == first && marker.at == last {
                let name = marker.marker.as_str();
                if route.marker_end == name && (route.marker_start != name || marker_index > 0) {
                    b
                } else {
                    a
                }
            } else if marker.at == first {
                a
            } else if marker.at == last {
                b
            } else {
                return Cow::Borrowed(item);
            };
            if at == marker.at {
                return Cow::Borrowed(item);
            }
            let mut projected = marker.clone();
            projected.at = at;
            Cow::Owned(Item::MarkerRef(projected))
        }
        Item::Polyline(line) if line.points == route.points && (a != first || b != last) => {
            Cow::Owned(Item::Polyline(PolylineItem {
                shape: line.shape,
                points: line_points(&line.points, a, b),
                corner: line.corner,
            }))
        }
        _ => Cow::Borrowed(item),
    }
}

fn line_points(points: &[Point], first: Point, last: Point) -> Vec<Point> {
    let mut out = Vec::with_capacity(points.len() + 2);
    out.push(first);
    let count = points.len().max(2);
    for i in 1..count {
        let Some(&a) = out.last() else { return out };
        let b = if i == count - 1 { last } else { points[i] };
        let original_a = points[i - 1];
        let original_b = points[i.min(points.len() - 1)];
        let orthogonal = original_a.x == original_b.x || original_a.y == original_b.y;
        if orthogonal && a.x != b.x && a.y != b.y {
            let mut horizontal = original_a.y == original_b.y;
            if i == count - 1 && i != 1 {
                horizontal = !horizontal;
            }
            out.push(if horizontal {
                Point { x: b.x, y: a.y }
            } else {
                Point { x: a.x, y: b.y }
            });
        }
        if out.last() != Some(&b) {
            out.push(b);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cells::{Options, render},
        geom::{Rect, Size},
    };

    fn scene(
        points: Vec<Point>,
        expected: Vec<Point>,
        markers: bool,
    ) -> Result<(Scene, Scene), Box<dyn std::error::Error>> {
        let mut dump = Dump::new(
            "flowchart",
            DumpOptions {
                profile: Profile::Cell,
                ..DumpOptions::default()
            },
        );
        for (id, rect) in [
            (
                "a",
                Rect {
                    x: 1,
                    y: 1,
                    w: 3,
                    h: 3,
                },
            ),
            (
                "b",
                Rect {
                    x: 7,
                    y: 7,
                    w: 3,
                    h: 3,
                },
            ),
        ] {
            dump.boxes.push(SceneBox {
                id: id.into(),
                role: BoxRole::Node,
                rect,
                parent: String::new(),
                exclusive: true,
            });
        }
        dump.routes.push(SceneRoute {
            id: "e".into(),
            from: "a".into(),
            to: "b".into(),
            orthogonal: true,
            points: points.clone(),
            marker_start: "point".into(),
            marker_end: "point".into(),
            stroke: String::new(),
        });
        let items = |p: Vec<Point>| -> Result<Vec<Item>, Box<dyn std::error::Error>> {
            let mut items = vec![Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Edge),
                points: p.clone(),
                corner: 0,
            })];
            if markers {
                for at in p.first().into_iter().chain(p.last()).copied() {
                    items.push(Item::MarkerRef(MarkerRefItem {
                        marker: MarkerName::new("point").ok_or("missing point marker")?,
                        at,
                        axis: MarkerAxis::PlusX,
                    }));
                }
            }
            Ok(items)
        };
        let actual = Scene::new(
            Size { w: 12, h: 12 },
            dump.clone(),
            vec![Group::new(GroupRole::Edge, "e").with_items(items(points)?)],
        );
        dump.routes.clear();
        let oracle = Scene::new(
            Size { w: 12, h: 12 },
            dump,
            vec![Group::new(GroupRole::Edge, "e").with_items(items(expected)?)],
        );
        Ok((actual, oracle))
    }

    #[test]
    fn producer_projects_four_attachment_directions_and_markers()
    -> Result<(), Box<dyn std::error::Error>> {
        for (source, target, expected_source, expected_target) in [
            ((4, 2), (7, 8), (3, 2), (7, 8)),
            ((1, 2), (10, 8), (1, 2), (9, 8)),
            ((2, 4), (8, 7), (2, 3), (8, 7)),
            ((2, 1), (8, 10), (2, 1), (8, 9)),
        ] {
            let p = |(x, y)| Point { x, y };
            let points = vec![
                p(source),
                Point { x: 5, y: source.1 },
                Point { x: 5, y: target.1 },
                p(target),
            ];
            let expected = vec![
                p(expected_source),
                Point {
                    x: 5,
                    y: expected_source.1,
                },
                Point { x: 5, y: source.1 },
                Point { x: 5, y: target.1 },
                Point {
                    x: 5,
                    y: expected_target.1,
                },
                p(expected_target),
            ];
            let (mut actual, oracle) = scene(points, expected, true)?;
            let before = actual.dump();
            project_cell_attachments(&mut actual);
            assert_eq!(actual.dump(), before);
            let snapshot = actual.clone();
            assert_eq!(
                render(&actual, &Options::default())?,
                render(&oracle, &Options::default())?
            );
            assert_eq!(actual, snapshot);
        }
        Ok(())
    }

    #[test]
    fn producer_projects_far_corners_preserving_bends() -> Result<(), Box<dyn std::error::Error>> {
        let (mut actual, oracle) = scene(
            vec![
                Point { x: 4, y: 4 },
                Point { x: 6, y: 4 },
                Point { x: 6, y: 10 },
                Point { x: 10, y: 10 },
            ],
            vec![
                Point { x: 3, y: 3 },
                Point { x: 6, y: 3 },
                Point { x: 6, y: 4 },
                Point { x: 6, y: 10 },
                Point { x: 6, y: 9 },
                Point { x: 9, y: 9 },
            ],
            true,
        )?;
        let before = actual.dump();
        project_cell_attachments(&mut actual);
        assert_eq!(actual.dump(), before);
        let snapshot = actual.clone();
        assert_eq!(
            render(&actual, &Options::default())?,
            render(&oracle, &Options::default())?
        );
        assert_eq!(actual, snapshot);
        Ok(())
    }

    #[test]
    fn producer_projects_coincident_corner_markers_source_before_target()
    -> Result<(), Box<dyn std::error::Error>> {
        let point = Point { x: 4, y: 4 };
        let (mut actual, _) = scene(vec![point], vec![], false)?;
        let mut dump = actual.dump_part().clone();
        dump.boxes[1].rect = Rect {
            x: 4,
            y: 4,
            w: 3,
            h: 3,
        };
        let marker = MarkerName::new("point").ok_or("missing point marker")?;
        let items = vec![
            Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Edge),
                points: vec![point],
                corner: 0,
            }),
            Item::MarkerRef(MarkerRefItem {
                marker,
                at: point,
                axis: MarkerAxis::PlusX,
            }),
            Item::MarkerRef(MarkerRefItem {
                marker,
                at: point,
                axis: MarkerAxis::PlusX,
            }),
        ];
        actual = Scene::new(
            Size { w: 12, h: 12 },
            dump,
            vec![Group::new(GroupRole::Edge, "e").with_items(items)],
        );
        let before = actual.dump();
        project_cell_attachments(&mut actual);
        assert_eq!(actual.dump(), before);
        let snapshot = actual.clone();
        let output = render(&actual, &Options::default())?;
        let rows: Vec<_> = output.text.lines().collect();
        assert_eq!(rows[3].chars().nth(3), Some('▶'));
        assert_eq!(rows[4].chars().nth(4), Some('▶'));
        assert_eq!(actual, snapshot);
        Ok(())
    }

    #[test]
    fn producer_projects_self_loop_without_moving_internal_vertices()
    -> Result<(), Box<dyn std::error::Error>> {
        let points = vec![
            Point { x: 4, y: 2 },
            Point { x: 6, y: 2 },
            Point { x: 6, y: 3 },
            Point { x: 4, y: 3 },
        ];
        let expected = vec![
            Point { x: 3, y: 2 },
            Point { x: 6, y: 2 },
            Point { x: 6, y: 3 },
            Point { x: 3, y: 3 },
        ];
        let (actual, oracle) = scene(points, expected, true)?;
        let mut dump = actual.dump_part().clone();
        dump.routes[0].to = "a".into();
        let mut actual = Scene::new(actual.canvas(), dump, actual.items().to_vec());
        let before = actual.dump();
        project_cell_attachments(&mut actual);
        assert_eq!(actual.dump(), before);
        let snapshot = actual.clone();
        assert_eq!(
            render(&actual, &Options::default())?,
            render(&oracle, &Options::default())?
        );
        assert_eq!(actual, snapshot);
        Ok(())
    }
}

#[cfg(test)]
mod invariants {
    use super::*;

    #[test]
    fn one_point_projection_uses_x_first() {
        assert_eq!(
            line_points(
                &[Point { x: 4, y: 4 }],
                Point { x: 3, y: 3 },
                Point { x: 4, y: 4 }
            ),
            vec![
                Point { x: 3, y: 3 },
                Point { x: 4, y: 3 },
                Point { x: 4, y: 4 },
            ]
        );
    }

    #[test]
    fn vector_scene_is_unchanged() {
        let mut scene = Scene::new(
            crate::geom::Size { w: 12, h: 12 },
            Dump::new("flowchart", DumpOptions::default()),
            vec![Group::new(GroupRole::Edge, "e")],
        );
        let before = scene.clone();
        project_cell_attachments(&mut scene);
        assert_eq!(scene, before);
    }
}
