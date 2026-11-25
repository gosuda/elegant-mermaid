use crate::geom::{Point, Rect};
use crate::layout::{input::Input, layered::LayoutError};
use crate::scene::{
    EllipseItem, GroupRole, Item, Line, PolygonItem, PolylineItem, Profile, RectItem, Scene, Shape,
    ShapeStyle, SymbolName, SymbolRefItem,
};

pub(super) fn paint(input: &Input, scene: Scene) -> Result<Scene, LayoutError> {
    let mut groups = scene.items().to_vec();
    for group in &mut groups {
        if group.role != GroupRole::Node {
            continue;
        }
        let Some(node) = input.boxes.iter().find(|node| node.id == group.owner) else {
            continue;
        };
        let shape = match node.shape.as_str() {
            "sm-circ" => "sm-circ",
            "fr-circ" => "fr-circ",
            "fork" => "fork",
            "choice" => "choice",
            "note" => "note",
            _ => continue,
        };
        let bounds = scene
            .boxes()
            .iter()
            .find(|bounds| bounds.id == group.owner)
            .ok_or(LayoutError::Domain)?
            .rect;
        if shape == "note" {
            let mut items = vec![Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Note),
                rect: bounds,
            })];
            items.extend(
                group
                    .items
                    .drain(..)
                    .filter(|item| matches!(item, Item::Text(_))),
            );
            group.items = items;
        } else {
            group.items = symbol_items(shape, bounds, input.profile)?;
        }
    }
    paint_regions(input, &scene, &mut groups)?;
    Ok(Scene::new(
        scene.canvas(),
        scene.dump_part().clone(),
        groups,
    ))
}

fn symbol_items(shape: &str, rect: Rect, profile: Profile) -> Result<Vec<Item>, LayoutError> {
    if rect.w <= 0 || rect.h <= 0 {
        return Err(LayoutError::Domain);
    }
    let right = rect.x.checked_add(rect.w).ok_or(LayoutError::Overflow)?;
    let bottom = rect.y.checked_add(rect.h).ok_or(LayoutError::Overflow)?;
    let centre = Point {
        x: rect
            .x
            .checked_add(rect.w / 2)
            .ok_or(LayoutError::Overflow)?,
        y: rect
            .y
            .checked_add(rect.h / 2)
            .ok_or(LayoutError::Overflow)?,
    };
    if profile == Profile::Cell && shape != "fork" {
        let name = match shape {
            "sm-circ" => "disc",
            "fr-circ" => "bullseye",
            "choice" => "diamond-hollow",
            _ => return Err(LayoutError::Domain),
        };
        return Ok(vec![Item::SymbolRef(SymbolRefItem {
            symbol: SymbolName::new(name).ok_or(LayoutError::Domain)?,
            at: Point {
                x: rect.x,
                y: rect.y,
            },
            style: if shape == "choice" {
                ShapeStyle::Node
            } else {
                ShapeStyle::Ink
            },
        })]);
    }
    match shape {
        "fork" => Ok(vec![Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Ink),
            rect,
        })]),
        "choice" => Ok(vec![Item::Polygon(PolygonItem {
            shape: Shape::plain(ShapeStyle::Node),
            points: vec![
                Point {
                    x: centre.x,
                    y: rect.y,
                },
                Point {
                    x: right,
                    y: centre.y,
                },
                Point {
                    x: centre.x,
                    y: bottom,
                },
                Point {
                    x: rect.x,
                    y: centre.y,
                },
            ],
        })]),
        "sm-circ" | "fr-circ" => circles(shape, rect, centre),
        _ => Err(LayoutError::Domain),
    }
}

fn circles(shape: &str, rect: Rect, centre: Point) -> Result<Vec<Item>, LayoutError> {
    let outer_style = if shape == "sm-circ" {
        ShapeStyle::Ink
    } else {
        ShapeStyle::InkLine
    };
    let mut items = vec![Item::Ellipse(EllipseItem {
        shape: Shape::plain(outer_style),
        cx: centre.x,
        cy: centre.y,
        rx: rect.w / 2,
        ry: rect.h / 2,
    })];
    if shape == "fr-circ" {
        let diameter = crate::r#gen::layoutconst::LAYOUT_CONST
            .iter()
            .find(|row| row.name == "vector.state.end_inner_size")
            .map(|row| row.value)
            .ok_or(LayoutError::Domain)?;
        if diameter <= 0 || diameter > rect.w || diameter > rect.h {
            return Err(LayoutError::Domain);
        }
        items.push(Item::Ellipse(EllipseItem {
            shape: Shape::plain(ShapeStyle::Ink),
            cx: centre.x,
            cy: centre.y,
            rx: diameter / 2,
            ry: diameter / 2,
        }));
    }
    Ok(items)
}

fn paint_regions(
    input: &Input,
    scene: &Scene,
    groups: &mut [crate::scene::Group],
) -> Result<(), LayoutError> {
    if input.region_sets.is_empty() {
        return Ok(());
    }
    let key = format!("{}.cluster_pad", input.profile.as_str());
    let inset = crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)?;
    for set in &input.region_sets {
        let parent = region_rect(input, scene, set.parent)?;
        for &region in &set.regions {
            let id = &input.groups.get(region).ok_or(LayoutError::Domain)?.id;
            let group = groups
                .iter_mut()
                .find(|group| group.role == GroupRole::Group && group.owner == *id)
                .ok_or(LayoutError::Domain)?;
            group.items.clear();
        }
        let parent_id = &input.groups.get(set.parent).ok_or(LayoutError::Domain)?.id;
        let group = groups
            .iter_mut()
            .find(|group| group.role == GroupRole::Group && group.owner == *parent_id)
            .ok_or(LayoutError::Domain)?;
        let insertion = group
            .items
            .iter()
            .position(|item| !matches!(item.class(), crate::scene::ItemClass::Shape))
            .unwrap_or(group.items.len());
        for (offset, pair) in set.regions.windows(2).enumerate() {
            let a = region_rect(input, scene, pair[0])?;
            let b = region_rect(input, scene, pair[1])?;
            let points = separator(parent, a, b, inset)?;
            let mut shape = Shape::plain(ShapeStyle::Rule);
            shape.line = Line::Dashed;
            group.items.insert(
                insertion + offset,
                Item::Polyline(PolylineItem {
                    shape,
                    points: points.to_vec(),
                    corner: 0,
                }),
            );
        }
    }
    Ok(())
}

fn region_rect(input: &Input, scene: &Scene, index: usize) -> Result<Rect, LayoutError> {
    let id = &input.groups.get(index).ok_or(LayoutError::Domain)?.id;
    scene
        .boxes()
        .iter()
        .find(|bounds| bounds.id == *id)
        .map(|bounds| bounds.rect)
        .ok_or(LayoutError::Domain)
}

fn separator(parent: Rect, a: Rect, b: Rect, inset: i32) -> Result<[Point; 2], LayoutError> {
    let edge = |origin: i32, size: i32| origin.checked_add(size).ok_or(LayoutError::Overflow);
    let midpoint = |lo: i32, hi: i32| {
        i32::try_from((i64::from(lo) + i64::from(hi)).div_euclid(2))
            .map_err(|_| LayoutError::Overflow)
    };
    let ar = edge(a.x, a.w)?;
    let br = edge(b.x, b.w)?;
    let ab = edge(a.y, a.h)?;
    let bb = edge(b.y, b.h)?;
    let left = edge(parent.x, inset)?.max(a.x.min(b.x));
    let top = edge(parent.y, inset)?.max(a.y.min(b.y));
    let right = edge(parent.x, parent.w)?
        .checked_sub(inset)
        .ok_or(LayoutError::Overflow)?
        .min(ar.max(br));
    let bottom = edge(parent.y, parent.h)?
        .checked_sub(inset)
        .ok_or(LayoutError::Overflow)?
        .min(ab.max(bb));
    if inset < 0 || left > right || top > bottom || a.w <= 0 || a.h <= 0 || b.w <= 0 || b.h <= 0 {
        return Err(LayoutError::Domain);
    }
    if ar <= b.x || br <= a.x {
        let x = if ar <= b.x {
            midpoint(ar, b.x)?
        } else {
            midpoint(br, a.x)?
        };
        if x < left || x > right {
            return Err(LayoutError::Domain);
        }
        return Ok([Point { x, y: top }, Point { x, y: bottom }]);
    }
    if ab <= b.y || bb <= a.y {
        let y = if ab <= b.y {
            midpoint(ab, b.y)?
        } else {
            midpoint(bb, a.y)?
        };
        if y < top || y > bottom {
            return Err(LayoutError::Domain);
        }
        return Ok([Point { x: left, y }, Point { x: right, y }]);
    }
    Err(LayoutError::Domain)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dividers_cover_only_region_bodies_inside_parent_padding() -> Result<(), LayoutError> {
        let parent = Rect {
            x: 0,
            y: 0,
            w: 40,
            h: 30,
        };
        let cases = [
            (
                Rect {
                    x: 4,
                    y: 7,
                    w: 10,
                    h: 10,
                },
                Rect {
                    x: 22,
                    y: 9,
                    w: 12,
                    h: 8,
                },
                [Point { x: 18, y: 7 }, Point { x: 18, y: 17 }],
            ),
            (
                Rect {
                    x: 5,
                    y: 5,
                    w: 10,
                    h: 5,
                },
                Rect {
                    x: 7,
                    y: 20,
                    w: 14,
                    h: 5,
                },
                [Point { x: 5, y: 15 }, Point { x: 21, y: 15 }],
            ),
            (
                Rect {
                    x: 4,
                    y: 0,
                    w: 10,
                    h: 30,
                },
                Rect {
                    x: 22,
                    y: 1,
                    w: 12,
                    h: 28,
                },
                [Point { x: 18, y: 2 }, Point { x: 18, y: 28 }],
            ),
            (
                Rect {
                    x: 0,
                    y: 5,
                    w: 40,
                    h: 5,
                },
                Rect {
                    x: 1,
                    y: 20,
                    w: 38,
                    h: 5,
                },
                [Point { x: 2, y: 15 }, Point { x: 38, y: 15 }],
            ),
        ];
        for (a, b, expected) in cases {
            assert_eq!(separator(parent, a, b, 2)?, expected);
            assert_eq!(separator(parent, b, a, 2)?, expected);
        }
        Ok(())
    }

    #[test]
    fn dividers_reject_overflow_and_midpoints_outside_the_parent() {
        let parent = Rect {
            x: 0,
            y: 0,
            w: 40,
            h: 30,
        };
        let left = Rect {
            x: -20,
            y: 7,
            w: 10,
            h: 10,
        };
        let right = Rect {
            x: -5,
            y: 9,
            w: 10,
            h: 8,
        };
        assert_eq!(separator(parent, left, right, 2), Err(LayoutError::Domain));
        let above = Rect {
            x: 5,
            y: -20,
            w: 10,
            h: 10,
        };
        let below = Rect {
            x: 7,
            y: -5,
            w: 14,
            h: 10,
        };
        assert_eq!(separator(parent, above, below, 2), Err(LayoutError::Domain));
        let overflow = Rect {
            x: i32::MAX,
            ..parent
        };
        assert_eq!(
            separator(overflow, left, right, 2),
            Err(LayoutError::Overflow)
        );
    }
}
