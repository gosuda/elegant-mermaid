use super::input::{Box, Group, Input, Label, Route, SizeRule};
use crate::{
    geom::GeomError,
    model::c4::{Declaration, Field, Model},
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
};

pub fn from_c4(model: &Model, profile: Profile, options: DumpOptions) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "c4",
        profile,
        direction: Direction::from_token(&model.direction).unwrap_or_default(),
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: super::input::Spacing::default(),
    };
    let boundary_ids = boundary_ids(model);
    for declaration in &model.declarations {
        append_declaration(&mut input, model, *declaration, &boundary_ids);
    }
    input.labels.extend(
        input
            .boxes
            .iter()
            .filter(|node| node.text != node.id)
            .map(|node| Label {
                id: format!("{}.label", node.id),
                owner: node.id.clone(),
                role: TextRole::Label,
                text: node.text.clone(),
            }),
    );
    append_relations(&mut input, model, &boundary_ids);
    Ok(input)
}

fn boundary_ids(model: &Model) -> Vec<String> {
    let mut reserved = model
        .elements
        .iter()
        .map(|element| element.id.clone())
        .chain(model.boundaries.iter().map(|boundary| boundary.id.clone()))
        .collect::<std::collections::BTreeSet<_>>();
    let mut ids = Vec::with_capacity(model.boundaries.len());
    let mut next = 0usize;
    for boundary in &model.boundaries {
        let id = if model
            .elements
            .iter()
            .any(|element| element.id == boundary.id)
        {
            generated_boundary_id(&mut reserved, &mut next)
        } else {
            boundary.id.clone()
        };
        ids.push(id);
    }
    ids
}

fn generated_boundary_id(
    reserved: &mut std::collections::BTreeSet<String>,
    next: &mut usize,
) -> String {
    loop {
        let id = format!("c4group{next}");
        *next += 1;
        if reserved.insert(id.clone()) {
            return id;
        }
    }
}

fn parent_id(model: &Model, ids: &[String], parent: &str) -> String {
    model
        .boundaries
        .iter()
        .position(|boundary| boundary.id == parent)
        .and_then(|index| ids.get(index))
        .cloned()
        .unwrap_or_default()
}

fn append_declaration(input: &mut Input, model: &Model, declaration: Declaration, ids: &[String]) {
    match declaration {
        Declaration::Element(index) => {
            let Some(element) = model.elements.get(index) else {
                return;
            };
            input.boxes.push(Box {
                id: element.id.clone(),
                role: BoxRole::Node,
                shape: shape(&element.kind).into(),
                icon: false,
                parent: parent_id(model, ids, &element.parent),
                exclusive: true,
                text: display_text(&element.label.value, &element.fields),
                direction: String::new(),
            });
            input.sizes.push(SizeRule::Measured);
        }
        Declaration::Boundary(index) => append_boundary(input, model, index, ids),
    }
}

fn append_boundary(input: &mut Input, model: &Model, index: usize, ids: &[String]) {
    let Some(boundary) = model.boundaries.get(index) else {
        return;
    };
    let Some(id) = ids.get(index) else {
        return;
    };
    let parent = parent_id(model, ids, &boundary.parent);
    input.boxes.push(Box {
        id: id.clone(),
        role: BoxRole::Group,
        shape: String::new(),
        icon: false,
        parent: parent.clone(),
        exclusive: false,
        text: display_text(&boundary.label.value, &boundary.fields),
        direction: String::new(),
    });
    input.sizes.push(SizeRule::Measured);
    input.groups.push(Group {
        id: id.clone(),
        parent,
        direction: String::new(),
        direction_span: boundary.macro_span,
    });
}

fn shape(kind: &str) -> &'static str {
    if matches!(kind, "person" | "external_person") {
        return "person";
    }
    if kind.ends_with("_db") {
        return "cyl";
    }
    "rect"
}

fn display_text(label: &str, fields: &[Field]) -> String {
    let mut lines = vec![label];
    for name in ["type", "techn", "descr"] {
        if let Some(field) = fields
            .iter()
            .find(|field| field.name == name && !field.value.value.is_empty())
        {
            lines.push(&field.value.value);
        }
    }
    lines.join("<br/>")
}

fn endpoint(model: &Model, ids: &[String], alias: &str) -> Option<String> {
    if model.elements.iter().any(|element| element.id == alias) {
        return Some(alias.into());
    }
    model
        .boundaries
        .iter()
        .position(|boundary| boundary.id == alias)
        .and_then(|index| ids.get(index))
        .cloned()
}

fn append_relations(input: &mut Input, model: &Model, ids: &[String]) {
    let mut next = 0usize;
    for relation in &model.relations {
        let Some(from) = endpoint(model, ids, &relation.from.value) else {
            continue;
        };
        let Some(to) = endpoint(model, ids, &relation.to.value) else {
            continue;
        };
        let id = route_id(&input.boxes, &mut next);
        let text = display_text(&relation.label.value, &relation.fields);
        if !text.is_empty() {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text,
            });
        }
        input.routes.push(Route {
            id,
            from,
            to,
            orthogonal: true,
            marker_start: if matches!(relation.macro_name.as_str(), "BiRel" | "Rel_Back") {
                "point"
            } else {
                "none"
            }
            .into(),
            marker_end: if matches!(relation.macro_name.as_str(), "Rel_Back") {
                "none"
            } else {
                "point"
            }
            .into(),
            line: "normal".into(),
            min_length: 1,
            from_side: relation_sides(&relation.macro_name).map(|sides| sides.0),
            to_side: relation_sides(&relation.macro_name).map(|sides| sides.1),
        });
    }
}

fn relation_sides(name: &str) -> Option<(super::input::RouteSide, super::input::RouteSide)> {
    use super::input::RouteSide::{Down, Left, Right, Up};
    match name {
        "Rel_Up" | "Rel_U" => Some((Up, Down)),
        "Rel_Down" | "Rel_D" => Some((Down, Up)),
        "Rel_Left" | "Rel_L" => Some((Left, Right)),
        "Rel_Right" | "Rel_R" => Some((Right, Left)),
        _ => None,
    }
}

fn route_id(boxes: &[Box], next: &mut usize) -> String {
    loop {
        let id = format!("e{next}");
        *next += 1;
        if !boxes.iter().any(|node| node.id == id) {
            return id;
        }
    }
}

pub fn layout(input: &Input) -> Result<(crate::scene::Scene, bool), super::layered::LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| super::layered::pipeline::EdgeOptions {
            marker_start: marker(&route.marker_start),
            marker_end: marker(&route.marker_end),
            stroke: &route.line,
            min_length: 1,
        })
        .collect::<Vec<_>>();
    let (scene, budget) = super::layered::pipeline::layout_family(input, &edges)?;
    let scene = super::layered::pipeline::reroute_endpoints(input, scene, &edges)?;
    Ok((shape_scene(input, scene)?, budget))
}

fn marker(name: &str) -> Option<crate::scene::MarkerName> {
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == name)
        .and_then(|row| crate::scene::MarkerName::new(row.name))
}

fn shape_scene(
    input: &Input,
    scene: crate::scene::Scene,
) -> Result<crate::scene::Scene, super::layered::LayoutError> {
    use crate::scene::ItemClass;
    let mut groups = scene.items().to_vec();
    for group in &mut groups {
        let Some(node) = input
            .boxes
            .iter()
            .find(|node| node.id == group.owner && matches!(node.role, BoxRole::Node))
        else {
            continue;
        };
        if node.shape == "rect" {
            continue;
        }
        let Some(bounds) = scene.boxes().iter().find(|bounds| bounds.id == node.id) else {
            continue;
        };
        let gap = text_top_gap(&group.items, bounds.rect.y);
        let mut shapes = match node.shape.as_str() {
            "person" => person_outline(bounds.rect, input.profile, gap)?,
            "cyl" => cylinder_outline(bounds.rect, input.profile, gap)?,
            _ => continue,
        };
        shapes.extend(
            group
                .items
                .drain(..)
                .filter(|item| item.class() != ItemClass::Shape),
        );
        group.items = shapes;
    }
    Ok(crate::scene::Scene::new(
        scene.canvas(),
        scene.dump_part().clone(),
        groups,
    ))
}

fn text_top_gap(items: &[crate::scene::Item], top: i32) -> i64 {
    items
        .iter()
        .filter_map(|item| match item {
            crate::scene::Item::Text(text) => Some(i64::from(text.rect.y) - i64::from(top)),
            _ => None,
        })
        .min()
        .unwrap_or(0)
        .max(0)
}

fn coordinate(value: i64) -> Result<i32, super::layered::LayoutError> {
    i32::try_from(value).map_err(|_| super::layered::LayoutError::Overflow)
}

fn person_outline(
    rect: crate::geom::Rect,
    profile: Profile,
    gap: i64,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let width = i64::from(rect.w);
    let height = i64::from(rect.h);
    let radius = (width * 23 / 100)
        .clamp(16 * 64, 56 * 64)
        .min(width / 2)
        .min(height / 2)
        .min(gap / 2)
        .max(0);
    let offset = radius * 173 / 100;
    let body_height = height - offset;
    let body_radius = (width * 177 / 1000).min(body_height * 45 / 100);
    let shape = Shape::plain(ShapeStyle::Node);
    Ok(vec![
        Item::RoundRect(RoundRectItem {
            shape,
            rect: crate::geom::Rect {
                y: coordinate(i64::from(rect.y) + offset)?,
                h: coordinate(body_height)?,
                ..rect
            },
            r: if profile == Profile::Cell {
                0
            } else {
                coordinate(body_radius)?
            },
        }),
        Item::Ellipse(EllipseItem {
            shape,
            cx: coordinate(i64::from(rect.x) + width / 2)?,
            cy: coordinate(i64::from(rect.y) + radius)?,
            rx: coordinate(radius)?,
            ry: coordinate(radius)?,
        }),
    ])
}

pub(crate) fn cylinder_outline(
    rect: crate::geom::Rect,
    profile: Profile,
    gap: i64,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let width = i64::from(rect.w);
    let height = i64::from(rect.h);
    let radius = (width * 1600 / (8000 + width))
        .min(height / 4)
        .min(gap / 2)
        .max(0);
    let shape = Shape::plain(ShapeStyle::Node);
    let outer = if profile == Profile::Cell {
        Item::RoundRect(RoundRectItem { shape, rect, r: 0 })
    } else {
        cylinder_path(rect, radius)?
    };
    let rx = if profile == Profile::Cell {
        (width - 1).max(0) / 2
    } else {
        width / 2
    };
    let mut items = vec![
        outer,
        Item::Ellipse(EllipseItem {
            shape,
            cx: coordinate(i64::from(rect.x) + width / 2)?,
            cy: coordinate(i64::from(rect.y) + radius)?,
            rx: coordinate(rx)?,
            ry: coordinate(radius)?,
        }),
    ];
    if profile == Profile::Cell {
        items.push(Item::SymbolRef(SymbolRefItem {
            symbol: SymbolName::new("database").ok_or(super::layered::LayoutError::Domain)?,
            at: outline_point(i64::from(rect.x) + width / 2, i64::from(rect.y))?,
            style: ShapeStyle::Node,
        }));
    }
    Ok(items)
}

fn outline_point(x: i64, y: i64) -> Result<crate::geom::Point, super::layered::LayoutError> {
    Ok(crate::geom::Point {
        x: coordinate(x)?,
        y: coordinate(y)?,
    })
}

fn cylinder_path(
    rect: crate::geom::Rect,
    radius: i64,
) -> Result<crate::scene::Item, super::layered::LayoutError> {
    use crate::scene::*;
    let left = i64::from(rect.x);
    let right = left + i64::from(rect.w);
    let top = i64::from(rect.y);
    let bottom = top + i64::from(rect.h);
    let centre = left + i64::from(rect.w) / 2;
    let dx = i64::from(rect.w) * 552 / 2000;
    let dy = radius * 552 / 1000;
    let commands = vec![
        PathCommand::Move(outline_point(left, top + radius)?),
        PathCommand::Line(outline_point(left, bottom - radius)?),
        PathCommand::Curve {
            c1: outline_point(left, bottom - radius + dy)?,
            c2: outline_point(centre - dx, bottom)?,
            to: outline_point(centre, bottom)?,
        },
        PathCommand::Curve {
            c1: outline_point(centre + dx, bottom)?,
            c2: outline_point(right, bottom - radius + dy)?,
            to: outline_point(right, bottom - radius)?,
        },
        PathCommand::Line(outline_point(right, top + radius)?),
        PathCommand::Curve {
            c1: outline_point(right, top + radius - dy)?,
            c2: outline_point(centre + dx, top)?,
            to: outline_point(centre, top)?,
        },
        PathCommand::Curve {
            c1: outline_point(centre - dx, top)?,
            c2: outline_point(left, top + radius - dy)?,
            to: outline_point(left, top + radius)?,
        },
        PathCommand::Close,
    ];
    Ok(Item::Path(PathItem {
        shape: Shape::plain(ShapeStyle::Node),
        commands,
    }))
}

#[cfg(test)]
mod tests;
