use super::input::{Box, Group, Input, Label, Route, SizeRule, Spacing};
use crate::{
    geom::{GeomError, Size},
    model::agentflow::{Declaration, Model},
    scene::{BoxRole, Direction, DumpOptions, Profile, TextRole},
};

pub fn from_agentflow(
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "agentflow",
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
        spacing: Spacing::for_kind(profile, "agentflow"),
    };
    for declaration in &model.declarations {
        match declaration {
            Declaration::Node(index) => append_node(&mut input, model, *index)?,
            Declaration::Group(index) => append_group(&mut input, model, *index)?,
        }
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
    append_edges(&mut input, model)?;
    Ok(input)
}
fn append_node(input: &mut Input, model: &Model, index: usize) -> Result<(), GeomError> {
    let Some(node) = model.nodes.get(index) else {
        return Ok(());
    };
    let (text, size) = content(&node.label, model.padding, input)?;
    input.boxes.push(Box {
        id: node.id.clone(),
        role: BoxRole::Node,
        shape: node.shape.clone(),
        icon: false,
        parent: node.parent.clone(),
        exclusive: true,
        text,
        direction: String::new(),
    });
    input.sizes.push(SizeRule::Content(size));
    Ok(())
}
fn append_group(input: &mut Input, model: &Model, index: usize) -> Result<(), GeomError> {
    let Some(group) = model.groups.get(index) else {
        return Ok(());
    };
    if hidden_group(model, &group.parent) {
        return Ok(());
    }
    let collapsed = group.appearance.metadata.iter().any(|entry| entry.key == "view" && matches!(&entry.value, crate::syntax::config_value::ConfigValue::String(value) if value == "collapsed"));
    let (text, mut size) = content(&group.title, model.padding, input)?;
    input.boxes.push(Box {
        id: group.id.clone(),
        role: if collapsed {
            BoxRole::Node
        } else {
            BoxRole::Group
        },
        shape: if collapsed { "collapsedGroup" } else { "" }.into(),
        icon: false,
        parent: group.parent.clone(),
        exclusive: collapsed,
        text,
        direction: group.direction.clone(),
    });
    if collapsed {
        let (_, pad_y) = padding_units(model.padding, input.profile)?;
        size.h = size
            .h
            .checked_add(line_height(input.profile))
            .and_then(|height| height.checked_add(pad_y))
            .ok_or(GeomError::Overflow)?;
    }
    input.sizes.push(if collapsed {
        SizeRule::Content(size)
    } else {
        SizeRule::Measured
    });
    if !collapsed {
        input.groups.push(Group {
            id: group.id.clone(),
            parent: group.parent.clone(),
            direction: group.direction.clone(),
            direction_span: group.direction_span,
        });
    }
    Ok(())
}
fn hidden_group(model: &Model, parent: &str) -> bool {
    let mut ancestor = parent;
    while let Some(group) = model.groups.iter().find(|g| g.id == ancestor) {
        if group.appearance.metadata.iter().any(|entry| entry.key == "view" && matches!(&entry.value, crate::syntax::config_value::ConfigValue::String(value) if value == "collapsed")) { return true; }
        ancestor = &group.parent;
    }
    false
}
fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.agentflow.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}
fn measured(text: &str, input: &Input) -> Result<(i32, i32), GeomError> {
    let profile = input.profile;
    let metric = crate::scene::configured_metric(metric(profile), &input.options.config);
    let lines =
        crate::measure::styled_lines(text, constant(profile, "wrapping_width")?, metric)?;
    let width = lines.iter().map(|line| line.width).max().unwrap_or(0);
    let count = i32::try_from(lines.len()).map_err(|_| GeomError::Overflow)?;
    let height = count
        .checked_mul(line_height(profile))
        .ok_or(GeomError::Overflow)?;
    Ok((width, height))
}
fn metric(profile: Profile) -> crate::measure::Metric {
    if profile == Profile::Cell {
        crate::measure::Metric::cell()
    } else {
        crate::measure::Metric::for_role(crate::measure::Role::Label)
    }
}
fn content(
    text: &str,
    padding: Option<i32>,
    input: &Input,
) -> Result<(String, Size), GeomError> {
    let profile = input.profile;
    let (width, height) = measured(text, input)?;
    let (pad_x, pad_y) = padding_units(padding, profile)?;
    let width = width
        .checked_add(pad_x.checked_mul(2).ok_or(GeomError::Overflow)?)
        .ok_or(GeomError::Overflow)?;
    let height = height
        .checked_add(pad_y.checked_mul(2).ok_or(GeomError::Overflow)?)
        .ok_or(GeomError::Overflow)?;
    Ok((
        text.to_string(),
        Size {
            w: width.max(constant(profile, "min_node_width")?),
            h: height,
        },
    ))
}
fn padding_units(padding: Option<i32>, profile: Profile) -> Result<(i32, i32), GeomError> {
    let Some(padding) = padding else {
        let padding = constant(profile, "padding")?;
        return Ok((padding, padding));
    };
    if padding < 0 {
        return Err(GeomError::Domain);
    }
    if profile == Profile::Vector {
        let padding = padding.checked_mul(64).ok_or(GeomError::Overflow)?;
        return Ok((padding, padding));
    }
    let x = i32::try_from(crate::measure::ceil_div(i64::from(padding), 8))
        .map_err(|_| GeomError::Overflow)?
        .max(1);
    let y = i32::try_from(crate::measure::ceil_div(i64::from(padding), 16))
        .map_err(|_| GeomError::Overflow)?
        .max(1);
    Ok((x, y))
}
fn append_edges(input: &mut Input, model: &Model) -> Result<(), GeomError> {
    let mut next = 0usize;
    for edge in &model.edges {
        if edge.line == "invisible"
            || !input.boxes.iter().any(|b| b.id == edge.from)
            || !input.boxes.iter().any(|b| b.id == edge.to)
        {
            continue;
        }
        let id = route_id(&input.boxes, &mut next);
        if !edge.label.is_empty() {
            input.labels.push(Label {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: edge.label.clone(),
            });
        }
        input.routes.push(Route {
            id,
            from: edge.from.clone(),
            to: edge.to.clone(),
            orthogonal: true,
            marker_start: "none".into(),
            marker_end: edge.marker.clone(),
            line: edge.line.clone(),
            min_length: edge.length.max(if edge.label.is_empty() { 1 } else { 2 }),
            from_side: None,
            to_side: None,
        });
    }
    Ok(())
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
        .map(|route| {
            Ok(super::layered::pipeline::EdgeOptions {
                marker_start: marker(&route.marker_start),
                marker_end: marker(&route.marker_end),
                stroke: &route.line,
                min_length: i32::try_from(route.min_length)
                    .map_err(|_| super::layered::LayoutError::Overflow)?,
            })
        })
        .collect::<Result<Vec<_>, super::layered::LayoutError>>()?;
    let (scene, budget) = super::layered::pipeline::layout_family(input, &edges)?;
    Ok((shape_scene(input, scene)?, budget))
}
fn marker(name: &str) -> Option<crate::scene::MarkerName> {
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == name)
        .and_then(|row| crate::scene::MarkerName::new(row.name))
}
fn line_height(profile: Profile) -> i32 {
    if profile == Profile::Cell {
        1
    } else {
        crate::measure::Role::Label.line_height_px() * 64
    }
}
fn shape_scene(
    input: &Input,
    scene: crate::scene::Scene,
) -> Result<crate::scene::Scene, super::layered::LayoutError> {
    let mut groups = scene.items().to_vec();
    for group in &mut groups {
        let Some(node) = input
            .boxes
            .iter()
            .find(|node| node.id == group.owner && matches!(node.role, BoxRole::Node))
        else {
            continue;
        };
        let Some(bounds) = scene.boxes().iter().find(|bounds| bounds.id == node.id) else {
            continue;
        };
        let mut shapes = outline(&node.shape, bounds.rect, input.profile)?;
        for item in group
            .items
            .iter()
            .filter(|item| matches!(item, crate::scene::Item::Text(_)))
        {
            let mut item = item.clone();
            if node.shape == "collapsedGroup"
                && let crate::scene::Item::Text(text) = &mut item
            {
                let padding = constant(input.profile, "padding")
                    .map_err(|_| super::layered::LayoutError::Domain)?;
                text.rect.y = text
                    .rect
                    .y
                    .checked_sub((line_height(input.profile) + padding) / 2)
                    .ok_or(super::layered::LayoutError::Overflow)?;
            }
            shapes.push(item);
        }
        group.items = shapes;
    }
    Ok(crate::scene::Scene::new(
        scene.canvas(),
        scene.dump_part().clone(),
        groups,
    ))
}
fn outline(
    name: &str,
    rect: crate::geom::Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let shape = Shape::plain(ShapeStyle::Node);
    let right = rect
        .x
        .checked_add(rect.w)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let bottom = rect
        .y
        .checked_add(rect.h)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let centre = crate::geom::Point {
        x: rect.x + rect.w / 2,
        y: rect.y + rect.h / 2,
    };
    let polygon = |points| vec![Item::Polygon(PolygonItem { shape, points })];
    let point = |x, y| crate::geom::Point { x, y };
    match name {
        "diamond" => Ok(polygon(vec![
            point(centre.x, rect.y),
            point(right, centre.y),
            point(centre.x, bottom),
            point(rect.x, centre.y),
        ])),
        "hexagon" | "hex" => {
            let inset = (rect.h / 4).min(rect.w / 4);
            Ok(polygon(vec![
                point(rect.x + inset, rect.y),
                point(right - inset, rect.y),
                point(right, centre.y),
                point(right - inset, bottom),
                point(rect.x + inset, bottom),
                point(rect.x, centre.y),
            ]))
        }
        "lean-right" => {
            let inset = (rect.h / 2).min(rect.w / 3);
            Ok(polygon(vec![
                point(rect.x + inset, rect.y),
                point(right, rect.y),
                point(right - inset, bottom),
                point(rect.x, bottom),
            ]))
        }
        "subroutine" | "subprocess" | "subproc" | "framed-rectangle" => framed(rect, profile),
        "lin-doc" | "lined-document" => document_outline(rect),
        "connector" => Ok(vec![Item::Ellipse(EllipseItem {
            shape,
            cx: centre.x,
            cy: centre.y,
            rx: rect.w / 2,
            ry: rect.h / 2,
        })]),
        _ => rounded_outline(name, rect, profile),
    }
}
fn framed(
    rect: crate::geom::Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let inset = constant(profile, "padding")
        .map_err(|_| super::layered::LayoutError::Domain)?
        .min(rect.w / 3);
    let right = rect
        .x
        .checked_add(rect.w)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let bottom = rect
        .y
        .checked_add(rect.h)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let mut items = vec![Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect,
    })];
    for x in [rect.x + inset, right - inset] {
        items.push(Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: vec![
                crate::geom::Point { x, y: rect.y },
                crate::geom::Point { x, y: bottom },
            ],
            corner: 0,
        }));
    }
    Ok(items)
}
fn document_outline(
    rect: crate::geom::Rect,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::{geom::Point, scene::*};
    let right = rect
        .x
        .checked_add(rect.w)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let bottom = rect
        .y
        .checked_add(rect.h)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let amplitude = rect.h / 8;
    let baseline = bottom - amplitude;
    let mut points = vec![
        Point {
            x: rect.x,
            y: rect.y,
        },
        Point {
            x: rect.x,
            y: baseline,
        },
    ];
    for index in 0i64..=32 {
        let x = i32::try_from(
            i64::from(rect.x) + crate::geom::floor_div(i64::from(rect.w) * index, 32),
        )
        .map_err(|_| super::layered::LayoutError::Overflow)?;
        let angle =
            i32::try_from(index * 2048).map_err(|_| super::layered::LayoutError::Overflow)?;
        let y = i32::try_from(
            i64::from(baseline)
                + crate::geom::floor_div(
                    i64::from(amplitude) * i64::from(crate::geom::sin_q15(angle)),
                    32768,
                ),
        )
        .map_err(|_| super::layered::LayoutError::Overflow)?;
        points.push(Point { x, y });
    }
    points.push(Point {
        x: right,
        y: rect.y,
    });
    let line_x = rect.x + rect.w / 22;
    Ok(vec![
        Item::Polygon(PolygonItem {
            shape: Shape::plain(ShapeStyle::Node),
            points,
        }),
        Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: vec![
                Point {
                    x: line_x,
                    y: rect.y,
                },
                Point {
                    x: line_x,
                    y: baseline,
                },
            ],
            corner: 0,
        }),
    ])
}
fn rounded_outline(
    name: &str,
    rect: crate::geom::Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::scene::*;
    let key = format!("{}.corner_radius", profile.as_str());
    let radius = crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(super::layered::LayoutError::Domain)?;
    let style = if name == "collapsedGroup" {
        ShapeStyle::Group
    } else {
        ShapeStyle::Node
    };
    let mut items = vec![Item::RoundRect(RoundRectItem {
        shape: Shape::plain(style),
        rect,
        r: radius,
    })];
    if name == "collapsedGroup" {
        items.extend(collapsed_indicator(rect, profile)?);
    }
    Ok(items)
}
fn collapsed_indicator(
    rect: crate::geom::Rect,
    profile: Profile,
) -> Result<Vec<crate::scene::Item>, super::layered::LayoutError> {
    use crate::{geom::Point, scene::*};
    let padding = constant(profile, "padding").map_err(|_| super::layered::LayoutError::Domain)?;
    let bottom = rect
        .y
        .checked_add(rect.h)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let right = rect
        .x
        .checked_add(rect.w)
        .ok_or(super::layered::LayoutError::Overflow)?;
    let y = bottom - padding - 2 * line_height(profile);
    let mut items = vec![Item::Polyline(PolylineItem {
        shape: Shape::plain(ShapeStyle::Rule).with_line(Line::Dotted),
        points: vec![
            Point {
                x: rect.x + padding,
                y,
            },
            Point {
                x: right - padding,
                y,
            },
        ],
        corner: 0,
    })];
    let centre = rect.x + rect.w / 2;
    for offset in [-padding, 0, padding] {
        let cy = y + line_height(profile);
        if profile == Profile::Cell {
            let symbol = SymbolName::new("disc").ok_or(super::layered::LayoutError::Domain)?;
            items.push(Item::SymbolRef(SymbolRefItem {
                symbol,
                at: Point {
                    x: centre + offset,
                    y: cy,
                },
                style: ShapeStyle::Ink,
            }));
        } else {
            let radius = padding * 5 / 16;
            items.push(Item::Ellipse(EllipseItem {
                shape: Shape::plain(ShapeStyle::Ink),
                cx: centre + offset,
                cy,
                rx: radius,
                ry: radius,
            }));
        }
    }
    Ok(items)
}
#[cfg(test)]
mod tests;
