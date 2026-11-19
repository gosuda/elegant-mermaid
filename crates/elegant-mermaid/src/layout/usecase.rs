use super::input::{Box, Group, Input, Label, Route, SizeRule, Spacing};
use super::layered::LayoutError;
use crate::{
    geom::{GeomError, Point, Rect, Size, floor_div},
    measure::{Metric, Role, StyledLine},
    model::usecase::{Json, Kind, Model, Node},
    scene::{self, BoxRole, Direction, DumpOptions, Profile, TextRole},
};

pub fn from_usecase(
    model: &Model,
    profile: Profile,
    options: DumpOptions,
) -> Result<Input, GeomError> {
    let mut input = Input {
        kind: "usecase",
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
        spacing: Spacing::for_kind(profile, "usecase"),
    };
    append_boxes(&mut input, model)?;
    for node in &input.boxes {
        if node.text != node.id {
            input.labels.push(Label {
                id: format!("{}.label", node.id),
                owner: node.id.clone(),
                role: TextRole::Label,
                text: node.text.clone(),
            });
        }
    }
    append_routes(&mut input, model)?;
    Ok(input)
}
fn append_boxes(input: &mut Input, model: &Model) -> Result<(), GeomError> {
    let mut notes = model.notes.iter().peekable();
    for node in &model.nodes {
        while notes
            .peek()
            .is_some_and(|note| note.span.start < node.first_span.start)
        {
            if let Some(note) = notes.next() {
                append_note(input, model, note)?;
            }
        }
        append_node(input, node)?;
    }
    for note in notes {
        append_note(input, model, note)?;
    }
    Ok(())
}
fn append_note(
    input: &mut Input,
    model: &Model,
    note: &crate::model::usecase::Note,
) -> Result<(), GeomError> {
    let parent = model
        .nodes
        .iter()
        .find(|node| node.id == note.target)
        .map_or("", |node| node.parent.as_str());
    input.boxes.push(Box {
        id: note.id.clone(),
        role: BoxRole::Node,
        shape: "note".into(),
        icon: false,
        parent: parent.into(),
        exclusive: true,
        text: note.text.clone(),
        direction: String::new(),
    });
    input.sizes.push(SizeRule::Measured);
    Ok(())
}
fn append_node(input: &mut Input, node: &Node) -> Result<(), GeomError> {
    let text = display(node);
    let size = node_size(node, &lines(&text, input.profile)?, input.profile)?;
    let boundary = node.kind == Kind::Boundary;
    input.boxes.push(Box {
        id: node.id.clone(),
        role: if boundary {
            BoxRole::Group
        } else {
            BoxRole::Node
        },
        shape: encoded_shape(node),
        icon: false,
        parent: node.parent.clone(),
        exclusive: !boundary,
        text,
        direction: String::new(),
    });
    input.sizes.push(size);
    if boundary {
        input.groups.push(Group {
            id: node.id.clone(),
            parent: node.parent.clone(),
            direction: String::new(),
            direction_span: node.span,
        });
    }
    Ok(())
}
fn encoded_shape(node: &Node) -> String {
    match node.kind {
        Kind::Actor => actor_shape(node),
        Kind::Usecase if node.business => "usecaseBusiness".into(),
        Kind::Boundary if node.boundary_type == "package" => "rect:package".into(),
        _ => node.shape.clone(),
    }
}
fn actor_shape(node: &Node) -> String {
    if !node.icon.is_empty() {
        let flag = if node.business { "business" } else { "icon" };
        return format!("usecaseActorIcon:{flag}:{}", node.icon);
    }
    let base = match node.actor_type.as_str() {
        "hollow" => "usecaseActorHollow",
        "awesome" => "usecaseActorAwesome",
        _ => "usecaseActor",
    };
    if node.business {
        format!("{base}:business")
    } else {
        base.into()
    }
}
fn display(node: &Node) -> String {
    let label = node
        .json
        .as_ref()
        .map_or_else(|| node.label.clone(), json_text);
    if node.stereotype.is_empty() {
        return label;
    }
    format!("«{}»<br/>{label}", node.stereotype)
}
fn node_size(
    node: &Node,
    lines: &[StyledLine<'_>],
    profile: Profile,
) -> Result<SizeRule, GeomError> {
    let width = lines.iter().map(|line| line.width).max().unwrap_or(0);
    let count = i32::try_from(lines.len().max(1)).map_err(|_| GeomError::Overflow)?;
    let line_height = if profile == Profile::Cell {
        1
    } else {
        Role::Label.line_height_px() * 64
    };
    let height = count.checked_mul(line_height).ok_or(GeomError::Overflow)?;
    if node.kind == Kind::Actor {
        return actor_size(width, height, profile).map(SizeRule::Exact);
    }
    if node.kind != Kind::Usecase || node.shape != "usecaseEllipse" {
        return Ok(SizeRule::Measured);
    }
    let pad_x =
        profile_constant(profile, "node_pad_x")? + profile_constant(profile, "node_border")?;
    let pad_y =
        profile_constant(profile, "node_pad_y")? + profile_constant(profile, "node_border")?;
    Ok(SizeRule::Content(Size {
        w: width
            .checked_add(2 * pad_x)
            .ok_or(GeomError::Overflow)?
            .max(constant(profile, "min_node_width")?),
        h: height.checked_add(2 * pad_y).ok_or(GeomError::Overflow)?,
    }))
}
fn actor_size(width: i32, height: i32, profile: Profile) -> Result<Size, GeomError> {
    let (figure_w, figure_h, padding, gap) = match profile {
        Profile::Vector => (56 * 64, 72 * 64, 8 * 64, 8 * 64),
        Profile::Cell => (7, 5, 1, 1),
    };
    Ok(Size {
        w: width
            .max(figure_w)
            .checked_add(2 * padding)
            .ok_or(GeomError::Overflow)?,
        h: height
            .checked_add(figure_h + gap + 2 * padding)
            .ok_or(GeomError::Overflow)?,
    })
}
fn metric(profile: Profile) -> Metric {
    match profile {
        Profile::Cell => Metric::Cell,
        Profile::Vector => Metric::for_role(Role::Label),
    }
}
fn lines(text: &str, profile: Profile) -> Result<Vec<StyledLine<'_>>, GeomError> {
    crate::measure::styled_lines(text, constant(profile, "wrapping_width")?, metric(profile))
}
fn constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    profile_constant(profile, &format!("usecase.{name}"))
}
fn profile_constant(profile: Profile, name: &str) -> Result<i32, GeomError> {
    let key = format!("{}.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(GeomError::Domain)
}
fn route_id(input: &Input, next: &mut usize) -> String {
    loop {
        let id = format!("e{next}");
        *next += 1;
        if !input.boxes.iter().any(|node| node.id == id) {
            return id;
        }
    }
}
fn append_routes(input: &mut Input, model: &Model) -> Result<(), GeomError> {
    let mut next = 0;
    for edge in &model.relations {
        let id = route_id(input, &mut next);
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
            marker_start: edge.marker_start.clone(),
            marker_end: edge.marker_end.clone(),
            line: if matches!(edge.kind.as_str(), "include" | "extend") {
                "dotted"
            } else {
                "normal"
            }
            .into(),
            min_length: edge.min_length,
            from_side: None,
            to_side: None,
        });
    }
    for note in &model.notes {
        let id = route_id(input, &mut next);
        input.routes.push(Route {
            id,
            from: note.id.clone(),
            to: note.target.clone(),
            orthogonal: true,
            marker_start: "none".into(),
            marker_end: "none".into(),
            line: "normal".into(),
            min_length: 1,
            from_side: None,
            to_side: None,
        });
    }
    Ok(())
}
pub fn layout(input: &Input) -> Result<(scene::Scene, bool), LayoutError> {
    let edges = input
        .routes
        .iter()
        .map(|route| {
            Ok(super::layered::pipeline::EdgeOptions {
                marker_start: marker(&route.marker_start),
                marker_end: marker(&route.marker_end),
                stroke: &route.line,
                min_length: i32::try_from(route.min_length).map_err(|_| LayoutError::Overflow)?,
            })
        })
        .collect::<Result<Vec<_>, LayoutError>>()?;
    let (scene, budget) = super::layered::pipeline::layout_family(input, &edges)?;
    Ok((draw_shapes(input, scene)?, budget))
}
fn marker(name: &str) -> Option<scene::MarkerName> {
    crate::r#gen::markers::MARKERS
        .iter()
        .find(|row| row.name == name)
        .and_then(|row| scene::MarkerName::new(row.name))
}
fn json_text(value: &Json) -> String {
    match value {
        Json::Object(properties) => format!(
            "{{{}}}",
            properties
                .iter()
                .map(|(key, value)| format!("{key}:{}", json_text(value)))
                .collect::<Vec<_>>()
                .join(",")
        ),
        Json::Array(values) => format!(
            "[{}]",
            values.iter().map(json_text).collect::<Vec<_>>().join(",")
        ),
        Json::Scalar(value) => value.clone(),
    }
}
struct ShapeSpec<'a> {
    id: &'a str,
    business: bool,
    icon: Option<&'a str>,
    package: bool,
}
impl<'a> ShapeSpec<'a> {
    fn parse(encoded: &'a str) -> Self {
        let (id, flag) = encoded.split_once(':').unwrap_or((encoded, ""));
        let icon =
            (id == "usecaseActorIcon").then(|| flag.split_once(':').map_or(flag, |(_, name)| name));
        Self {
            id,
            business: flag == "business" || flag.starts_with("business:"),
            package: flag == "package",
            icon,
        }
    }
    fn is_actor(&self) -> bool {
        self.id.starts_with("usecaseActor")
    }
}
fn draw_shapes(input: &Input, scene: scene::Scene) -> Result<scene::Scene, LayoutError> {
    let mut groups = scene.items().to_vec();
    let mut dump = scene.dump_part().clone();
    for group in &mut groups {
        let Some(node) = input.boxes.iter().find(|node| node.id == group.owner) else {
            continue;
        };
        let Some(bounds) = scene.boxes().iter().find(|bounds| bounds.id == group.owner) else {
            continue;
        };
        let shape = ShapeSpec::parse(&node.shape);
        let mut text = group
            .items
            .iter()
            .filter_map(|item| match item {
                scene::Item::Text(text) => Some(text.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if shape.is_actor() {
            position_caption(&mut text, bounds.rect, input.profile)?;
        }
        if let Some(caption) = text.first() {
            for label in dump
                .labels
                .iter_mut()
                .filter(|label| label.owner == group.owner)
            {
                label.rect = caption.rect;
            }
        }
        group.items = outline(&shape, bounds, input.profile)?;
        group.items.extend(text.into_iter().map(scene::Item::Text));
    }
    Ok(scene::Scene::new(scene.canvas(), dump, groups))
}
fn position_caption(
    texts: &mut [scene::TextItem],
    rect: Rect,
    profile: Profile,
) -> Result<(), LayoutError> {
    let (top, padding) = if profile == Profile::Cell {
        (7, 1)
    } else {
        (88 * 64, 8 * 64)
    };
    for text in texts {
        text.rect.y = rect.y.checked_add(top).ok_or(LayoutError::Overflow)?;
        text.rect.x = rect.x.checked_add(padding).ok_or(LayoutError::Overflow)?;
        text.rect.w = rect
            .w
            .checked_sub(2 * padding)
            .ok_or(LayoutError::Overflow)?;
    }
    Ok(())
}
fn outline(
    spec: &ShapeSpec<'_>,
    bounds: &scene::SceneBox,
    profile: Profile,
) -> Result<Vec<scene::Item>, LayoutError> {
    use scene::*;
    let rect = bounds.rect;
    if spec.is_actor() {
        return ActorDrawing::new(rect, profile)?.items(spec);
    }
    let style = if bounds.role == BoxRole::Group {
        ShapeStyle::Group
    } else if spec.id == "note" {
        ShapeStyle::Note
    } else {
        ShapeStyle::Node
    };
    if matches!(spec.id, "usecaseEllipse" | "usecaseBusiness") {
        return ellipse_items(spec.id, rect, style);
    }
    let mut items = vec![Item::Rect(RectItem {
        shape: Shape::plain(style),
        rect,
    })];
    if spec.package {
        items.push(Item::Rect(RectItem {
            shape: Shape::plain(style),
            rect: Rect {
                x: rect.x,
                y: rect.y,
                w: rect.w / 3,
                h: if profile == Profile::Cell {
                    1
                } else {
                    Role::Label.line_height_px() * 64
                },
            },
        }));
    }
    Ok(items)
}
fn ellipse_items(
    id: &str,
    rect: Rect,
    style: scene::ShapeStyle,
) -> Result<Vec<scene::Item>, LayoutError> {
    use scene::*;
    let cx = offset(rect.x, rect.w / 2)?;
    let cy = offset(rect.y, rect.h / 2)?;
    let mut items = vec![Item::Ellipse(EllipseItem {
        shape: Shape::plain(style),
        cx,
        cy,
        rx: rect.w / 2,
        ry: rect.h / 2,
    })];
    if id == "usecaseBusiness" {
        items.push(Item::Polyline(PolylineItem {
            shape: Shape::plain(style),
            corner: 0,
            points: vec![
                Point {
                    x: offset(cx, rect.w / 3)?,
                    y: offset(cy, rect.h / 4)?,
                },
                Point {
                    x: offset(cx, rect.w / 2)?,
                    y: offset(cy, -(rect.h / 4))?,
                },
            ],
        }));
    }
    Ok(items)
}
fn offset(origin: i32, delta: i32) -> Result<i32, LayoutError> {
    origin.checked_add(delta).ok_or(LayoutError::Overflow)
}
struct ActorDrawing {
    origin: Point,
    profile: Profile,
}
impl ActorDrawing {
    fn new(rect: Rect, profile: Profile) -> Result<Self, LayoutError> {
        Ok(Self {
            origin: Point {
                x: offset(rect.x, rect.w / 2)?,
                y: offset(rect.y, if profile == Profile::Cell { 1 } else { 8 * 64 })?,
            },
            profile,
        })
    }
    fn point(&self, x: i32, y: i32) -> Result<Point, LayoutError> {
        let (dx, dy) = match self.profile {
            Profile::Vector => (i64::from(x) * 64, (i64::from(y) + 36) * 64),
            Profile::Cell => (
                floor_div(i64::from(x) * 7, 56),
                floor_div((i64::from(y) + 36) * 5, 72),
            ),
        };
        Ok(Point {
            x: offset(
                self.origin.x,
                i32::try_from(dx).map_err(|_| LayoutError::Overflow)?,
            )?,
            y: offset(
                self.origin.y,
                i32::try_from(dy).map_err(|_| LayoutError::Overflow)?,
            )?,
        })
    }
    fn items(&self, spec: &ShapeSpec<'_>) -> Result<Vec<scene::Item>, LayoutError> {
        if spec.icon.is_some() {
            let mut items = self.icon_items()?;
            if spec.business {
                items.insert(0, self.stroke(&[(12, -8), (26, -26)])?);
            }
            return Ok(items);
        }
        let (y, radius) = match spec.id {
            "usecaseActorHollow" => (-23, 9),
            "usecaseActorAwesome" => (-21, 13),
            _ => (-24, 12),
        };
        let center = self.point(0, y)?;
        let mut items = vec![self.head(center, radius)];
        match spec.id {
            "usecaseActorHollow" => items.push(self.polygon(&[
                (-22, -10),
                (22, -10),
                (22, 0),
                (6, 0),
                (22, 17),
                (13, 28),
                (0, 13),
                (-13, 28),
                (-22, 17),
                (-6, 0),
                (-22, 0),
            ])?),
            "usecaseActorAwesome" => items.push(self.silhouette()?),
            _ => {
                for points in [
                    &[(0, -12), (0, 8)][..],
                    &[(-17, -5), (17, -5)][..],
                    &[(-15, 28), (0, 8), (15, 28)][..],
                ] {
                    items.push(self.stroke(points)?);
                }
            }
        }
        if spec.business {
            items.push(self.stroke(&[(3, y + radius), (radius, y - radius)])?);
        }
        Ok(items)
    }
    fn head(&self, center: Point, radius: i32) -> scene::Item {
        use scene::*;
        let (rx, ry) = if self.profile == Profile::Cell {
            (1, 1)
        } else {
            (radius * 64, radius * 64)
        };
        Item::Ellipse(EllipseItem {
            shape: Shape::plain(ShapeStyle::InkLine),
            cx: center.x,
            cy: center.y,
            rx,
            ry,
        })
    }
    fn stroke(&self, points: &[(i32, i32)]) -> Result<scene::Item, LayoutError> {
        Ok(scene::Item::Polyline(scene::PolylineItem {
            shape: scene::Shape::plain(scene::ShapeStyle::InkLine),
            points: points
                .iter()
                .map(|(x, y)| self.point(*x, *y))
                .collect::<Result<Vec<_>, _>>()?,
            corner: 0,
        }))
    }
    fn polygon(&self, points: &[(i32, i32)]) -> Result<scene::Item, LayoutError> {
        Ok(scene::Item::Polygon(scene::PolygonItem {
            shape: scene::Shape::plain(scene::ShapeStyle::InkLine),
            points: points
                .iter()
                .map(|(x, y)| self.point(*x, *y))
                .collect::<Result<Vec<_>, _>>()?,
        }))
    }
    fn silhouette(&self) -> Result<scene::Item, LayoutError> {
        use scene::*;
        let start = self.point(-24, 25)?;
        let a = self.point(-24, 7)?;
        let b = self.point(-14, -3)?;
        let c = self.point(0, -3)?;
        let d = self.point(14, -3)?;
        let e = self.point(24, 7)?;
        let f = self.point(24, 25)?;
        let g = self.point(18, 30)?;
        let h = self.point(-18, 30)?;
        Ok(Item::Path(PathItem {
            shape: Shape::plain(ShapeStyle::InkLine),
            commands: vec![
                PathCommand::Move(start),
                PathCommand::Curve {
                    c1: a,
                    c2: b,
                    to: c,
                },
                PathCommand::Curve {
                    c1: d,
                    c2: e,
                    to: f,
                },
                PathCommand::Line(g),
                PathCommand::Line(h),
                PathCommand::Close,
            ],
        }))
    }
    fn icon_items(&self) -> Result<Vec<scene::Item>, LayoutError> {
        use scene::*;
        let top = self.point(-26, -28)?;
        let end = self.point(26, 24)?;
        let center = self.point(0, -2)?;
        let mut items = vec![Item::RoundRect(RoundRectItem {
            shape: Shape::plain(ShapeStyle::InkLine),
            rect: Rect {
                x: top.x,
                y: top.y,
                w: end.x - top.x,
                h: end.y - top.y,
            },
            r: if self.profile == Profile::Cell {
                0
            } else {
                4 * 64
            },
        })];
        if self.profile == Profile::Cell {
            let symbol = SymbolName::new("unknown").ok_or(LayoutError::Domain)?;
            items.push(Item::SymbolRef(SymbolRefItem {
                symbol,
                at: center,
                style: ShapeStyle::InkLine,
            }));
        } else {
            items.push(Item::Text(TextItem {
                rect: Rect {
                    x: top.x,
                    y: top.y,
                    w: end.x - top.x,
                    h: end.y - top.y,
                },
                role: TextRole::Label,
                size: 24,
                align: Align::Middle,
                style: TextStyle::Text,
                series: 0,
                lines: vec![vec![Run::plain("?")]],
            }));
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests;
