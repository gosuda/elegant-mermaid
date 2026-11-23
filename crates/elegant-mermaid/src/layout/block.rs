//! The block kind adapter (`spec/layout/grid.md`): [`from_block`] authors the model-stage
//! dump (root frame, blocks in pre-order, edge routes, edge labels) and [`layout`] feeds
//! the grid family with measured sizes, then draws the scene under both profiles.

use std::collections::BTreeMap;

use crate::r#gen::layoutconst::LAYOUT_CONST;
use crate::geom::{self, GeomError, Point, Rect, Size};
use crate::layout::grid::{self, Kind, Params};
use crate::measure::{self, Metric, Role, StyledLine};
use crate::model::block as mb;
use crate::scene::{
    Align, BoxRole, Dump, DumpOptions, DumpValue, EllipseItem, Group as SceneGroup, GroupRole,
    Item, Line as StyleLine, MarkerAxis, MarkerName, MarkerRefItem, PolygonItem, PolylineItem,
    Profile, RectItem, RoundRectItem, Run, Scene, SceneBox, SceneLabel, SceneRoute, Shape,
    ShapeStyle, TextItem, TextRole, TextStyle, Width,
};

use super::input::{Box as InputBox, Input, Label as InputLabel, Route as InputRoute, Spacing};
use super::layered::LayoutError;

const KIND: &str = "block";
const RING_INSET: i32 = 256;
const SUBROUTINE_INSET: i32 = 512;

pub(crate) fn from_block(
    model: &mb::Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(model
        .config
        .iter()
        .map(|entry| (entry.key.clone(), DumpValue::Integer(entry.value)))
        .collect::<BTreeMap<_, _>>());
    options.profile = profile;
    let mut boxes = vec![block_box(&model.root, "")];
    walk(&model.root, &mut boxes);
    let ids = route_ids(&boxes, model.edges.len());
    let mut routes = Vec::with_capacity(model.edges.len());
    let mut labels = Vec::new();
    for (edge, id) in model.edges.iter().zip(&ids) {
        routes.push(InputRoute {
            id: id.clone(),
            from: edge.start.clone(),
            to: edge.end.clone(),
            orthogonal: true,
            marker_start: marker(&edge.arrow_start).into(),
            marker_end: marker(&edge.arrow_end).into(),
            line: stroke(edge).into(),
            min_length: 0,
            from_side: None,
            to_side: None,
        });
        if !edge.label.is_empty() {
            labels.push(InputLabel {
                id: format!("{id}.label"),
                owner: id.clone(),
                role: TextRole::Label,
                text: edge.label.clone(),
            });
        }
    }
    Ok(Input {
        kind: KIND,
        profile,
        direction: crate::scene::Direction::Tb,
        options,
        boxes,
        routes,
        labels,
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    })
}

fn walk(parent: &mb::Block, boxes: &mut Vec<InputBox>) {
    for child in &parent.children {
        boxes.push(block_box(child, &parent.id));
        if child.kind == "composite" {
            walk(child, boxes);
        }
    }
}

fn block_box(block: &mb::Block, parent: &str) -> InputBox {
    match block.kind.as_str() {
        "composite" => InputBox {
            icon: false,
            id: block.id.clone(),
            role: BoxRole::Group,
            shape: shape_of("composite", block),
            parent: parent.into(),
            exclusive: false,
            text: String::new(),
            direction: String::new(),
        },
        "space" => InputBox {
            icon: false,
            id: block.id.clone(),
            role: BoxRole::Node,
            shape: "space".into(),
            parent: parent.into(),
            exclusive: false,
            text: String::new(),
            direction: String::new(),
        },
        kind => InputBox {
            icon: false,
            id: block.id.clone(),
            role: BoxRole::Node,
            shape: shape_of(shape_id(kind), block),
            parent: parent.into(),
            exclusive: true,
            text: block.label.clone(),
            direction: String::new(),
        },
    }
}

fn shape_id(kind: &str) -> &str {
    match kind {
        "na" | "square" => "rect",
        "round" => "roundedRect",
        "rect_left_inv_arrow" => "odd",
        other => other,
    }
}

fn shape_of(kind: &str, block: &mb::Block) -> String {
    let mut out = String::from(kind);
    if kind == "composite" && block.columns != mb::AUTO_COLUMNS {
        out.push_str(&format!(";columns={}", block.columns));
    }
    if block.span != 1 {
        out.push_str(&format!(";span={}", block.span));
    }
    if !block.directions.is_empty() {
        out.push_str(&format!(";directions={}", block.directions.join(",")));
    }
    out
}

fn marker(arrow: &str) -> &'static str {
    match arrow {
        "arrow_point" => "point",
        "arrow_cross" => "cross",
        "arrow_circle" => "circle",
        _ => "",
    }
}

fn stroke(edge: &mb::Edge) -> &'static str {
    if edge.thickness == "thick" {
        "thick"
    } else if edge.pattern == "dotted" {
        "dotted"
    } else {
        "normal"
    }
}

fn route_ids(boxes: &[InputBox], count: usize) -> Vec<String> {
    let mut next = 0usize;
    let mut ids = Vec::with_capacity(count);
    while ids.len() < count {
        let id = format!("e{next}");
        next += 1;
        if !boxes.iter().any(|node| node.id == id) {
            ids.push(id);
        }
    }
    ids
}

#[derive(Debug, Clone)]
struct Spec {
    kind: String,
    columns: i32,
    span: i32,
    directions: Vec<String>,
}

fn parse_shape(shape: &str) -> Spec {
    let mut fields = shape.split(';');
    let kind = fields
        .next()
        .filter(|kind| !kind.is_empty())
        .unwrap_or("rect");
    let mut spec = Spec {
        kind: kind.into(),
        columns: mb::AUTO_COLUMNS,
        span: 1,
        directions: Vec::new(),
    };
    for field in fields {
        let (key, value) = field.split_once('=').unwrap_or((field, ""));
        match key {
            "columns" => spec.columns = value.parse().unwrap_or(spec.columns),
            "span" => spec.span = value.parse().unwrap_or(spec.span),
            "directions" => spec.directions = value.split(',').map(String::from).collect(),
            _ => {}
        }
    }
    spec
}

#[derive(Debug, Clone, Default)]
struct Measured {
    width: i32,
    texts: Vec<String>,
    runs: Vec<Vec<Run>>,
}

impl Measured {
    fn of(lines: &[StyledLine<'_>]) -> Self {
        Self {
            width: lines.iter().map(|line| line.width).max().unwrap_or(0),
            texts: lines.iter().map(|line| line.text.clone()).collect(),
            runs: lines
                .iter()
                .map(|line| {
                    line.runs
                        .iter()
                        .map(|run| Run {
                            text: run.text.to_string(),
                            bold: run.bold,
                            italic: run.italic,
                        })
                        .collect()
                })
                .collect(),
        }
    }

    fn extent(&self, line_height: i32) -> Size {
        let limit = geom::COORD_LIMIT;
        let height = i64::try_from(self.texts.len()).unwrap_or(limit) * i64::from(line_height);
        Size {
            w: clamp(i64::from(self.width), limit),
            h: clamp(height, limit),
        }
    }
}

fn clamp(value: i64, limit: i64) -> i32 {
    i32::try_from(value.min(limit)).unwrap_or(i32::MAX)
}

fn lookup(key: &str) -> Result<i32, LayoutError> {
    LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| row.value)
        .ok_or(LayoutError::Domain)
}

fn metric_of(profile: Profile) -> Metric {
    if profile == Profile::Cell {
        Metric::cell()
    } else {
        Metric::for_role(Role::Label)
    }
}

fn is_root(candidate: &InputBox) -> bool {
    candidate.role == BoxRole::Group
        && candidate.parent.is_empty()
        && parse_shape(&candidate.shape).kind == "composite"
}

fn with_root(input: &Input) -> Input {
    let mut rooted = input.clone();
    if rooted.boxes.first().is_some_and(is_root) {
        return rooted;
    }
    let mut id = String::from("root");
    let mut ordinal = 0usize;
    while input.boxes.iter().any(|candidate| candidate.id == id) {
        ordinal += 1;
        id = format!("root{ordinal}");
    }
    rooted.boxes.insert(
        0,
        InputBox {
            icon: false,
            id,
            role: BoxRole::Group,
            shape: "composite".into(),
            parent: String::new(),
            exclusive: false,
            text: String::new(),
            direction: String::new(),
        },
    );
    rooted
}

fn box_text<'a>(input: &'a Input, candidate: &'a InputBox) -> &'a str {
    if let Some(label) = input
        .labels
        .iter()
        .find(|label| label.owner == candidate.id)
    {
        return &label.text;
    }
    if candidate.text.is_empty() {
        &candidate.id
    } else {
        &candidate.text
    }
}

struct Planner {
    input: Input,
    profile: Profile,
    padding: i32,
    line_height: i32,
    corner: i32,
    params: Params,
    specs: Vec<Spec>,
    texts: Vec<Measured>,
    label_texts: Vec<Measured>,
    index: BTreeMap<String, usize>,
}

pub(crate) fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let planner = Planner::new(with_root(input))?;
    let grid_input = planner.grid_input()?;
    let result = grid::block(&grid_input, planner.params)?;
    let dump = planner.fill(&result);
    let groups = planner.groups(&dump);
    Ok((Scene::new(result.canvas, dump, groups), false))
}

fn measure_text(input: &Input, text: &str) -> Result<Measured, LayoutError> {
    let metric = crate::scene::configured_metric(metric_of(input.profile), &input.options.config);
    let lines = measure::styled_lines(text, i32::MAX, metric)
        .map_err(|_| LayoutError::Overflow)?;
    Ok(Measured::of(&lines))
}

fn configured_padding(config: &BTreeMap<String, DumpValue>) -> Option<i32> {
    match config.get("padding") {
        Some(DumpValue::Integer(px)) => i32::try_from(*px).ok().filter(|px| *px >= 0),
        _ => None,
    }
}

impl Planner {
    fn new(input: Input) -> Result<Self, LayoutError> {
        let profile = input.profile;
        let key = |name: &str| lookup(&format!("{}.{name}", profile.as_str()));
        let padding = match configured_padding(&input.options.config) {
            Some(px) => scale_padding(profile, px),
            None => key("block.padding")?,
        };
        let params = Params {
            padding,
            bend_cost: key("block.bend_cost")?,
            line_thickness: key("block.line_thickness")?,
        };
        let mut index = BTreeMap::new();
        index.insert(String::new(), 0);
        let mut specs = Vec::with_capacity(input.boxes.len());
        let mut texts = Vec::with_capacity(input.boxes.len());
        for (i, candidate) in input.boxes.iter().enumerate() {
            index.insert(candidate.id.clone(), i);
            let spec = parse_shape(&candidate.shape);
            let measured = if candidate.role == BoxRole::Node && spec.kind != "space" {
                measure_text(&input, box_text(&input, candidate))?
            } else {
                Measured::default()
            };
            specs.push(spec);
            texts.push(measured);
        }
        let label_texts = input
            .labels
            .iter()
            .map(|label| measure_text(&input, &label.text))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            profile,
            padding,
            line_height: key("line_h")?,
            corner: key("corner_radius")?,
            params,
            specs,
            texts,
            label_texts,
            index,
            input,
        })
    }

    fn grid_input(&self) -> Result<grid::Input, LayoutError> {
        let mut blocks = Vec::with_capacity(self.input.boxes.len().saturating_sub(1));
        for i in 1..self.input.boxes.len() {
            let parent = *self
                .index
                .get(&self.input.boxes[i].parent)
                .ok_or(LayoutError::Domain)?;
            blocks.push(self.grid_block(i, parent.checked_sub(1)));
        }
        let mut edges = Vec::with_capacity(self.input.routes.len());
        for route in &self.input.routes {
            let from = self.index.get(&route.from).copied().unwrap_or(0);
            let to = self.index.get(&route.to).copied().unwrap_or(0);
            if from == 0 || to == 0 {
                return Err(LayoutError::Domain);
            }
            edges.push(grid::Edge {
                from: from - 1,
                to: to - 1,
                label: self.label_size(&route.id),
            });
        }
        Ok(grid::Input {
            columns: self.specs[0].columns,
            blocks,
            edges,
        })
    }

    fn grid_block(&self, i: usize, parent: Option<usize>) -> grid::Block {
        let spec = &self.specs[i];
        let mut block = grid::Block {
            parent,
            kind: Kind::Leaf,
            span: spec.span,
            columns: spec.columns,
            size: Size { w: 0, h: 0 },
        };
        if self.input.boxes[i].role == BoxRole::Group {
            block.kind = Kind::Composite;
        } else if spec.kind == "space" {
            block.kind = Kind::Space;
        } else {
            let text = self.texts[i].extent(self.line_height);
            block.size = Size {
                w: add_clamped(text.w, 2 * self.padding),
                h: add_clamped(text.h, 2 * self.padding),
            };
        }
        block
    }

    fn label_position(&self, owner: &str) -> Option<usize> {
        self.input
            .labels
            .iter()
            .position(|label| label.owner == owner)
    }

    fn label_size(&self, owner: &str) -> Size {
        self.label_position(owner).map_or(Size { w: 0, h: 0 }, |j| {
            self.label_texts[j].extent(self.line_height)
        })
    }

    fn fill(&self, result: &grid::Layout) -> Dump {
        let mut dump = Dump::new(KIND, self.input.options.clone());
        let mut rects: Vec<Rect> = result.rects.last().copied().into_iter().collect();
        rects.extend_from_slice(&result.rects[..result.rects.len().saturating_sub(1)]);
        for (candidate, rect) in self.input.boxes.iter().zip(rects) {
            dump.boxes.push(SceneBox {
                id: candidate.id.clone(),
                role: candidate.role,
                rect,
                parent: candidate.parent.clone(),
                exclusive: candidate.exclusive,
            });
        }
        for (route, points) in self.input.routes.iter().zip(&result.routes) {
            dump.routes.push(SceneRoute {
                id: route.id.clone(),
                from: route.from.clone(),
                to: route.to.clone(),
                orthogonal: true,
                points: points.clone(),
                marker_start: route.marker_start.clone(),
                marker_end: route.marker_end.clone(),
                stroke: route.line.clone(),
            });
        }
        for (label, measured) in self.input.labels.iter().zip(&self.label_texts) {
            let route = self
                .input
                .routes
                .iter()
                .position(|route| route.id == label.owner)
                .unwrap_or(0);
            dump.labels.push(SceneLabel {
                id: label.id.clone(),
                owner: label.owner.clone(),
                text: label.text.clone(),
                rect: result.labels.get(route).copied().unwrap_or(Rect {
                    x: 0,
                    y: 0,
                    w: 0,
                    h: 0,
                }),
                lines: measured.texts.clone(),
            });
        }
        dump
    }

    fn groups(&self, dump: &Dump) -> Vec<SceneGroup> {
        let mut groups = Vec::new();
        for (i, candidate) in self.input.boxes.iter().enumerate() {
            if candidate.role == BoxRole::Group {
                groups.push(SceneGroup {
                    role: GroupRole::Group,
                    owner: candidate.id.clone(),
                    items: self.frame(dump, i),
                });
            }
        }
        for (i, route) in self.input.routes.iter().enumerate() {
            groups.push(SceneGroup {
                role: GroupRole::Edge,
                owner: route.id.clone(),
                items: self.edge_items(dump, i, route),
            });
        }
        for (i, candidate) in self.input.boxes.iter().enumerate() {
            if candidate.role == BoxRole::Node && self.specs[i].kind != "space" {
                groups.push(SceneGroup {
                    role: GroupRole::Node,
                    owner: candidate.id.clone(),
                    items: self.node_items(dump, i),
                });
            }
        }
        groups
    }

    fn frame(&self, dump: &Dump, index: usize) -> Vec<Item> {
        if index == 0 {
            return Vec::new();
        }
        vec![Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Group),
            rect: dump.boxes[index].rect,
        })]
    }

    fn edge_items(&self, dump: &Dump, index: usize, route: &InputRoute) -> Vec<Item> {
        let points = &dump.routes[index].points;
        let mut items = if points.len() >= 2 {
            self.route_items(route, points)
        } else {
            Vec::new()
        };
        if let Some(position) = self.label_position(&route.id) {
            items.push(self.label_item(dump, position));
        }
        items
    }

    fn route_items(&self, route: &InputRoute, points: &[Point]) -> Vec<Item> {
        let mut shape = Shape::plain(ShapeStyle::Edge);
        match route.line.as_str() {
            "thick" => shape = shape.with_width(Width::Emphasis),
            "dotted" => shape = shape.with_line(StyleLine::Dotted),
            _ => {}
        }
        let mut items = vec![Item::Polyline(PolylineItem {
            shape,
            points: points.to_vec(),
            corner: self.corner,
        })];
        if let [first, second, ..] = points {
            items.extend(marker_item(
                &route.marker_start,
                *first,
                axis(*second, *first),
            ));
        }
        if let [.., before, last] = points {
            items.extend(marker_item(&route.marker_end, *last, axis(*before, *last)));
        }
        items
    }

    fn label_item(&self, dump: &Dump, position: usize) -> Item {
        Item::Text(TextItem {
            rect: dump.labels[position].rect,
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: self.label_texts[position].runs.clone(),
        })
    }

    fn node_items(&self, dump: &Dump, index: usize) -> Vec<Item> {
        let rect = dump.boxes[index].rect;
        let measured = &self.texts[index];
        let text_h = i32::try_from(measured.texts.len()).unwrap_or(0) * self.line_height;
        let mut items = self.outline(&self.specs[index], rect);
        items.push(Item::Text(TextItem {
            rect: Rect {
                x: rect.x,
                y: rect.y + ((rect.h - text_h) >> 1),
                w: rect.w,
                h: text_h,
            },
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: measured.runs.clone(),
        }));
        items
    }

    fn outline(&self, spec: &Spec, rect: Rect) -> Vec<Item> {
        if self.profile == Profile::Cell {
            cell_outline(spec, rect)
        } else {
            self.vector_outline(spec, rect)
        }
    }

    fn vector_outline(&self, spec: &Spec, rect: Rect) -> Vec<Item> {
        let shape = Shape::plain(ShapeStyle::Node);
        let bounds = Bounds::of(rect);
        if let Some(points) = bounds.polygon(&spec.kind) {
            return vec![polygon(shape, &points)];
        }
        match spec.kind.as_str() {
            "roundedRect" => vec![Item::RoundRect(RoundRectItem {
                shape,
                rect,
                r: self.corner.min(rect.w / 2).min(rect.h / 2),
            })],
            "stadium" => vec![Item::RoundRect(RoundRectItem {
                shape,
                rect,
                r: rect.w.min(rect.h) / 2,
            })],
            "circle" => vec![ellipse(shape, rect, 0)],
            "doublecircle" => vec![
                ellipse(shape, rect, 0),
                ellipse(shape, rect, RING_INSET.min(rect.w / 4).min(rect.h / 4)),
            ],
            "cylinder" => cylinder(rect, Profile::Vector),
            "subroutine" => subroutine(rect),
            "block_arrow" => vec![polygon(
                shape,
                &arrow_points(&Heads::of(&spec.directions), rect),
            )],
            _ => vec![Item::Rect(RectItem { shape, rect })],
        }
    }
}

fn scale_padding(profile: Profile, px: i32) -> i32 {
    if profile == Profile::Cell {
        ((px + 7) / 8).max(1)
    } else {
        px * 64
    }
}

fn add_clamped(a: i32, b: i32) -> i32 {
    clamp(i64::from(a) + i64::from(b), geom::COORD_LIMIT)
}

fn axis(from: Point, to: Point) -> MarkerAxis {
    let dx = i64::from(to.x) - i64::from(from.x);
    let dy = i64::from(to.y) - i64::from(from.y);
    let horizontal = dx.abs() >= dy.abs();
    match (horizontal, dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

fn marker_item(name: &str, at: Point, axis: MarkerAxis) -> Option<Item> {
    let marker = match name {
        "point" => MarkerName::new("point")?,
        "cross" => MarkerName::new("cross")?,
        "circle" => MarkerName::new("circle")?,
        _ => return None,
    };
    Some(Item::MarkerRef(MarkerRefItem { marker, at, axis }))
}

fn cell_outline(spec: &Spec, rect: Rect) -> Vec<Item> {
    let shape = Shape::plain(ShapeStyle::Node);
    match spec.kind.as_str() {
        "roundedRect" | "stadium" | "circle" => {
            vec![Item::RoundRect(RoundRectItem { shape, rect, r: 0 })]
        }
        "cylinder" => cylinder(rect, Profile::Cell),
        "doublecircle" => vec![Item::Rect(RectItem {
            shape: shape.with_line(StyleLine::Double),
            rect,
        })],
        "block_arrow" => {
            let mut items = vec![Item::Rect(RectItem { shape, rect })];
            items.extend(arrow_markers(&Heads::of(&spec.directions), rect));
            items
        }
        _ => vec![Item::Rect(RectItem { shape, rect })],
    }
}

fn cylinder(rect: Rect, profile: Profile) -> Vec<Item> {
    super::c4::cylinder_outline(rect, profile, i64::from(rect.h)).unwrap_or_else(|_| {
        vec![Item::RoundRect(RoundRectItem {
            shape: Shape::plain(ShapeStyle::Node),
            rect,
            r: 0,
        })]
    })
}

#[derive(Debug, Clone, Copy, Default)]
struct Heads {
    up: bool,
    right: bool,
    down: bool,
    left: bool,
}

impl Heads {
    fn of(directions: &[String]) -> Self {
        let mut heads = Self::default();
        for direction in directions {
            match direction.as_str() {
                "up" => heads.up = true,
                "down" => heads.down = true,
                "left" => heads.left = true,
                "right" => heads.right = true,
                "x" => {
                    heads.left = true;
                    heads.right = true;
                }
                "y" => {
                    heads.up = true;
                    heads.down = true;
                }
                _ => {}
            }
        }
        heads
    }
}

fn arrow_markers(heads: &Heads, rect: Rect) -> Vec<Item> {
    let (cx, cy) = (rect.x + rect.w / 2, rect.y + rect.h / 2);
    let (right, bottom) = (rect.x + rect.w - 1, rect.y + rect.h - 1);
    [
        (heads.up, Point { x: cx, y: rect.y }, MarkerAxis::MinusY),
        (heads.right, Point { x: right, y: cy }, MarkerAxis::PlusX),
        (heads.down, Point { x: cx, y: bottom }, MarkerAxis::PlusY),
        (heads.left, Point { x: rect.x, y: cy }, MarkerAxis::MinusX),
    ]
    .into_iter()
    .filter(|(on, _, _)| *on)
    .filter_map(|(_, at, axis)| marker_item("point", at, axis))
    .collect()
}

fn ellipse(shape: Shape, rect: Rect, inset: i32) -> Item {
    Item::Ellipse(EllipseItem {
        shape,
        cx: rect.x + rect.w / 2,
        cy: rect.y + rect.h / 2,
        rx: rect.w / 2 - inset,
        ry: rect.h / 2 - inset,
    })
}

fn polygon(shape: Shape, coordinates: &[(i64, i64)]) -> Item {
    Item::Polygon(PolygonItem {
        shape,
        points: coordinates
            .iter()
            .map(|(x, y)| Point {
                x: i32::try_from(*x).unwrap_or(i32::MAX),
                y: i32::try_from(*y).unwrap_or(i32::MAX),
            })
            .collect(),
    })
}

fn subroutine(rect: Rect) -> Vec<Item> {
    let inset = SUBROUTINE_INSET.min(rect.w / 4);
    let mut items = vec![Item::Rect(RectItem {
        shape: Shape::plain(ShapeStyle::Node),
        rect,
    })];
    for x in [rect.x + inset, rect.x + rect.w - inset] {
        items.push(Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Rule),
            points: vec![
                Point { x, y: rect.y },
                Point {
                    x,
                    y: rect.y + rect.h,
                },
            ],
            corner: 0,
        }));
    }
    items
}

#[derive(Debug, Clone, Copy)]
struct Bounds {
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    slant: i64,
}

impl Bounds {
    fn of(rect: Rect) -> Self {
        let (w, h) = (i64::from(rect.w), i64::from(rect.h));
        Self {
            x: i64::from(rect.x),
            y: i64::from(rect.y),
            w,
            h,
            slant: (h / 4).min(w / 4),
        }
    }

    fn right(&self) -> i64 {
        self.x + self.w
    }

    fn bottom(&self) -> i64 {
        self.y + self.h
    }

    fn mid_x(&self) -> i64 {
        self.x + self.w / 2
    }

    fn mid_y(&self) -> i64 {
        self.y + self.h / 2
    }

    fn polygon(&self, kind: &str) -> Option<Vec<(i64, i64)>> {
        let (x, y, r, b, s) = (self.x, self.y, self.right(), self.bottom(), self.slant);
        let (mx, my) = (self.mid_x(), self.mid_y());
        Some(match kind {
            "diamond" => vec![(mx, y), (r, my), (mx, b), (x, my)],
            "hexagon" => vec![
                (x + s, y),
                (r - s, y),
                (r, my),
                (r - s, b),
                (x + s, b),
                (x, my),
            ],
            "lean_right" => vec![(x + s, y), (r, y), (r - s, b), (x, b)],
            "lean_left" => vec![(x, y), (r - s, y), (r, b), (x + s, b)],
            "trapezoid" => vec![(x + s, y), (r - s, y), (r, b), (x, b)],
            "inv_trapezoid" => vec![(x, y), (r, y), (r - s, b), (x + s, b)],
            "odd" => vec![(x, y), (r, y), (r, b), (x, b), (x + s, my)],
            _ => return None,
        })
    }
}

fn arrow_points(heads: &Heads, rect: Rect) -> Vec<(i64, i64)> {
    let b = Bounds::of(rect);
    let depth = b.w.min(b.h) / 4;
    let (mut left, mut right, mut top, mut bottom) = (b.x, b.right(), b.y, b.bottom());
    if heads.left {
        left += depth;
    }
    if heads.right {
        right -= depth;
    }
    if heads.up {
        top += depth;
    }
    if heads.down {
        bottom -= depth;
    }
    let mut points = vec![(left, top)];
    if heads.up {
        points.push((b.mid_x(), b.y));
    }
    points.push((right, top));
    if heads.right {
        points.push((b.right(), b.mid_y()));
    }
    points.push((right, bottom));
    if heads.down {
        points.push((b.mid_x(), b.bottom()));
    }
    points.push((left, bottom));
    if heads.left {
        points.push((b.x, b.mid_y()));
    }
    points
}

#[cfg(test)]
mod tests;
