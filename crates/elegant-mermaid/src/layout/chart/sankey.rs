use super::{Area, Skeleton, constant, to_i32};
use crate::geom::{GeomError, Point, Size};
use crate::measure::{self, Metric, Role};
use crate::model::sankey::Model;
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, DumpValue, Group, GroupRole, Item, PathCommand,
    PathItem, Profile, RectItem, Run, Scene, SceneBox, SceneLabel, SceneRoute, Shape, ShapeStyle,
    TextItem, TextRole, TextStyle, Width,
};

#[path = "sankey_flow.rs"]
mod flow;
use flow::Flow;

pub fn node_id(index: usize) -> String {
    format!("n{index}")
}
pub fn link_id(index: usize) -> String {
    format!("l{index}")
}

pub fn labels(model: &Model) -> Result<Vec<String>, GeomError> {
    let show = model.config.get("showValues") != Some(&DumpValue::Bool(false));
    let mut incoming = vec![0_i64; model.nodes.len()];
    let mut outgoing = vec![0_i64; model.nodes.len()];
    for link in &model.links {
        if link.value.kind != crate::model::sankey::ValueKind::Finite {
            continue;
        }
        outgoing[link.source] = outgoing[link.source]
            .checked_add(link.value.thousandths)
            .ok_or(GeomError::Overflow)?;
        incoming[link.target] = incoming[link.target]
            .checked_add(link.value.thousandths)
            .ok_or(GeomError::Overflow)?;
    }
    model
        .nodes
        .iter()
        .enumerate()
        .map(|(i, node)| {
            if let Some(label) = &node.label {
                return Ok(label.clone());
            }
            let id = node.id.replace('\n', " ");
            if !show {
                return Ok(id);
            }
            let value = incoming[i]
                .max(outgoing[i])
                .checked_add(5)
                .ok_or(GeomError::Overflow)?
                .div_euclid(10)
                * 10;
            let negative = value < 0;
            let magnitude = value.unsigned_abs();
            let whole = magnitude / 1000;
            let fraction = magnitude % 1000;
            let mut text = format!("{}{whole}", if negative { "-" } else { "" });
            if fraction != 0 {
                text.push('.');
                text.push_str(format!("{fraction:03}").trim_end_matches('0'));
            }
            Ok(format!("{id}<br>{text}"))
        })
        .collect()
}

pub fn skeleton(model: &Model) -> Result<Skeleton, GeomError> {
    let mut skeleton = Skeleton {
        boxes: Vec::new(),
        labels: Vec::new(),
    };
    for (i, text) in labels(model)?.into_iter().enumerate() {
        skeleton.boxes.push(SceneBox {
            id: node_id(i),
            role: BoxRole::Node,
            rect: super::ZERO_RECT,
            parent: String::new(),
            exclusive: false,
        });
        if !text.is_empty() {
            skeleton.labels.push(SceneLabel {
                id: format!("n{i}.label"),
                owner: node_id(i),
                text,
                rect: super::ZERO_RECT,
                lines: Vec::new(),
            });
        }
    }
    Ok(skeleton)
}

struct Text {
    text: String,
    lines: Vec<String>,
    width: i64,
    height: i64,
    cell_width: i64,
}

impl Text {
    fn measure(text: String, font_family: bool) -> Result<Self, GeomError> {
        let role = Role::Label;
        let metric = Metric::Vector {
            size_px: role.size_px(),
            weight: role.weight(),
            font_family,
        };
        let wrapped = measure::wrap(&text, i32::MAX, metric)?;
        let width = wrapped
            .iter()
            .map(|line| i64::from(line.width))
            .max()
            .unwrap_or(0);
        let cell_width = wrapped.iter().try_fold(0_i64, |widest, line| {
            measure::cell_width(line.text).map(|width| widest.max(i64::from(width) * 512))
        })?;
        let height = i64::try_from(wrapped.len()).map_err(|_| GeomError::Overflow)?
            * i64::from(role.line_height_px())
            * 64;
        let lines = wrapped.iter().map(|line| line.text.to_string()).collect();
        Ok(Self {
            text,
            lines,
            width,
            height,
            cell_width,
        })
    }
}

struct Plan<'a> {
    model: &'a Model,
    flow: Flow,
    width: i64,
    height: i64,
    node_width: i64,
    label_gap: i64,
    nodes: Vec<Area>,
    texts: Vec<Text>,
    places: Vec<Area>,
    aligns: Vec<Align>,
}

fn integer(model: &Model, key: &str, default: i64) -> Result<i64, GeomError> {
    match model.config.get(key) {
        Some(DumpValue::Integer(value)) => value.checked_mul(64).ok_or(GeomError::Overflow),
        _ => Ok(default),
    }
}

pub fn layout(model: &Model, options: &DumpOptions) -> Result<(Scene, bool), GeomError> {
    let width = integer(model, "width", constant(Profile::Vector, "sankey.width")?)?;
    let height = integer(model, "height", constant(Profile::Vector, "sankey.height")?)?;
    let mut padding = constant(Profile::Vector, "sankey.node_padding")?;
    if model.config.get("showValues") != Some(&DumpValue::Bool(false)) {
        padding += constant(Profile::Vector, "sankey.show_values_pad")?;
    }
    let iterations = u32::try_from(constant(Profile::Vector, "sankey.iterations")?)
        .map_err(|_| GeomError::Overflow)?;
    let flow = Flow::new(model, height, padding, iterations)?;
    let mut plan = Plan {
        model,
        flow,
        width,
        height,
        node_width: constant(Profile::Vector, "sankey.node_width")?,
        label_gap: constant(Profile::Vector, "sankey.label_gap")?,
        nodes: Vec::new(),
        texts: Vec::new(),
        places: Vec::new(),
        aligns: Vec::new(),
    };
    plan.arrange()?;
    Ok((plan.scene(options)?, false))
}

impl Plan<'_> {
    fn arrange(&mut self) -> Result<(), GeomError> {
        let alignment = match self.model.config.get("nodeAlignment") {
            Some(DumpValue::String(value)) => value.as_str(),
            _ => "justify",
        };
        self.flow.run(alignment)?;
        let depth = self
            .flow
            .nodes
            .iter()
            .map(|node| node.depth)
            .max()
            .unwrap_or(0);
        for node in &self.flow.nodes {
            let x = if depth == 0 {
                0
            } else {
                i64::try_from(node.layer)
                    .map_err(|_| GeomError::Overflow)?
                    .checked_mul(self.width - self.node_width)
                    .ok_or(GeomError::Overflow)?
                    .div_euclid(i64::try_from(depth).map_err(|_| GeomError::Overflow)?)
            };
            self.nodes
                .push(Area::new(x, node.y0, self.node_width, node.y1 - node.y0));
        }
        for (i, label) in labels(self.model)?.into_iter().enumerate() {
            let text = Text::measure(label, crate::scene::has_font_family(&self.model.config))?;
            let node = self.nodes[i];
            let centre = (2 * node.y + node.h).div_euclid(2);
            let y =
                (centre - text.height.div_euclid(2)).clamp(0, (self.height - text.height).max(0));
            let (x, align) = if 2 * node.x < self.width {
                (node.x + node.w + self.label_gap, Align::Start)
            } else {
                ((node.x - self.label_gap - text.width).max(0), Align::End)
            };
            self.places.push(Area::new(x, y, text.width, text.height));
            self.aligns.push(align);
            self.texts.push(text);
        }
        self.separate_labels();
        self.normalize_canvas()
    }

    fn normalize_canvas(&mut self) -> Result<(), GeomError> {
        let mut rectangles = self.nodes.iter().copied().chain(
            self.places
                .iter()
                .zip(&self.texts)
                .filter(|(_, text)| !text.text.is_empty())
                .map(|(place, _)| *place),
        );
        let (min_x, mut min_y, max_x, mut max_y) = rectangles.try_fold(
            (0_i64, 0_i64, self.width, self.height),
            |(min_x, min_y, max_x, max_y), rect| {
                let right = rect.x.checked_add(rect.w).ok_or(GeomError::Overflow)?;
                let bottom = rect.y.checked_add(rect.h).ok_or(GeomError::Overflow)?;
                Ok::<_, GeomError>((
                    min_x.min(rect.x),
                    min_y.min(rect.y),
                    max_x.max(right),
                    max_y.max(bottom),
                ))
            },
        )?;
        for link in &self.flow.links {
            min_y = min_y.min(link.y0).min(link.y1);
            max_y = max_y.max(link.y0).max(link.y1);
        }
        let dx = min_x.checked_neg().ok_or(GeomError::Overflow)?;
        let dy = min_y.checked_neg().ok_or(GeomError::Overflow)?;
        for rect in self.nodes.iter_mut().chain(self.places.iter_mut()) {
            rect.x = rect.x.checked_add(dx).ok_or(GeomError::Overflow)?;
            rect.y = rect.y.checked_add(dy).ok_or(GeomError::Overflow)?;
        }
        for link in &mut self.flow.links {
            link.y0 = link.y0.checked_add(dy).ok_or(GeomError::Overflow)?;
            link.y1 = link.y1.checked_add(dy).ok_or(GeomError::Overflow)?;
        }
        self.width = max_x.checked_add(dx).ok_or(GeomError::Overflow)?;
        self.height = max_y.checked_add(dy).ok_or(GeomError::Overflow)?;
        Ok(())
    }

    fn reach(&self, index: usize) -> Area {
        let place = self.places[index];
        let width = place.w.max(self.texts[index].cell_width) + 1024;
        let left = if self.aligns[index] == Align::End {
            place.x + place.w + 512 - width
        } else {
            place.x - 512
        };
        Area::new(left, place.y, width, place.h)
    }

    fn separate_labels(&mut self) {
        let mut indices: Vec<usize> = self
            .texts
            .iter()
            .enumerate()
            .filter(|(_, text)| !text.text.is_empty())
            .map(|(i, _)| i)
            .collect();
        indices.sort_by_key(|&i| self.places[i].y);
        for (k, &i) in indices.iter().enumerate() {
            self.separate_label(i, &indices[..k]);
        }
    }

    fn separate_label(&mut self, index: usize, previous: &[usize]) {
        let mut moved = true;
        while moved {
            moved = false;
            for &other in previous {
                let a = self.reach(index);
                let b = self.reach(other);
                if a.x.max(b.x) >= (a.x + a.w).min(b.x + b.w)
                    || a.y.max(b.y) >= (a.y + a.h).min(b.y + b.h)
                {
                    continue;
                }
                self.places[index].y = self.places[other].y + self.places[other].h;
                moved = true;
            }
        }
    }

    fn scene(&self, options: &DumpOptions) -> Result<Scene, GeomError> {
        let mut options = options.clone();
        options.profile = Profile::Vector;
        options.direction = Direction::Tb;
        let mut dump = Dump::new("sankey", options);
        let mut groups = Vec::new();
        for (i, link) in self.flow.links.iter().enumerate() {
            let source = self.nodes[link.source];
            let target = self.nodes[link.target];
            let from = Point {
                x: to_i32(source.x + source.w)?,
                y: to_i32(link.y0)?,
            };
            let to = Point {
                x: to_i32(target.x)?,
                y: to_i32(link.y1)?,
            };
            dump.routes.push(SceneRoute {
                id: link_id(i),
                from: node_id(link.source),
                to: node_id(link.target),
                orthogonal: false,
                points: vec![from, to],
                marker_start: String::new(),
                marker_end: String::new(),
                stroke: String::new(),
            });
            let mid = to_i32((i64::from(from.x) + i64::from(to.x)).div_euclid(2))?;
            let mut shape = Shape::plain(ShapeStyle::SeriesFlow)
                .with_series(u8::try_from(link.source % 12).map_err(|_| GeomError::Overflow)?);
            shape.width = Width::Units(to_i32(link.width)?);
            let path = Item::Path(PathItem {
                shape,
                commands: vec![
                    PathCommand::Move(from),
                    PathCommand::Curve {
                        c1: Point { x: mid, y: from.y },
                        c2: Point { x: mid, y: to.y },
                        to,
                    },
                ],
            });
            groups.push(Group::new(GroupRole::Edge, link_id(i)).with_items(vec![path]));
        }
        for (i, node) in self.nodes.iter().enumerate() {
            let rect = node.to_rect()?;
            dump.boxes.push(SceneBox {
                id: node_id(i),
                role: BoxRole::Node,
                rect,
                parent: String::new(),
                exclusive: false,
            });
            let shape = Shape::plain(ShapeStyle::Series)
                .with_series(u8::try_from(i % 12).map_err(|_| GeomError::Overflow)?);
            let mut items = vec![Item::Rect(RectItem { shape, rect })];
            let text = &self.texts[i];
            if !text.text.is_empty() {
                let rect = self.places[i].to_rect()?;
                dump.labels.push(SceneLabel {
                    id: format!("n{i}.label"),
                    owner: node_id(i),
                    text: text.text.clone(),
                    rect,
                    lines: text.lines.clone(),
                });
                items.push(Item::Text(TextItem {
                    rect,
                    role: TextRole::Label,
                    size: Role::Label.size_px(),
                    align: self.aligns[i],
                    style: TextStyle::Text,
                    series: 0,
                    lines: text
                        .lines
                        .iter()
                        .map(|line| {
                            vec![Run {
                                text: line.clone(),
                                bold: false,
                                italic: false,
                            }]
                        })
                        .collect(),
                }));
            }
            groups.push(Group::new(GroupRole::Node, node_id(i)).with_items(items));
        }
        Ok(Scene::new(
            Size {
                w: to_i32(self.width)?,
                h: to_i32(self.height)?,
            },
            dump,
            groups,
        ))
    }
}
