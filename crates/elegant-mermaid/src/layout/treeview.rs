//! Treeview preorder rows, guides, icons, and aligned descriptions.
use super::input::{Box, Input, Label, Route, Spacing};
use super::layered::LayoutError;
use crate::geom::{COORD_LIMIT, GeomError, Point, Rect, Size, floor_div};
use crate::measure::{Metric, Role};
use crate::model::treeview::Model;
use crate::scene::{
    Align, BoxRole, Direction, Dump, DumpOptions, DumpValue, Group, GroupRole, Item, PolylineItem,
    Profile, RectItem, Run, Scene, SceneBox, SceneRoute, Shape, ShapeStyle, TextItem, TextRole,
    TextStyle, Width,
};
use std::collections::BTreeMap;

pub fn from_treeview(
    model: &Model,
    profile: Profile,
    mut options: DumpOptions,
) -> Result<Input, GeomError> {
    options.set_kind_config(Default::default());
    for (key, value) in [
        ("lineThickness", model.config.line_thickness),
        ("paddingX", model.config.padding_x),
        ("paddingY", model.config.padding_y),
        ("rowIndent", model.config.row_indent),
    ] {
        if let Some(value) = value {
            options
                .config
                .insert(key.into(), DumpValue::Integer(i64::from(value)));
        }
    }
    options.profile = profile;
    options.direction = Direction::Tb;
    let mut input = Input {
        kind: "treeview",
        profile,
        direction: Direction::Tb,
        options,
        boxes: Vec::new(),
        routes: Vec::new(),
        labels: Vec::new(),
        groups: Vec::new(),
        sizes: Vec::new(),
        attachments: Vec::new(),
        region_sets: Vec::new(),
        spacing: Spacing::default(),
    };
    for node in &model.nodes {
        let id = format!("n{}", node.index);
        input.boxes.push(Box {
            id: id.clone(),
            role: BoxRole::Node,
            shape: if node.directory { "directory" } else { "file" }.into(),
            icon: false,
            parent: String::new(),
            exclusive: true,
            text: String::new(),
            direction: String::new(),
        });
        input.labels.push(Label {
            id: format!("{id}.label"),
            owner: id.clone(),
            role: TextRole::Label,
            text: node.name.clone(),
        });
        for (suffix, text) in [
            ("desc", &node.description),
            ("icon", &node.icon),
            ("class", &node.class),
        ] {
            if !text.is_empty() {
                input.labels.push(Label {
                    id: format!("{id}.{suffix}"),
                    owner: id.clone(),
                    role: TextRole::Body,
                    text: text.clone(),
                });
            }
        }
        if let Some(parent) = node.parent {
            input.routes.push(Route {
                id: format!("e{}", input.routes.len()),
                from: format!("n{parent}"),
                to: id,
                orthogonal: true,
                marker_start: String::new(),
                marker_end: String::new(),
                line: "normal".into(),
                min_length: 0,
                from_side: None,
                to_side: None,
            });
        }
    }
    Ok(input)
}

#[derive(Default)]
struct Node {
    name: String,
    desc: String,
    icon: String,
    class: String,
    directory: bool,
    parent: Option<usize>,
    depth: usize,
    label_width: i32,
    desc_width: i32,
}
impl Node {
    fn shown(&self, profile: Profile) -> String {
        let name = self.name.replace('\n', " ");
        if profile == Profile::Cell && self.directory && self.parent.is_some() {
            format!("{name}/")
        } else {
            name
        }
    }
    fn metric(&self, profile: Profile) -> Metric {
        if profile == Profile::Cell {
            Metric::Cell
        } else {
            Metric::for_role(if self.directory {
                Role::Label
            } else {
                Role::Body
            })
        }
    }
    fn assign(&mut self, label: &Label) {
        if label.id.ends_with(".label") {
            self.name.clone_from(&label.text);
        } else if label.id.ends_with(".desc") {
            self.desc.clone_from(&label.text);
        } else if label.id.ends_with(".class") {
            self.class.clone_from(&label.text);
        } else if label.id.ends_with(".icon") && label.text != "none" {
            self.icon.clone_from(&label.text);
        }
    }
}

struct Metrics {
    indent: i64,
    px: i64,
    py: i64,
    height: i64,
    icon: i64,
    icon_gap: i64,
    desc_gap: i64,
    thickness: i32,
    margin: i64,
}
fn constant(profile: Profile, name: &str) -> Result<i64, GeomError> {
    let key = format!("{}.{name}", profile.as_str());
    crate::r#gen::layoutconst::LAYOUT_CONST
        .iter()
        .find(|row| row.name == key)
        .map(|row| i64::from(row.value))
        .ok_or(GeomError::Domain)
}
impl Metrics {
    fn load(input: &Input) -> Result<Self, GeomError> {
        let c = |name| constant(input.profile, name);
        let mut m = Self {
            indent: c("treeview.row_indent")?,
            px: c("treeview.padding_x")?,
            py: c("treeview.padding_y")?,
            height: c("line_h")?,
            icon: c("treeview.icon_size")?,
            icon_gap: c("treeview.icon_gap")?,
            desc_gap: c("treeview.desc_gap")?,
            thickness: narrow(c("treeview.line_thickness")?)?,
            margin: c("canvas_margin")?,
        };
        if input.profile == Profile::Vector {
            m.configure(&input.options.config)?;
        }
        Ok(m)
    }
    fn configure(&mut self, config: &BTreeMap<String, DumpValue>) -> Result<(), GeomError> {
        for (key, value) in config {
            let DumpValue::Integer(value) = value else {
                return Err(GeomError::Domain);
            };
            if *value < 0 || *value > COORD_LIMIT {
                return Err(GeomError::Overflow);
            }
            let units = floor_div(2 * value * 64 + 1000, 2000);
            match key.as_str() {
                "rowIndent" => self.indent = units,
                "paddingX" => self.px = units,
                "paddingY" => self.py = units,
                "lineThickness" => self.thickness = narrow(units)?,
                _ => {}
            }
        }
        Ok(())
    }
}
fn narrow(value: i64) -> Result<i32, GeomError> {
    if !(0..=COORD_LIMIT).contains(&value) {
        return Err(GeomError::Overflow);
    }
    i32::try_from(value).map_err(|_| GeomError::Overflow)
}
struct Plan<'a> {
    input: &'a Input,
    nodes: Vec<Node>,
    m: Metrics,
    index: BTreeMap<&'a str, usize>,
}
impl<'a> Plan<'a> {
    fn new(input: &'a Input) -> Result<Self, GeomError> {
        let mut p = Self {
            input,
            m: Metrics::load(input)?,
            nodes: input
                .boxes
                .iter()
                .map(|b| Node {
                    name: b.id.clone(),
                    directory: b.shape == "directory",
                    ..Node::default()
                })
                .collect(),
            index: input
                .boxes
                .iter()
                .enumerate()
                .map(|(i, b)| (b.id.as_str(), i))
                .collect(),
        };
        for label in &input.labels {
            let i = *p.index.get(label.owner.as_str()).ok_or(GeomError::Domain)?;
            p.nodes[i].assign(label);
        }
        for route in &input.routes {
            let to = *p.index.get(route.to.as_str()).ok_or(GeomError::Domain)?;
            let from = *p.index.get(route.from.as_str()).ok_or(GeomError::Domain)?;
            if from >= to || p.nodes[to].parent.is_some() {
                return Err(GeomError::Domain);
            }
            p.nodes[to].parent = Some(from);
        }
        p.measure()?;
        Ok(p)
    }
    fn measure(&mut self) -> Result<(), GeomError> {
        if self.nodes.is_empty() || self.nodes[0].parent.is_some() {
            return Err(GeomError::Domain);
        }
        for i in 0..self.nodes.len() {
            if i > 0 {
                let parent = self.nodes[i].parent.ok_or(GeomError::Domain)?;
                self.nodes[i].depth = self.nodes[parent].depth + 1;
            }
            let n = &mut self.nodes[i];
            n.label_width = crate::scene::configured_metric(n.metric(self.input.profile), &self.input.options.config)
                .width(&n.shown(self.input.profile))?;
            let metric = if self.input.profile == Profile::Cell {
                Metric::Cell
            } else {
                Metric::for_role(Role::Body)
            };
            let metric = crate::scene::configured_metric(metric, &self.input.options.config);
            n.desc_width = metric.width(&n.desc.replace('\n', " "))?;
        }
        Ok(())
    }
    fn indent(&self, i: usize) -> i64 {
        i64::try_from(self.nodes[i].depth).unwrap_or(i64::MAX) * (self.m.indent + self.m.px)
    }
    fn icon_span(&self, i: usize) -> i64 {
        if self.nodes[i].icon.is_empty() {
            0
        } else {
            self.m.icon + self.m.icon_gap
        }
    }
    fn label_x(&self, i: usize) -> i64 {
        self.indent(i) + self.m.px + self.icon_span(i)
    }
    fn width(&self, i: usize) -> i64 {
        (i64::from(self.nodes[i].label_width) + 2 * self.m.px + self.icon_span(i)).max(1)
    }
    fn extent(&self) -> (i64, i64) {
        let mut right = 0;
        let mut desc = 0;
        for (i, n) in self.nodes.iter().enumerate() {
            right = right.max(self.indent(i) + self.width(i));
            desc = desc.max(self.label_x(i) + i64::from(n.label_width) + self.m.desc_gap);
        }
        for n in &self.nodes {
            if !n.desc.is_empty() {
                right = right.max(desc + i64::from(n.desc_width) + self.m.px);
            }
        }
        (right, desc)
    }
    fn prefixes(&self) -> Vec<String> {
        let mut last = vec![None; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            if let Some(p) = n.parent {
                last[p] = Some(i);
            }
        }
        let mut trunk = vec![String::new(); self.nodes.len()];
        let mut prefixes = trunk.clone();
        for (i, n) in self.nodes.iter().enumerate() {
            if let Some(p) = n.parent {
                let (own, next) = if last[p] == Some(i) {
                    ("└── ", "    ")
                } else {
                    ("├── ", "│   ")
                };
                prefixes[i] = format!("{}{own}", trunk[p]);
                trunk[i] = format!("{}{next}", trunk[p]);
            }
        }
        prefixes
    }
    fn route(&self, i: usize) -> Result<Vec<Point>, GeomError> {
        let Some(p) = self.nodes[i].parent else {
            return Ok(Vec::new());
        };
        let height = self.m.height + 2 * self.m.py;
        let spine = narrow(self.indent(p) + self.m.px + self.m.margin)?;
        let bottom = narrow(
            (i64::try_from(p).map_err(|_| GeomError::Overflow)? + 1) * height + self.m.margin,
        )?;
        let mid = narrow(
            i64::try_from(i).map_err(|_| GeomError::Overflow)? * height
                + self.m.margin
                + floor_div(height, 2),
        )?;
        let end = Point {
            x: narrow(self.indent(i) + self.m.margin)?,
            y: mid,
        };
        let mut points = vec![
            Point {
                x: spine,
                y: bottom,
            },
            Point { x: spine, y: mid },
            end,
        ];
        if bottom == mid {
            points.remove(0);
        }
        Ok(points)
    }
    fn text(&self, rect: Rect, role: TextRole, style: TextStyle, run: Run) -> Item {
        Item::Text(TextItem {
            rect,
            role,
            size: 14,
            align: Align::Start,
            style,
            series: 0,
            lines: vec![vec![run]],
        })
    }
    fn node_items(
        &self,
        i: usize,
        rect: Rect,
        right: i64,
        desc: i64,
        prefix: &str,
    ) -> Result<Vec<Item>, GeomError> {
        let n = &self.nodes[i];
        let mut items = Vec::new();
        if n.class == "highlight" && self.input.profile == Profile::Vector {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Band),
                rect: Rect {
                    w: narrow(right + self.m.margin - i64::from(rect.x))?,
                    ..rect
                },
            }));
        }
        let y = narrow(i64::from(rect.y) + self.m.py)?;
        let height = narrow(self.m.height)?;
        if self.input.profile == Profile::Cell && !prefix.is_empty() {
            items.push(self.text(
                Rect {
                    x: narrow(self.m.margin)?,
                    y,
                    w: narrow(4 * i64::try_from(n.depth).map_err(|_| GeomError::Overflow)?)?,
                    h: height,
                },
                TextRole::Body,
                TextStyle::Text,
                Run {
                    text: prefix.into(),
                    bold: false,
                    italic: false,
                },
            ));
        }
        items.push(self.text(
            Rect {
                x: narrow(self.label_x(i) + self.m.margin)?,
                y,
                w: n.label_width,
                h: height,
            },
            if n.directory {
                TextRole::Label
            } else {
                TextRole::Body
            },
            TextStyle::Text,
            Run {
                text: n.shown(self.input.profile),
                bold: false,
                italic: false,
            },
        ));
        if !n.desc.is_empty() {
            items.push(self.text(
                Rect {
                    x: narrow(desc + self.m.margin)?,
                    y,
                    w: n.desc_width,
                    h: height,
                },
                TextRole::Body,
                TextStyle::TextMuted,
                Run {
                    text: n.desc.replace('\n', " "),
                    bold: false,
                    italic: true,
                },
            ));
        }
        Ok(items)
    }
}

pub fn layout(input: &Input) -> Result<(Scene, bool), LayoutError> {
    let p = Plan::new(input)?;
    let (right, desc) = p.extent();
    let height = p.m.height + 2 * p.m.py;
    let canvas = Size {
        w: narrow(right + 2 * p.m.margin)?,
        h: narrow(
            i64::try_from(p.nodes.len()).map_err(|_| GeomError::Overflow)? * height
                + 2 * p.m.margin,
        )?,
    };
    let mut dump = Dump::new("treeview", input.options.clone());
    for (i, b) in input.boxes.iter().enumerate() {
        dump.boxes.push(SceneBox {
            id: b.id.clone(),
            role: b.role,
            parent: String::new(),
            exclusive: b.exclusive,
            rect: Rect {
                x: narrow(p.indent(i) + p.m.margin)?,
                y: narrow(
                    i64::try_from(i).map_err(|_| GeomError::Overflow)? * height + p.m.margin,
                )?,
                w: narrow(p.width(i))?,
                h: narrow(height)?,
            },
        });
    }
    let mut groups = Vec::new();
    for route in &input.routes {
        let to = *p.index.get(route.to.as_str()).ok_or(GeomError::Domain)?;
        let points = p.route(to)?;
        let mut items = Vec::new();
        if input.profile == Profile::Vector {
            let mut shape = Shape::plain(ShapeStyle::Rule);
            shape.width = Width::Units(p.m.thickness);
            items.push(Item::Polyline(PolylineItem {
                shape,
                points: points.clone(),
                corner: 0,
            }));
        }
        groups.push(Group::new(GroupRole::Edge, route.id.clone()).with_items(items));
        dump.routes.push(SceneRoute {
            id: route.id.clone(),
            from: route.from.clone(),
            to: route.to.clone(),
            orthogonal: route.orthogonal,
            points,
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        });
    }
    let prefixes = p.prefixes();
    for (i, b) in dump.boxes.iter().enumerate() {
        groups.push(
            Group::new(GroupRole::Node, b.id.clone()).with_items(p.node_items(
                i,
                b.rect,
                right,
                desc,
                &prefixes[i],
            )?),
        );
    }
    Ok((Scene::new(canvas, dump, groups), false))
}

/// Places icons in the reserved icon slots after layout, using the caller's packs.
pub fn place_icons(
    input: &Input,
    scene: &mut Scene,
    packs: &[crate::icons::IconPack],
) -> Result<Vec<crate::diag::Diagnostic>, GeomError> {
    let plan = Plan::new(input)?;
    let mut diagnostics = Vec::new();
    for (i, node) in plan.nodes.iter().enumerate() {
        if node.icon.is_empty() {
            continue;
        }
        let owner = &input.boxes[i].id;
        let rect = scene.boxes().get(i).ok_or(GeomError::Domain)?.rect;
        let slot = Rect {
            x: narrow(plan.indent(i) + plan.m.px + plan.m.margin)?,
            y: if input.profile == Profile::Cell {
                rect.y
            } else {
                narrow(i64::from(rect.y) + floor_div(i64::from(rect.h), 2))?
            },
            w: narrow(plan.m.icon)?,
            h: 0,
        };
        let reference = crate::icons::IconRef {
            owner,
            name: &node.icon,
            span: crate::source::Span { start: 0, end: 0 },
            placement: crate::icons::Placement::Edge,
        };
        let (items, note) = crate::icons::items_for(&reference, slot, input.profile, packs);
        diagnostics.extend(note);
        let group = scene
            .items_mut()
            .iter_mut()
            .find(|g| g.role == GroupRole::Node && g.owner == *owner)
            .ok_or(GeomError::Domain)?;
        let at = group
            .items
            .iter()
            .position(|item| matches!(item, Item::Text(_)))
            .unwrap_or(group.items.len());
        group.items.splice(at..at, items);
    }
    Ok(diagnostics)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn treeview_preorder_and_description_alignment() -> Result<(), GeomError> {
        let source = "treeView-beta\n src/\n       a.rs ## first\n   b ## second\n other\n";
        let parsed = crate::syntax::treeview::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty());
        let (model, diagnostics) = crate::model::treeview::resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        assert_eq!(
            model
                .nodes
                .iter()
                .map(|n| (n.name.as_str(), n.parent))
                .collect::<Vec<_>>(),
            vec![
                ("/", None),
                ("src", Some(0)),
                ("a.rs", Some(1)),
                ("b", Some(1)),
                ("other", Some(0))
            ]
        );
        let input = from_treeview(&model, Profile::Cell, DumpOptions::default())?;
        let (scene, _) = layout(&input)?;
        let positions = scene
            .boxes()
            .iter()
            .map(|b| (b.rect.x, b.rect.y))
            .collect::<Vec<_>>();
        assert_eq!(positions, vec![(1, 1), (5, 2), (9, 3), (9, 4), (5, 5)]);
        let descriptions = scene
            .items()
            .iter()
            .flat_map(|g| &g.items)
            .filter_map(|item| match item {
                Item::Text(text) if text.style == TextStyle::TextMuted => Some(text.rect.x),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(descriptions.len(), 2);
        assert_eq!(descriptions[0], descriptions[1]);
        Ok(())
    }

    #[test]
    fn treeview_icon_uses_reserved_slot() -> Result<(), GeomError> {
        let source = "treeView-beta\n a icon(missing:x)\n";
        let parsed = crate::syntax::treeview::parse(source, &[]);
        let (model, _) = crate::model::treeview::resolve(source, &parsed.document);
        let input = from_treeview(&model, Profile::Cell, DumpOptions::default())?;
        let (mut scene, _) = layout(&input)?;
        let notes = place_icons(&input, &mut scene, &[])?;
        assert_eq!(notes.len(), 1);
        assert_eq!(notes[0].code, "icon/pack-missing");
        let symbols = scene
            .items()
            .iter()
            .flat_map(|g| &g.items)
            .filter_map(|item| match item {
                Item::SymbolRef(symbol) => Some(symbol.at),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(symbols, vec![Point { x: 5, y: 2 }]);
        let label = scene
            .items()
            .iter()
            .flat_map(|g| &g.items)
            .find_map(|item| match item {
                Item::Text(text) if text.lines.iter().flatten().any(|r| r.text == "a") => {
                    Some(text.rect.x)
                }
                _ => None,
            });
        assert_eq!(label, Some(7));
        Ok(())
    }
}
