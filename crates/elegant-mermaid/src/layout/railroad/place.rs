use super::rails::point_of;
use super::size::{Shape, measure};
use super::tree::{Constants, Kind, Params, Pt, Rule, fit, route_id};
use crate::geom::{GeomError, Point, Rect, Size, floor_div};
use crate::scene::{
    Align, BoxRole, Dump, EllipseItem, Group, GroupRole, Item, Line, PolylineItem, RectItem,
    RoundRectItem, Run, Scene, SceneBox, SceneLabel, SceneRoute, Shape as SceneShape, ShapeStyle,
    TextItem, TextRole, TextStyle,
};

const KIND_NAME: &str = "railroad";

pub(super) struct Layouter {
    pub p: Params,
    pub k: Constants,
    dump: Dump,
    groups: Vec<Group>,
    edges: Vec<Group>,
    nodes: Vec<Group>,
}

pub(super) fn layout(rules: &[Rule], p: Params) -> Result<Scene, GeomError> {
    let mut l = Layouter {
        k: p.constants,
        dump: Dump::new(KIND_NAME, p.options.clone()),
        p,
        groups: Vec::new(),
        edges: Vec::new(),
        nodes: Vec::new(),
    };
    if rules.is_empty() {
        let (width, height) = (l.k.empty_width, l.k.empty_height);
        return l.finish(width, height);
    }
    let mut y = l.k.margin;
    let mut widest = 0;
    for rule in rules {
        let (height, width) = l.place_rule(rule, l.k.margin, y)?;
        y += height + l.k.vsep;
        widest = widest.max(width);
    }
    let (width, height) = (widest + 2 * l.k.margin, y + l.k.margin);
    l.finish(width, height)
}

struct RuleGeometry {
    title: i64,
    name_w: i64,
    def_x: i64,
    baseline: i64,
    def_y: i64,
    width: i64,
    height: i64,
}

fn rect_of(x: i64, y: i64, w: i64, h: i64) -> Result<Rect, GeomError> {
    Ok(Rect {
        x: fit(x)?,
        y: fit(y)?,
        w: fit(w)?,
        h: fit(h)?,
    })
}

fn text_item(rect: Rect, text: &str, align: Align) -> Item {
    Item::Text(TextItem {
        rect,
        role: TextRole::Label,
        size: 14,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: vec![vec![Run::plain(text)]],
    })
}

impl Layouter {
    fn finish(self, width: i64, height: i64) -> Result<Scene, GeomError> {
        let canvas = Size {
            w: fit(width)?,
            h: fit(height)?,
        };
        let mut groups = self.groups;
        groups.extend(self.edges);
        groups.extend(self.nodes);
        Ok(Scene::new(canvas, self.dump, groups))
    }

    fn rule_geometry(&self, rule: &Rule, root: &Shape<'_>) -> Result<RuleGeometry, GeomError> {
        let c = &self.k;
        let title = i64::from(self.p.metric.width(&rule.title)?);
        let name_w = title + c.rule_name_gap;
        let def_x = name_w + c.rule_name_gap;
        let baseline = c.rule_min_baseline.max(root.up);
        let def_y = baseline - root.up;
        Ok(RuleGeometry {
            title,
            name_w,
            def_x,
            baseline,
            def_y,
            width: def_x + root.w + c.rule_end_gap + c.marker_radius,
            height: c.rule_min_height.max(def_y + root.height() + 2 * c.margin),
        })
    }

    fn place_rule(&mut self, rule: &Rule, x: i64, y: i64) -> Result<(i64, i64), GeomError> {
        let root = measure(&rule.root, &self.p)?;
        let g = self.rule_geometry(rule, &root)?;
        fit(x + g.width + self.k.margin)?;
        fit(y + g.height)?;
        if !rule.id.is_empty() {
            let margin = self.k.margin;
            self.dump.boxes.push(SceneBox {
                id: rule.id.clone(),
                role: BoxRole::Group,
                rect: rect_of(x - margin, y, g.width + 2 * margin, g.height)?,
                parent: String::new(),
                exclusive: false,
            });
            let items = self.rule_items(rule, &root, &g, x, y)?;
            self.groups
                .push(Group::new(GroupRole::Group, rule.id.clone()).with_items(items));
        }
        self.place_node(&root, x + g.def_x, y + g.def_y, &rule.id)?;
        Ok((g.height, g.width))
    }

    fn rule_items(
        &mut self,
        rule: &Rule,
        root: &Shape<'_>,
        g: &RuleGeometry,
        x: i64,
        y: i64,
    ) -> Result<Vec<Item>, GeomError> {
        let c = self.k;
        let base = y + g.baseline;
        let def_right = x + g.def_x + root.w;
        let mut items = vec![
            self.rail(&[
                Pt {
                    x: x + g.name_w + c.marker_radius,
                    y: base,
                },
                Pt {
                    x: x + g.def_x,
                    y: base,
                },
            ])?,
            self.rail(&[
                Pt {
                    x: self.right_start(root, def_right),
                    y: base,
                },
                Pt {
                    x: def_right + c.rule_end_gap - c.marker_radius,
                    y: base,
                },
            ])?,
            self.marker(x + g.name_w, base)?,
            self.marker(def_right + c.rule_end_gap, base)?,
        ];
        let label = rect_of(
            x,
            base - floor_div(c.line_height, 2),
            g.title,
            c.line_height,
        )?;
        self.dump.labels.push(SceneLabel {
            id: format!("{}.label", rule.id),
            owner: rule.id.clone(),
            text: rule.title.clone(),
            rect: label,
            lines: vec![rule.title.clone()],
        });
        items.push(text_item(label, &rule.title, Align::Start));
        Ok(items)
    }

    fn marker(&self, cx: i64, cy: i64) -> Result<Item, GeomError> {
        let r = fit(self.k.marker_radius)?;
        Ok(Item::Ellipse(EllipseItem {
            shape: SceneShape::plain(ShapeStyle::Ink),
            cx: fit(cx)?,
            cy: fit(cy)?,
            rx: r,
            ry: r,
        }))
    }

    fn place_node(&mut self, s: &Shape<'_>, x: i64, y: i64, parent: &str) -> Result<(), GeomError> {
        let n = s.node;
        let rect = rect_of(x, y, s.w, s.height())?;
        let leaf = n.kind.leaf();
        let role = if leaf { BoxRole::Node } else { BoxRole::Group };
        self.dump.boxes.push(SceneBox {
            id: n.id.clone(),
            role,
            rect,
            parent: parent.to_owned(),
            exclusive: leaf,
        });
        if leaf {
            let items = self.leaf_items(s, rect)?;
            self.nodes
                .push(Group::new(GroupRole::Node, n.id.clone()).with_items(items));
            return Ok(());
        }
        let rails = self.rails(s, x, y)?;
        self.groups
            .push(Group::new(GroupRole::Group, n.id.clone()).with_items(rails));
        if n.kind == Kind::Sequence {
            self.joins(s, x, y)?;
        }
        for (kid, offset) in s.kids.iter().zip(&s.offsets) {
            self.place_node(kid, x + offset.x, y + offset.y, &n.id)?;
        }
        Ok(())
    }

    fn leaf_items(&self, s: &Shape<'_>, rect: Rect) -> Result<Vec<Item>, GeomError> {
        let n = s.node;
        let mut shape = SceneShape::plain(ShapeStyle::Node);
        let outline = match n.kind {
            Kind::Terminal => Item::RoundRect(RoundRectItem {
                shape,
                rect,
                r: fit(self.k.terminal_radius)?,
            }),
            Kind::Special => {
                shape = shape.with_line(Line::Dashed);
                Item::Rect(RectItem { shape, rect })
            }
            _ => Item::Rect(RectItem { shape, rect }),
        };
        let line = fit(self.k.line_height)?;
        let text = Rect {
            x: rect.x,
            y: rect.y + (rect.h - line) / 2,
            w: rect.w,
            h: line,
        };
        Ok(vec![outline, text_item(text, &n.text, Align::Middle)])
    }

    fn joins(&mut self, s: &Shape<'_>, x: i64, y: i64) -> Result<(), GeomError> {
        let line = y + s.up;
        for ((from, to), offsets) in s
            .kids
            .iter()
            .zip(s.kids.iter().skip(1))
            .zip(s.offsets.windows(2))
        {
            let start = Pt {
                x: x + offsets[0].x + from.w,
                y: line,
            };
            let end = Pt {
                x: x + offsets[1].x,
                y: line,
            };
            let id = route_id(self.dump.routes.len());
            let points: Vec<Point> = vec![point_of(start)?, point_of(end)?];
            self.dump.routes.push(SceneRoute {
                id: id.clone(),
                from: from.node.id.clone(),
                to: to.node.id.clone(),
                orthogonal: true,
                points: points.clone(),
                marker_start: String::new(),
                marker_end: String::new(),
                stroke: "normal".into(),
            });
            self.edges.push(
                Group::new(GroupRole::Edge, id).with_items(vec![Item::Polyline(PolylineItem {
                    shape: SceneShape::plain(ShapeStyle::Edge),
                    points,
                    corner: 0,
                })]),
            );
        }
        Ok(())
    }
}
