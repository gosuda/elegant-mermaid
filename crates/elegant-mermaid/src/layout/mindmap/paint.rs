use super::Plan;
use crate::geom::{Point, Rect, cos_q15, floor_div, sin_q15};
use crate::scene::{
    Align, Dump, EllipseItem, Group, GroupRole, Item, Line, PathCommand, PathItem, PolygonItem,
    PolylineItem, Profile, RectItem, RoundRectItem, Shape, ShapeStyle, TextItem, TextRole,
    TextStyle, Width,
};

const CLOUD_BUMPS: i32 = 8;
const CLOUD_BASE: i64 = 27525;
const CLOUD_CONTROL: i64 = 35062;
const BANG_SPIKES: i32 = 8;
const BANG_INNER: i64 = 20316;
const UNIT_Q15: i64 = 32768;
const TURN_Q16: i32 = 65536;
const POLAR_Q30: i64 = 1 << 30;
const LABEL_SIZE_PX: i32 = 14;

impl Plan<'_> {
    pub(super) fn groups(&self, dump: &Dump) -> Vec<Group> {
        let mut groups = Vec::with_capacity(dump.routes.len() + dump.boxes.len());
        for route in &dump.routes {
            let line = Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Edge),
                points: route.points.clone(),
                corner: self.c.corner,
            });
            groups.push(Group::new(GroupRole::Edge, route.id.clone()).with_items(vec![line]));
        }
        for (i, scene_box) in dump.boxes.iter().enumerate() {
            let name = self.input.boxes.get(i).map_or("", |b| b.shape.as_str());
            let mut items = self.shape(name, scene_box.rect);
            items.push(Item::Text(self.text(scene_box.rect, i)));
            groups.push(Group::new(GroupRole::Node, scene_box.id.clone()).with_items(items));
        }
        groups
    }

    fn text(&self, rect: Rect, index: usize) -> TextItem {
        let runs = self
            .measured
            .get(index)
            .map_or_else(Vec::new, |measured| measured.runs.clone());
        let count = i32::try_from(runs.len()).unwrap_or(i32::MAX);
        let height = count.saturating_mul(self.c.line_height);
        let offset =
            i32::try_from(floor_div(i64::from(rect.h) - i64::from(height), 2)).unwrap_or_default();
        TextItem {
            rect: Rect {
                x: rect.x,
                y: rect.y + offset,
                w: rect.w,
                h: height,
            },
            role: TextRole::Label,
            size: LABEL_SIZE_PX,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: runs,
        }
    }

    fn shape(&self, name: &str, rect: Rect) -> Vec<Item> {
        match self.input.profile {
            Profile::Cell => cell_shape(name, rect),
            Profile::Vector => self.vector_shape(name, rect),
        }
    }

    fn vector_shape(&self, name: &str, rect: Rect) -> Vec<Item> {
        let node = Shape::plain(ShapeStyle::Node);
        let centre = Point {
            x: rect.x + rect.w / 2,
            y: rect.y + rect.h / 2,
        };
        let round = |style| {
            Item::RoundRect(RoundRectItem {
                shape: Shape::plain(style),
                rect,
                r: self.c.corner,
            })
        };
        vec![match name {
            "defaultMindmapNode" => round(ShapeStyle::Band),
            "rounded" => round(ShapeStyle::Node),
            "mindmapCircle" => Item::Ellipse(EllipseItem {
                shape: node,
                cx: centre.x,
                cy: centre.y,
                rx: rect.w / 2,
                ry: rect.h / 2,
            }),
            "hexagon" => Item::Polygon(PolygonItem {
                shape: node,
                points: hexagon_points(rect, centre),
            }),
            "bang" => Item::Polygon(PolygonItem {
                shape: node,
                points: bang_points(rect, centre),
            }),
            "cloud" => Item::Path(PathItem {
                shape: node,
                commands: cloud_commands(rect, centre),
            }),
            _ => Item::Rect(RectItem { shape: node, rect }),
        }]
    }
}

fn cell_shape(name: &str, rect: Rect) -> Vec<Item> {
    let mut node = Shape::plain(ShapeStyle::Node);
    match name {
        "defaultMindmapNode" => return Vec::new(),
        "rounded" | "mindmapCircle" => {
            return vec![Item::RoundRect(RoundRectItem {
                shape: node,
                rect,
                r: 0,
            })];
        }
        "cloud" => {
            node.line = Line::Dotted;
            return vec![Item::RoundRect(RoundRectItem {
                shape: node,
                rect,
                r: 0,
            })];
        }
        "bang" => node.line = Line::Double,
        "hexagon" => node.width = Width::Emphasis,
        _ => {}
    }
    vec![Item::Rect(RectItem { shape: node, rect })]
}

fn hexagon_points(rect: Rect, centre: Point) -> Vec<Point> {
    let inset = (rect.h / 4).min(rect.w / 4);
    let right = rect.x + rect.w;
    let bottom = rect.y + rect.h;
    let at = |x, y| Point { x, y };
    vec![
        at(rect.x + inset, rect.y),
        at(right - inset, rect.y),
        at(right, centre.y),
        at(right - inset, bottom),
        at(rect.x + inset, bottom),
        at(rect.x, centre.y),
    ]
}

fn polar(rect: Rect, centre: Point, angle: i32, factor: i64) -> Point {
    let rx = i64::from(rect.w / 2);
    let ry = i64::from(rect.h / 2);
    let dx = floor_div(rx * i64::from(cos_q15(angle)) * factor, POLAR_Q30);
    let dy = floor_div(ry * i64::from(sin_q15(angle)) * factor, POLAR_Q30);
    Point {
        x: centre.x + i32::try_from(dx).unwrap_or_default(),
        y: centre.y + i32::try_from(dy).unwrap_or_default(),
    }
}

fn bang_points(rect: Rect, centre: Point) -> Vec<Point> {
    (0..2 * BANG_SPIKES)
        .map(|k| {
            let factor = if k % 2 == 1 { BANG_INNER } else { UNIT_Q15 };
            polar(rect, centre, k * TURN_Q16 / (2 * BANG_SPIKES), factor)
        })
        .collect()
}

fn cloud_commands(rect: Rect, centre: Point) -> Vec<PathCommand> {
    let step = TURN_Q16 / CLOUD_BUMPS;
    let mut commands = vec![PathCommand::Move(polar(rect, centre, 0, CLOUD_BASE))];
    for k in 0..CLOUD_BUMPS {
        let from = k * step;
        commands.push(PathCommand::Curve {
            c1: polar(rect, centre, from + step / 3, CLOUD_CONTROL),
            c2: polar(rect, centre, from + 2 * step / 3, CLOUD_CONTROL),
            to: polar(rect, centre, from + step, CLOUD_BASE),
        });
    }
    commands.push(PathCommand::Close);
    commands
}
