//! Scene items of the gitgraph planner: lane lines, branch labels, routes, commit glyphs,
//! cell symbols, and tag plates (`spec/scene.md`, element styles).

use crate::geom::{Point, Rect};
use crate::scene::{
    Align, EllipseItem, Group, GroupRole, Item, Line, PolylineItem, RectItem, RoundRectItem, Shape,
    ShapeStyle, SymbolName, SymbolRefItem, TextItem, TextStyle, Width,
};

use super::gitgraph::{GitGraphResult, Planner, Text, half};
use super::result::Frame;

const TEXT_SIZE: i32 = 14;

fn plain(style: ShapeStyle) -> Shape {
    Shape::plain(style)
}

fn cell_symbol(kind: &str) -> &'static str {
    match kind {
        "reverse" => "ring",
        "highlight" => "diamond",
        "merge" | "merge-reverse" | "merge-highlight" => "bullseye",
        "cherry-pick" => "diamond-hollow",
        _ => "disc",
    }
}

fn narrow(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(0)
}

fn text_item(label: &Text, rect: Rect, align: Align) -> Item {
    Item::Text(TextItem {
        rect,
        role: label.role,
        size: TEXT_SIZE,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: label.runs.clone(),
    })
}

impl Planner<'_> {
    fn commit_align(&self) -> Align {
        if self.vertical() {
            Align::Start
        } else {
            Align::Middle
        }
    }

    pub fn paint(&self, frame: &mut Frame, result: &GitGraphResult) -> Vec<Group> {
        let mut groups = Vec::new();
        for (branch, lane) in self.input.branches.iter().enumerate() {
            let items = self.lane_items(frame, result, branch);
            groups.push(Group::new(GroupRole::Group, lane.id.clone()).with_items(items));
        }
        for (index, link) in self.input.links.iter().enumerate() {
            let items = self.edge_items(result, index);
            groups.push(Group::new(GroupRole::Edge, link.id.clone()).with_items(items));
        }
        for (index, commit) in self.input.commits.iter().enumerate() {
            let items = self.commit_items(result, index);
            groups.push(Group::new(GroupRole::Node, commit.id.clone()).with_items(items));
        }
        groups
    }

    fn lane_items(&self, frame: &mut Frame, result: &GitGraphResult, branch: usize) -> Vec<Item> {
        if !self.input.show_branches {
            return Vec::new();
        }
        let rank = self.rank[branch];
        let series = u8::try_from(rank % 12).unwrap_or(0);
        let mut line = plain(ShapeStyle::SeriesLine)
            .with_series(series)
            .with_line(Line::for_series(series));
        if !self.is_cell() {
            line = line.with_width(Width::Emphasis);
        }
        let points = vec![
            frame.point(self.starts[branch]),
            frame.point(self.ends[branch]),
        ];
        let mut items = vec![Item::Polyline(PolylineItem {
            shape: line,
            points,
            corner: 0,
        })];
        let Some(label) = self.shown_label(branch) else {
            return items;
        };
        if !self.is_cell() {
            items.push(Item::RoundRect(RoundRectItem {
                shape: plain(ShapeStyle::SeriesTint).with_series(series),
                rect: frame.rect(self.branches[branch]),
                r: narrow(self.c.corner_radius),
            }));
        }
        items.push(text_item(
            label,
            result.branch_labels[branch],
            Align::Middle,
        ));
        items
    }

    fn edge_items(&self, result: &GitGraphResult, index: usize) -> Vec<Item> {
        let mut shape = plain(ShapeStyle::Edge);
        if self.input.links[index].pick {
            shape = shape.with_line(Line::Dotted);
        }
        vec![Item::Polyline(PolylineItem {
            shape,
            points: result.routes[index].clone(),
            corner: narrow(self.c.corner_radius),
        })]
    }

    fn commit_items(&self, result: &GitGraphResult, index: usize) -> Vec<Item> {
        let commit = &self.input.commits[index];
        let mut items = self.marker(result, index);
        if let Some(label) = &commit.label {
            items.push(text_item(
                label,
                result.commit_labels[index],
                self.commit_align(),
            ));
        }
        for (k, tag) in commit.tags.iter().enumerate() {
            items.push(text_item(
                tag,
                result.tag_labels[index][k],
                self.commit_align(),
            ));
        }
        items
    }

    fn marker(&self, result: &GitGraphResult, index: usize) -> Vec<Item> {
        let commit = &self.input.commits[index];
        if self.is_cell() {
            let name = cell_symbol(&commit.kind);
            let symbol = SymbolName::new(name).or_else(|| SymbolName::new("disc"));
            return symbol
                .map(|symbol| {
                    vec![Item::SymbolRef(SymbolRefItem {
                        symbol,
                        at: result.points[index],
                        style: ShapeStyle::Mark,
                    })]
                })
                .unwrap_or_default();
        }
        let series = u8::try_from(self.rank[commit.branch] % 12).unwrap_or(0);
        let mut items = self.glyph(&commit.kind, result.points[index], series);
        for tag in &result.tag_labels[index] {
            items.push(self.tag_box(*tag));
        }
        items
    }

    fn tag_box(&self, text: Rect) -> Item {
        let pad = narrow(self.c.tag_pad);
        Item::RoundRect(RoundRectItem {
            shape: plain(ShapeStyle::Note),
            rect: Rect {
                x: text.x - pad,
                y: text.y - pad,
                w: text.w + 2 * pad,
                h: text.h + 2 * pad,
            },
            r: pad,
        })
    }

    fn glyph(&self, kind: &str, at: Point, series: u8) -> Vec<Item> {
        let r = narrow(self.c.commit_radius);
        let body = plain(ShapeStyle::Series).with_series(series);
        let mut items = if matches!(kind, "highlight" | "merge-highlight") {
            vec![Item::Rect(RectItem {
                shape: body,
                rect: Rect {
                    x: at.x - r,
                    y: at.y - r,
                    w: 2 * r,
                    h: 2 * r,
                },
            })]
        } else {
            vec![Item::Ellipse(EllipseItem {
                shape: body,
                cx: at.x,
                cy: at.y,
                rx: r,
                ry: r,
            })]
        };
        items.extend(decoration(kind, at, r));
        items
    }
}

fn decoration(kind: &str, at: Point, r: i32) -> Vec<Item> {
    let d = narrow(half(i64::from(r)));
    if kind == "cherry-pick" {
        return cherry(at, d);
    }
    let mut items = Vec::new();
    match kind {
        "reverse" | "merge-reverse" => items.extend(cross(at, d)),
        "highlight" | "merge-highlight" => items.push(Item::Rect(RectItem {
            shape: plain(ShapeStyle::MarkHollow),
            rect: Rect {
                x: at.x - d,
                y: at.y - d,
                w: 2 * d,
                h: 2 * d,
            },
        })),
        _ => {}
    }
    if matches!(kind, "merge" | "merge-reverse" | "merge-highlight") {
        items.push(Item::Ellipse(EllipseItem {
            shape: plain(ShapeStyle::MarkHollow),
            cx: at.x,
            cy: at.y,
            rx: d,
            ry: d,
        }));
    }
    items
}

fn stroke(points: Vec<Point>) -> Item {
    Item::Polyline(PolylineItem {
        shape: plain(ShapeStyle::InkLine),
        points,
        corner: 0,
    })
}

fn cross(at: Point, d: i32) -> Vec<Item> {
    vec![
        stroke(vec![
            Point {
                x: at.x - d,
                y: at.y - d,
            },
            Point {
                x: at.x + d,
                y: at.y + d,
            },
        ]),
        stroke(vec![
            Point {
                x: at.x - d,
                y: at.y + d,
            },
            Point {
                x: at.x + d,
                y: at.y - d,
            },
        ]),
    ]
}

fn cherry(at: Point, d: i32) -> Vec<Item> {
    let dot = narrow(half(i64::from(d)));
    let left = Point {
        x: at.x - d,
        y: at.y - dot,
    };
    let right = Point {
        x: at.x + d,
        y: at.y - dot,
    };
    let stem = Point {
        x: at.x,
        y: at.y + d,
    };
    let bead = |centre: Point| {
        Item::Ellipse(EllipseItem {
            shape: plain(ShapeStyle::Ink),
            cx: centre.x,
            cy: centre.y,
            rx: dot,
            ry: dot,
        })
    };
    vec![
        stroke(vec![left, stem]),
        stroke(vec![right, stem]),
        bead(left),
        bead(right),
    ]
}
