//! Scene items of the journey planner: section bands, the title, task cards, and faces
//! (`spec/scene.md`, element styles).

use crate::geom::{Point, Rect, floor_div};
use crate::scene::{
    Align, EllipseItem, Group, GroupRole, Item, PathCommand, PathItem, PolylineItem, RoundRectItem,
    Shape, ShapeStyle, SymbolName, SymbolRefItem, TextItem, TextRole, TextStyle, Width,
};

use super::gitgraph::{Text, half};
use super::journey::{JourneyResult, Planner};
use super::journey_result::Shift;

const TITLE_SIZE: i32 = 16;
const TEXT_SIZE: i32 = 14;
const SERIES_MAX: usize = 12;
const HALF_TURN: i32 = 32768;

fn narrow(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(0)
}

fn series(band: usize) -> Shape {
    let index = u8::try_from(band % SERIES_MAX).unwrap_or(0);
    Shape::plain(ShapeStyle::SeriesTint).with_series(index)
}

impl Planner<'_> {
    pub fn paint(&self, shift: &mut Shift, result: &JourneyResult) -> Vec<Group> {
        let input = self.input;
        let mut groups = Vec::with_capacity(input.sections.len() + input.tasks.len() + 1);
        for (b, section) in input.sections.iter().enumerate() {
            let items = self.band_items(shift, result, b);
            groups.push(Group::new(GroupRole::Group, section.id.clone()).with_items(items));
        }
        if let Some(title) = &input.title {
            let item = self.text_item(&title.label, result.title, TextStyle::Text);
            groups.push(Group::new(GroupRole::Node, title.id.clone()).with_items(vec![item]));
        }
        for (k, task) in input.tasks.iter().enumerate() {
            let items = self.task_items(shift, result, k);
            groups.push(Group::new(GroupRole::Node, task.id.clone()).with_items(items));
        }
        groups
    }

    fn card(&self, shape: Shape, rect: Rect) -> Item {
        Item::RoundRect(RoundRectItem {
            shape,
            rect,
            r: narrow(self.c.corner_radius),
        })
    }

    fn band_items(&self, shift: &mut Shift, result: &JourneyResult, band: usize) -> Vec<Item> {
        let shape = series(band).with_width(Width::Emphasis);
        let label = &self.input.sections[band].label;
        let text = shift.rect(self.sections[band]);
        vec![
            self.card(shape, result.bands[band]),
            self.text_item(label, text, TextStyle::Text),
        ]
    }

    fn task_items(&self, shift: &mut Shift, result: &JourneyResult, k: usize) -> Vec<Item> {
        let task = &self.input.tasks[k];
        let shape = task
            .band
            .map_or_else(|| Shape::plain(ShapeStyle::Node), series);
        let mut items = vec![self.card(shape, result.tasks[k])];
        items.extend(self.face(result.faces[k], task.score));
        let name = shift.rect(self.names[k]);
        items.push(self.text_item(&task.label, name, TextStyle::Text));
        if let Some(people) = &task.people {
            let rect = shift.rect(self.people[k]);
            items.push(self.text_item(people, rect, TextStyle::TextMuted));
        }
        items
    }

    fn text_item(&self, label: &Text, rect: Rect, style: TextStyle) -> Item {
        let size = if label.role == TextRole::Title {
            TITLE_SIZE
        } else {
            TEXT_SIZE
        };
        Item::Text(TextItem {
            rect,
            role: label.role,
            size,
            align: Align::Middle,
            style,
            series: 0,
            lines: label.runs.clone(),
        })
    }

    fn face(&self, at: Point, score: i64) -> Vec<Item> {
        if self.is_cell() {
            return SymbolName::new("ring")
                .map(|symbol| {
                    vec![Item::SymbolRef(SymbolRefItem {
                        symbol,
                        at,
                        style: ShapeStyle::InkLine,
                    })]
                })
                .unwrap_or_default();
        }
        let r = self.c.face_radius;
        let third = narrow(floor_div(r, 3));
        let eye = narrow(floor_div(r, 6).max(1));
        let ellipse = |style: ShapeStyle, cx: i32, cy: i32, radius: i32| {
            Item::Ellipse(EllipseItem {
                shape: Shape::plain(style),
                cx,
                cy,
                rx: radius,
                ry: radius,
            })
        };
        vec![
            ellipse(ShapeStyle::InkLine, at.x, at.y, narrow(r)),
            ellipse(ShapeStyle::Ink, at.x - third, at.y - third, eye),
            ellipse(ShapeStyle::Ink, at.x + third, at.y - third, eye),
            self.mouth(at, r, third, score),
        ]
    }

    fn mouth(&self, at: Point, r: i64, third: i32, score: i64) -> Item {
        let mid = half(self.c.score_min + self.c.score_max);
        let radius = narrow(floor_div(r, 2));
        if score > mid {
            return arc_mouth(at.x, at.y + narrow(floor_div(2 * r, 15)), radius, HALF_TURN);
        }
        if score < mid {
            return arc_mouth(
                at.x,
                at.y + narrow(floor_div(7 * r, 15)),
                radius,
                -HALF_TURN,
            );
        }
        let y = at.y + narrow(floor_div(7 * r, 15));
        Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::InkLine),
            points: vec![Point { x: at.x - third, y }, Point { x: at.x + third, y }],
            corner: 0,
        })
    }
}

fn arc_mouth(cx: i32, cy: i32, radius: i32, sweep: i32) -> Item {
    Item::Path(PathItem {
        shape: Shape::plain(ShapeStyle::InkLine),
        commands: vec![
            PathCommand::Move(Point {
                x: cx + radius,
                y: cy,
            }),
            PathCommand::Arc {
                centre: Point { x: cx, y: cy },
                r: radius,
                start: 0,
                sweep,
            },
        ],
    })
}
