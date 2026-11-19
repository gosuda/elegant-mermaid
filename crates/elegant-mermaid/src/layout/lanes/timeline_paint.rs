//! Scene items of the timeline planner: the time axis, dotted event links, the title, and
//! section, period, and event cards (`spec/scene.md`, element styles).

use crate::geom::{Point, Rect};
use crate::scene::{
    Align, Group, GroupRole, Item, Line, MarkerAxis, MarkerName, MarkerRefItem, PolylineItem,
    RectItem, RoundRectItem, Shape, ShapeStyle, TextItem, TextRole, TextStyle, Width,
};

use super::gitgraph::{Text, half};
use super::timeline::{Planner, TimelineResult};
use super::timeline_result::Shift;

const TITLE_SIZE: i32 = 16;
const TEXT_SIZE: i32 = 14;
const SERIES_MAX: usize = 12;

#[derive(Clone, Copy, PartialEq, Eq)]
enum CardKind {
    Section,
    Period,
    Event,
}

fn narrow(value: i64) -> i32 {
    i32::try_from(value).unwrap_or(0)
}

fn series_index(value: usize) -> u8 {
    u8::try_from(value % SERIES_MAX).unwrap_or(0)
}

impl Planner<'_> {
    fn series(&self, period: usize) -> u8 {
        if self.input.sections.is_empty() {
            return series_index(period);
        }
        self.input.periods[period].section.map_or(0, series_index)
    }

    pub fn paint(&self, shift: &mut Shift, result: &TimelineResult) -> Vec<Group> {
        let mut groups = vec![self.axis_group(shift)];
        for (i, period) in self.input.periods.iter().enumerate() {
            for (k, event) in period.events.iter().enumerate() {
                let items = self.link_items(&result.routes[i][k]);
                groups.push(Group::new(GroupRole::Edge, event.link.clone()).with_items(items));
            }
        }
        if let Some(title) = &self.input.title {
            let item = self.text_item(&title.label, result.title);
            groups.push(Group::new(GroupRole::Node, title.id.clone()).with_items(vec![item]));
        }
        for (s, section) in self.input.sections.iter().enumerate() {
            let series = series_index(s);
            let rect = result.sections[s];
            groups.push(self.card(&section.id, CardKind::Section, series, &section.label, rect));
        }
        for (i, period) in self.input.periods.iter().enumerate() {
            let rect = result.periods[i];
            groups.push(self.card(
                &period.id,
                CardKind::Period,
                self.series(i),
                &period.label,
                rect,
            ));
            for (k, event) in period.events.iter().enumerate() {
                let rect = result.events[i][k];
                groups.push(self.card(&event.id, CardKind::Event, 0, &event.label, rect));
            }
        }
        groups
    }

    fn axis_group(&self, shift: &mut Shift) -> Group {
        let line = Shape::plain(ShapeStyle::Edge).with_width(Width::Emphasis);
        let end = shift.point(self.axis[1]);
        let axis = if self.vertical() {
            MarkerAxis::PlusY
        } else {
            MarkerAxis::PlusX
        };
        let mut items = vec![Item::Polyline(PolylineItem {
            shape: line,
            points: vec![shift.point(self.axis[0]), end],
            corner: 0,
        })];
        if let Some(marker) = MarkerName::new("point") {
            items.push(Item::MarkerRef(MarkerRefItem {
                marker,
                at: end,
                axis,
            }));
        }
        Group::new(GroupRole::Decor, "").with_items(items)
    }

    fn link_items(&self, route: &[Point]) -> Vec<Item> {
        vec![Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Edge).with_line(Line::Dotted),
            points: route.to_vec(),
            corner: narrow(self.c.corner_radius),
        })]
    }

    fn card(&self, id: &str, kind: CardKind, series: u8, label: &Text, rect: Rect) -> Group {
        let items = vec![
            self.card_shape(kind, series, rect),
            self.text_item(label, text_rect(label, rect)),
        ];
        Group::new(GroupRole::Node, id).with_items(items)
    }

    fn card_shape(&self, kind: CardKind, series: u8, rect: Rect) -> Item {
        let mut shape = Shape::plain(ShapeStyle::Node);
        if kind != CardKind::Event {
            shape = Shape::plain(ShapeStyle::SeriesTint).with_series(series);
        }
        if kind == CardKind::Section {
            shape = shape.with_width(Width::Emphasis);
        }
        if self.is_cell() && kind != CardKind::Period {
            return Item::Rect(RectItem { shape, rect });
        }
        Item::RoundRect(RoundRectItem {
            shape,
            rect,
            r: narrow(self.c.corner_radius),
        })
    }

    fn text_item(&self, label: &Text, rect: Rect) -> Item {
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
            style: TextStyle::Text,
            series: 0,
            lines: label.runs.clone(),
        })
    }
}

fn text_rect(label: &Text, card: Rect) -> Rect {
    let count = i64::try_from(label.lines.len()).unwrap_or(0);
    let height = count * (i64::from(label.h) / count.max(1));
    Rect {
        x: card.x,
        y: card.y + narrow(half(i64::from(card.h) - height)),
        w: card.w,
        h: narrow(height),
    }
}
