//! Extent, canvas margin, and scene items of the eventmodeling planner
//! (`spec/scene.md`, element styles).

use crate::geom::{COORD_LIMIT, Point, Rect, Size, floor_div};
use crate::layout::layered::LayoutError;
use crate::scene::{
    Align, Group, GroupRole, Item, MarkerAxis, MarkerName, MarkerRefItem, PolylineItem, Profile,
    RectItem, RoundRectItem, Shape, ShapeStyle, TextItem, TextStyle,
};

use super::Text;
use super::eventmodeling::{EventBox, EventModelingResult, EventPlanner, EventPoint};

const TEXT_SIZE: i32 = 14;

struct Shift {
    dx: i64,
    dy: i64,
    overflow: bool,
}

impl Shift {
    fn fit(&mut self, value: i64) -> i32 {
        if value.abs() > COORD_LIMIT {
            self.overflow = true;
            return 0;
        }
        i32::try_from(value).unwrap_or(0)
    }

    fn point(&mut self, point: EventPoint) -> Point {
        Point {
            x: self.fit(point.x + self.dx),
            y: self.fit(point.y + self.dy),
        }
    }

    fn rect(&mut self, area: EventBox) -> Rect {
        Rect {
            x: self.fit(area.x + self.dx),
            y: self.fit(area.y + self.dy),
            w: self.fit(area.w),
            h: self.fit(area.h),
        }
    }
}

fn union(a: EventBox, b: EventBox) -> EventBox {
    let (x, y) = (a.x.min(b.x), a.y.min(b.y));
    EventBox {
        x,
        y,
        w: (a.x + a.w).max(b.x + b.w) - x,
        h: a.bottom().max(b.bottom()) - y,
    }
}

fn text_item(text: &Text, rect: Rect, align: Align) -> Item {
    Item::Text(TextItem {
        rect,
        role: text.role,
        size: TEXT_SIZE,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: text.runs.clone(),
    })
}

fn frame_style(category: &str) -> ShapeStyle {
    match category {
        "command" => ShapeStyle::Note,
        "readmodel" => ShapeStyle::Success,
        "event" => ShapeStyle::Warning,
        "processor" => ShapeStyle::MarkHollow,
        _ => ShapeStyle::Node,
    }
}

fn arrow_axis(a: Point, b: Point) -> MarkerAxis {
    let dx = i64::from(b.x) - i64::from(a.x);
    let dy = i64::from(b.y) - i64::from(a.y);
    match (dx.abs() >= dy.abs(), dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

impl EventPlanner<'_> {
    fn lane_box(&self, lane: usize) -> EventBox {
        EventBox {
            x: 0,
            y: self.lane_y[lane],
            w: self.max_r + self.c.lane_padding,
            h: self.lane_h[lane],
        }
    }

    fn label_box(&self, lane: usize) -> EventBox {
        match &self.input.lanes[lane].label {
            None => EventBox::default(),
            Some(label) => EventBox {
                x: self.c.label_inset(),
                y: self.lane_y[lane] + self.c.lane_padding,
                w: i64::from(label.w),
                h: i64::from(label.h),
            },
        }
    }

    fn frame_texts(&self, index: usize) -> (EventBox, EventBox) {
        let c = &self.c;
        let frame = &self.input.frames[index];
        let placed = self.frames[index];
        let area_x = placed.x + c.box_padding;
        let area_y = placed.y + c.box_padding;
        let area_w = placed.w - 2 * c.box_padding;
        let area_h = placed.h - 2 * c.box_padding;
        let name_h = i64::from(frame.name.h);
        let mut total = name_h;
        if let Some(data) = &frame.data {
            total += c.line_height + i64::from(data.h);
        }
        let top = area_y + floor_div(area_h - total, 2).max(0);
        let name = EventBox {
            x: area_x,
            y: top,
            w: area_w,
            h: name_h,
        };
        let data = frame
            .data
            .as_ref()
            .map_or_else(EventBox::default, |data| EventBox {
                x: area_x,
                y: top + name_h + c.line_height,
                w: area_w,
                h: i64::from(data.h),
            });
        (name, data)
    }

    fn extent(&self) -> EventBox {
        let mut extent = EventBox::default();
        for lane in 0..self.input.lanes.len() {
            extent = union(extent, self.lane_box(lane));
            extent = union(extent, self.label_box(lane));
        }
        for index in 0..self.input.frames.len() {
            let (name, data) = self.frame_texts(index);
            extent = union(union(union(extent, self.frames[index]), name), data);
        }
        for point in self.routes.iter().flatten() {
            extent = union(
                extent,
                EventBox {
                    x: point.x,
                    y: point.y,
                    w: 0,
                    h: 0,
                },
            );
        }
        extent
    }

    pub(super) fn result(&self) -> Result<EventModelingResult, LayoutError> {
        let extent = self.extent();
        let margin = self.c.canvas_margin;
        let mut shift = Shift {
            dx: margin - extent.x,
            dy: margin - extent.y,
            overflow: false,
        };
        let canvas = Size {
            w: shift.fit(extent.w + 2 * margin),
            h: shift.fit(extent.h + 2 * margin),
        };
        let lane_count = self.input.lanes.len();
        let lanes = (0..lane_count)
            .map(|lane| shift.rect(self.lane_box(lane)))
            .collect();
        let lane_labels = (0..lane_count)
            .map(|lane| shift.rect(self.label_box(lane)))
            .collect();
        let frames = self.frames.iter().map(|&area| shift.rect(area)).collect();
        let routes = self
            .routes
            .iter()
            .map(|route| route.iter().map(|&point| shift.point(point)).collect())
            .collect();
        if shift.overflow {
            return Err(LayoutError::Overflow);
        }
        let mut result = EventModelingResult {
            canvas,
            lanes,
            lane_labels,
            frames,
            routes,
            groups: Vec::new(),
        };
        result.groups = self.paint(&mut shift, &result)?;
        if shift.overflow {
            return Err(LayoutError::Overflow);
        }
        Ok(result)
    }

    fn paint(
        &self,
        shift: &mut Shift,
        result: &EventModelingResult,
    ) -> Result<Vec<Group>, LayoutError> {
        let mut groups = Vec::new();
        for (lane, input) in self.input.lanes.iter().enumerate() {
            if !input.id.is_empty() {
                let items = self.lane_items(lane, result);
                groups.push(Group::new(GroupRole::Group, input.id.clone()).with_items(items));
            }
        }
        for (index, relation) in self.input.relations.iter().enumerate() {
            let items = self.edge_items(&result.routes[index]);
            groups.push(Group::new(GroupRole::Edge, relation.id.clone()).with_items(items));
        }
        for (index, frame) in self.input.frames.iter().enumerate() {
            let items = self.frame_items(shift, result, index)?;
            groups.push(Group::new(GroupRole::Node, frame.id.clone()).with_items(items));
        }
        Ok(groups)
    }

    fn lane_items(&self, lane: usize, result: &EventModelingResult) -> Vec<Item> {
        let mut items = Vec::new();
        if self.profile == Profile::Vector {
            items.push(Item::Rect(RectItem {
                shape: Shape::plain(ShapeStyle::Band),
                rect: result.lanes[lane],
            }));
        }
        items.push(Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Group),
            rect: result.lanes[lane],
        }));
        if let Some(label) = &self.input.lanes[lane].label {
            items.push(text_item(label, result.lane_labels[lane], Align::Start));
        }
        items
    }

    fn edge_items(&self, points: &[Point]) -> Vec<Item> {
        let corner = i32::try_from(self.c.corner_radius).unwrap_or(0);
        let mut items = vec![Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Edge),
            points: points.to_vec(),
            corner,
        })];
        let marker = MarkerName::new("point");
        if let (Some(marker), Some(end)) = (marker, points.len().checked_sub(1).filter(|&e| e > 0))
        {
            items.push(Item::MarkerRef(MarkerRefItem {
                marker,
                at: points[end],
                axis: arrow_axis(points[end - 1], points[end]),
            }));
        }
        items
    }

    fn frame_items(
        &self,
        shift: &mut Shift,
        result: &EventModelingResult,
        index: usize,
    ) -> Result<Vec<Item>, LayoutError> {
        let frame = &self.input.frames[index];
        let r = i32::try_from(self.c.corner_radius).map_err(|_| LayoutError::Overflow)?;
        let mut items = vec![Item::RoundRect(RoundRectItem {
            shape: Shape::plain(frame_style(&frame.category)),
            rect: result.frames[index],
            r,
        })];
        let (name, data) = self.frame_texts(index);
        items.push(text_item(&frame.name, shift.rect(name), Align::Middle));
        if let Some(text) = &frame.data {
            items.push(text_item(text, shift.rect(data), Align::Start));
        }
        Ok(items)
    }
}
