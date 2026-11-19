use super::{MARKER, Plan};
use crate::geom::{Point, Rect, floor_div};
use crate::scene::{
    Align, Dump, Group, GroupRole, Item, MarkerAxis, MarkerName, MarkerRefItem, PolylineItem,
    Profile, RectItem, RoundRectItem, Shape, ShapeStyle, TextItem, TextRole, TextStyle, Width,
};

const LABEL_SIZE_PX: i32 = 14;

impl Plan<'_> {
    pub(super) fn groups(&self, dump: &Dump) -> Vec<Group> {
        let mut groups = Vec::with_capacity(dump.routes.len() + self.count);
        for (route, input) in dump.routes.iter().zip(&self.input.routes) {
            let mut items = vec![Item::Polyline(PolylineItem {
                shape: Shape::plain(ShapeStyle::Edge),
                points: route.points.clone(),
                corner: 0,
            })];
            if input.marker_start == MARKER
                && let (Some(&at), Some(&from), Some(name)) = (
                    route.points.first(),
                    route.points.get(1),
                    MarkerName::new(MARKER),
                )
            {
                items.push(Item::MarkerRef(MarkerRefItem {
                    marker: name,
                    at,
                    axis: axis(from, at),
                }));
            }
            groups.push(Group::new(GroupRole::Edge, route.id.clone()).with_items(items));
        }
        for (i, scene_box) in dump.boxes.iter().take(self.count).enumerate() {
            let mut items = self.outline(i, scene_box.rect);
            items.push(Item::Text(self.text(scene_box.rect, i)));
            groups.push(Group::new(GroupRole::Node, scene_box.id.clone()).with_items(items));
        }
        groups
    }

    /// The head and the causes are outlined; bare sub-causes are text only.
    fn outline(&self, index: usize, rect: Rect) -> Vec<Item> {
        let mut shape = Shape::plain(ShapeStyle::Node);
        match self.depth[index] {
            0 => shape.width = Width::Emphasis,
            1 => {}
            _ => return Vec::new(),
        }
        if self.depth[index] == 0 && self.input.profile == Profile::Vector {
            return vec![Item::RoundRect(RoundRectItem {
                shape,
                rect,
                r: self.c.corner,
            })];
        }
        vec![Item::Rect(RectItem { shape, rect })]
    }

    fn text(&self, rect: Rect, index: usize) -> TextItem {
        let runs = self.runs.get(index).cloned().unwrap_or_default();
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
