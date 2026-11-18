//! The display list of the architecture kind under both profiles.

use crate::geom::{Point, Rect};
use crate::layout::grid::architecture::ArchLayout;
use crate::layout::input::Route as InputRoute;
use crate::scene::{
    Align, EllipseItem, Group as SceneGroup, GroupRole, Item, MarkerAxis, MarkerName,
    MarkerRefItem, PolylineItem, Profile, RectItem, RoundRectItem, Shape, ShapeStyle, SymbolName,
    SymbolRefItem, TextItem, TextRole, TextStyle,
};

use super::plan::{Measured, Planner};

fn axis(from: Point, to: Point) -> MarkerAxis {
    let dx = i64::from(to.x) - i64::from(from.x);
    let dy = i64::from(to.y) - i64::from(from.y);
    match (dx.abs() >= dy.abs(), dx < 0, dy < 0) {
        (true, true, _) => MarkerAxis::MinusX,
        (true, false, _) => MarkerAxis::PlusX,
        (false, _, true) => MarkerAxis::MinusY,
        (false, _, false) => MarkerAxis::PlusY,
    }
}

fn arrowhead(name: &str, at: Point, axis: MarkerAxis) -> Option<Item> {
    if name.is_empty() {
        return None;
    }
    let marker = MarkerName::new("point")?;
    Some(Item::MarkerRef(MarkerRefItem { marker, at, axis }))
}

fn text(rect: Rect, measured: &Measured, align: Align) -> Item {
    Item::Text(TextItem {
        rect,
        role: TextRole::Label,
        size: 14,
        align,
        style: TextStyle::Text,
        series: 0,
        lines: measured.runs.clone(),
    })
}

impl Planner<'_> {
    pub(super) fn groups(&self, result: &ArchLayout) -> Vec<SceneGroup> {
        let mut groups = Vec::new();
        for g in 0..self.group_count() {
            groups.push(SceneGroup {
                role: GroupRole::Group,
                owner: self.group_id(g).to_owned(),
                items: self.frame_items(result, g),
            });
        }
        for (i, route) in self.input.routes.iter().enumerate() {
            groups.push(SceneGroup {
                role: GroupRole::Edge,
                owner: route.id.clone(),
                items: self.edge_items(result, i, route),
            });
        }
        for n in 0..self.node_count() {
            groups.push(SceneGroup {
                role: GroupRole::Node,
                owner: self.node_id(n).to_owned(),
                items: self.node_items(result, n),
            });
        }
        groups
    }

    fn frame_items(&self, result: &ArchLayout, group: usize) -> Vec<Item> {
        let mut items = vec![Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Group),
            rect: result.frames[group],
        })];
        if !self.titles[group].is_empty() {
            items.push(text(
                result.titles[group],
                &self.titles[group],
                Align::Start,
            ));
        }
        items
    }

    fn edge_items(&self, result: &ArchLayout, index: usize, route: &InputRoute) -> Vec<Item> {
        let mut items = Vec::new();
        let points = &result.routes[index];
        if points.len() >= 2 {
            let end = points.len() - 1;
            items.push(self.polyline(points));
            items.extend(arrowhead(
                &route.marker_start,
                points[0],
                axis(points[1], points[0]),
            ));
            items.extend(arrowhead(
                &route.marker_end,
                points[end],
                axis(points[end - 1], points[end]),
            ));
        }
        if !self.edge_labels[index].is_empty() {
            items.push(text(
                result.edge_labels[index],
                &self.edge_labels[index],
                Align::Middle,
            ));
        }
        items
    }

    fn polyline(&self, points: &[Point]) -> Item {
        Item::Polyline(PolylineItem {
            shape: Shape::plain(ShapeStyle::Edge),
            points: points.to_vec(),
            corner: self.c.corner,
        })
    }

    fn node_items(&self, result: &ArchLayout, node: usize) -> Vec<Item> {
        let (boxed, icon) = (result.boxes[node], result.icons[node]);
        if self.spec(node).kind == "junction" {
            return self.junction_items(boxed);
        }
        let mut items = vec![self.outline(icon)];
        let inner = &self.icon_texts[node];
        if !inner.is_empty() {
            items.push(self.icon_text_item(icon, inner));
        }
        if !self.labels[node].is_empty() {
            items.push(text(result.labels[node], &self.labels[node], Align::Middle));
        }
        items
    }

    fn outline(&self, icon: Rect) -> Item {
        let shape = Shape::plain(ShapeStyle::Node);
        if self.profile == Profile::Cell {
            return Item::Rect(RectItem { shape, rect: icon });
        }
        Item::RoundRect(RoundRectItem {
            shape,
            rect: icon,
            r: self.c.corner.min(icon.w / 2).min(icon.h / 2),
        })
    }

    fn junction_items(&self, boxed: Rect) -> Vec<Item> {
        if self.profile == Profile::Cell {
            return SymbolName::new("disc")
                .map(|symbol| {
                    Item::SymbolRef(SymbolRefItem {
                        symbol,
                        at: Point {
                            x: boxed.x,
                            y: boxed.y,
                        },
                        style: ShapeStyle::Ink,
                    })
                })
                .into_iter()
                .collect();
        }
        vec![Item::Ellipse(EllipseItem {
            shape: Shape::plain(ShapeStyle::Ink),
            cx: boxed.x + boxed.w / 2,
            cy: boxed.y + boxed.h / 2,
            rx: boxed.w / 2,
            ry: boxed.h / 2,
        })]
    }

    fn icon_text_item(&self, icon: Rect, measured: &Measured) -> Item {
        let params = self.c.params;
        let border = self.c.border;
        let room = ((icon.h - 2 * border) / params.line_height).max(1);
        let kept = usize::try_from(room).unwrap_or(1).min(measured.texts.len());
        let shown = measured.head(kept);
        let height = i32::try_from(kept).unwrap_or(0) * params.line_height;
        let rect = Rect {
            x: icon.x + params.inset,
            y: icon.y + border + ((icon.h - 2 * border - height) >> 1),
            w: (icon.w - 2 * params.inset).max(1),
            h: height,
        };
        text(rect, &shown, Align::Middle)
    }
}
