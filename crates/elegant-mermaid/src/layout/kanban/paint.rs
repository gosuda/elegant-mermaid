use super::Plan;
use crate::geom::Rect;
use crate::layout::grid::KanbanLayout;
use crate::scene::{
    Align, Group, GroupRole, Item, RoundRectItem, Run, Shape, ShapeStyle, TextItem, TextRole,
    TextStyle,
};

const LABEL_SIZE_PX: i32 = 14;

impl Plan<'_> {
    pub(super) fn groups(&self, placed: &KanbanLayout) -> Vec<Group> {
        let mut groups = Vec::with_capacity(self.sections.len() + self.cards.len());
        for (k, &index) in self.sections.iter().enumerate() {
            let (Some(rect), Some(label), Some(title), Some(item)) = (
                placed.sections.get(k),
                placed.labels.get(k),
                self.titles.get(k),
                self.input.boxes.get(index),
            ) else {
                continue;
            };
            let mut items = vec![self.frame(ShapeStyle::Group, *rect)];
            if !title.is_empty() {
                items.push(self.text(*label, Align::Middle, title));
            }
            groups.push(Group::new(GroupRole::Group, item.id.clone()).with_items(items));
        }
        for (k, &index) in self.cards.iter().enumerate() {
            let (Some(rect), Some(lines), Some(item)) = (
                placed.cards.get(k),
                self.texts.get(k),
                self.input.boxes.get(index),
            ) else {
                continue;
            };
            let height = i32::try_from(lines.len())
                .unwrap_or(i32::MAX)
                .saturating_mul(self.c.line_height);
            let text = Rect {
                x: rect.x + self.c.card_pad_x,
                y: rect.y + self.c.border + self.c.card_pad_y,
                w: rect.w - 2 * self.c.card_pad_x,
                h: height,
            };
            let items = vec![
                self.frame(ShapeStyle::Node, *rect),
                self.text(text, Align::Start, lines),
            ];
            groups.push(Group::new(GroupRole::Node, item.id.clone()).with_items(items));
        }
        groups
    }

    fn frame(&self, style: ShapeStyle, rect: Rect) -> Item {
        Item::RoundRect(RoundRectItem {
            shape: Shape::plain(style),
            rect,
            r: self.c.corner,
        })
    }

    fn text(&self, rect: Rect, align: Align, lines: &[Vec<Run>]) -> Item {
        Item::Text(TextItem {
            rect,
            role: TextRole::Label,
            size: LABEL_SIZE_PX,
            align,
            style: TextStyle::Text,
            series: 0,
            lines: lines.to_vec(),
        })
    }
}
