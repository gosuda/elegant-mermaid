//! The display list of the venn plan: one group per box, with the set circle first and
//! the label texts after it.

use crate::measure::Role;
use crate::scene::{
    Align, EllipseItem, Group, GroupRole, Item, Shape, ShapeStyle, TextItem, TextRole, TextStyle,
};

use super::super::{LayoutError, to_i32};
use super::{Plan, VennBox, role_of};

const SERIES_COUNT: usize = 12;

fn text_role(role: Role) -> TextRole {
    match role {
        Role::Title => TextRole::Title,
        Role::Body => TextRole::Body,
        Role::Label => TextRole::Label,
    }
}

impl Plan<'_> {
    pub(super) fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        self.boxes
            .iter()
            .map(|b| Ok(Group::new(GroupRole::Node, b.id.clone()).with_items(self.box_items(b)?)))
            .collect()
    }

    fn box_items(&self, b: &VennBox) -> Result<Vec<Item>, LayoutError> {
        let mut out = Vec::new();
        if let Some(set) = b.set {
            out.push(self.ellipse(set)?);
        }
        out.extend(b.items.iter().map(|id| self.text_item(*id)));
        Ok(out)
    }

    fn ellipse(&self, set: usize) -> Result<Item, LayoutError> {
        let c = self.circles[set];
        let series = u8::try_from(set % SERIES_COUNT).unwrap_or(0);
        Ok(Item::Ellipse(EllipseItem {
            shape: Shape::plain(ShapeStyle::SeriesTint).with_series(series),
            cx: to_i32(c.x)?,
            cy: to_i32(c.y)?,
            rx: to_i32(c.r)?,
            ry: to_i32(c.r)?,
        }))
    }

    fn text_item(&self, id: usize) -> Item {
        let it = &self.items[id];
        let role = role_of(it.title);
        Item::Text(TextItem {
            rect: it.rect,
            role: text_role(role),
            size: role.size_px(),
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: it.text_box.lines.iter().map(|l| l.runs.clone()).collect(),
        })
    }
}
