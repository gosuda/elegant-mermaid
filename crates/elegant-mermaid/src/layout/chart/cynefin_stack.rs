//! The domain stack: a domain name over item badges, centred on one column.

use crate::geom::floor_div;

use super::Area;
use super::cynefin_consts::Consts;
use super::cynefin_text::{TextBox, bottom, right};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CurvePoint {
    pub x: i64,
    pub y: i64,
}

#[derive(Debug, Clone)]
pub(crate) struct DomainPlan {
    pub name: String,
    pub title: TextBox,
    pub items: Vec<TextBox>,
    pub cx: i64,
    pub name_at: Area,
    pub badges: Vec<Area>,
    pub texts: Vec<Area>,
    pub bounds: Area,
    pub anchor_y: i64,
}

impl DomainPlan {
    pub(crate) fn new(name: String, title: TextBox, items: Vec<TextBox>) -> DomainPlan {
        DomainPlan {
            name,
            title,
            items,
            cx: 0,
            name_at: Area::default(),
            badges: Vec::new(),
            texts: Vec::new(),
            bounds: Area::default(),
            anchor_y: 0,
        }
    }

    fn widest(&self, c: &Consts) -> i64 {
        self.items
            .iter()
            .map(|item| item.w + 2 * c.item_pad_x)
            .fold(self.title.w, i64::max)
    }

    pub(crate) fn height(&self, c: &Consts) -> i64 {
        let mut total = self.title.h;
        for (i, item) in self.items.iter().enumerate() {
            total += if i == 0 { c.name_gap } else { c.item_gap };
            total += item.h + 2 * c.item_pad_y;
        }
        total
    }

    pub(crate) fn span(&self, c: &Consts) -> (i64, i64) {
        let widest = self.widest(c);
        let lo = floor_div(widest, 2) + c.box_pad;
        (lo, widest - floor_div(widest, 2) + c.box_pad)
    }

    pub(crate) fn place(&mut self, c: &Consts, cx: i64, top: i64) {
        self.cx = cx;
        self.name_at = Area::new(
            cx - floor_div(self.title.w, 2),
            top,
            self.title.w,
            self.title.h,
        );
        self.anchor_y = top + floor_div(self.title.h, 2);
        self.badges.clear();
        self.texts.clear();
        let mut y = top + self.title.h + c.name_gap;
        for item in &self.items {
            let (badge_w, badge_h) = (item.w + 2 * c.item_pad_x, item.h + 2 * c.item_pad_y);
            self.badges
                .push(Area::new(cx - floor_div(badge_w, 2), y, badge_w, badge_h));
            self.texts.push(Area::new(
                cx - floor_div(item.w, 2),
                y + c.item_pad_y,
                item.w,
                item.h,
            ));
            y += badge_h + c.item_gap;
        }
        self.bounds = self.compute_bounds(c);
    }

    fn compute_bounds(&self, c: &Consts) -> Area {
        let name = self.name_at;
        let (mut x0, mut y0, mut x1, mut y1) = (name.x, name.y, right(name), bottom(name));
        for badge in &self.badges {
            x0 = x0.min(badge.x);
            y0 = y0.min(badge.y);
            x1 = x1.max(right(*badge));
            y1 = y1.max(bottom(*badge));
        }
        Area::new(
            x0 - c.box_pad,
            y0 - c.box_pad,
            x1 - x0 + 2 * c.box_pad,
            y1 - y0 + 2 * c.box_pad,
        )
    }
}
