//! Profile-aware treemap header and leaf labels, including grapheme-safe ellipses.
use super::super::layered::LayoutError;
use super::treemap::Plan;
use super::{Area, ZERO_RECT, to_i32};
use crate::geom::{Rect, floor_div};
use crate::measure::{Metric, Role, segment};
use crate::scene::{Align, Item, Run, TextItem, TextRole, TextStyle};
#[derive(Clone, Copy)]
pub(super) enum LabelKind {
    Title,
    Name,
    Value,
}
pub(super) struct Label {
    pub id: String,
    pub owner: String,
    pub text: String,
    pub shown: Option<String>,
    pub rect: Rect,
    pub size: i32,
    pub align: Align,
    pub role: TextRole,
    pub style: TextStyle,
    pub italic: bool,
}
impl Label {
    pub(super) fn new(id: String, owner: String, text: String, kind: LabelKind) -> Self {
        let (role, style) = match kind {
            LabelKind::Title => (TextRole::Title, TextStyle::Text),
            LabelKind::Name => (TextRole::Label, TextStyle::Text),
            LabelKind::Value => (TextRole::Body, TextStyle::TextMuted),
        };
        Self {
            id,
            owner,
            text,
            shown: None,
            rect: ZERO_RECT,
            size: 0,
            align: Align::Middle,
            role,
            style,
            italic: false,
        }
    }
    pub(super) fn item(&self) -> Option<Item> {
        self.shown.as_ref().map(|s| {
            Item::Text(TextItem {
                rect: self.rect,
                role: self.role,
                size: self.size,
                align: self.align,
                style: self.style,
                series: 0,
                lines: vec![vec![Run {
                    text: s.clone(),
                    bold: false,
                    italic: self.italic,
                }]],
            })
        })
    }
}
#[derive(Clone, Copy)]
struct Style {
    role: Role,
    size: i64,
}
struct Bounds {
    r: Area,
    w: i64,
    h: i64,
    pad: i64,
    spacing: i64,
    label_size: i64,
    label_min: i64,
    value_size: i64,
    value_min: i64,
}
impl Plan {
    fn line_height(&self, role: Role) -> i64 {
        if self.cell() {
            1
        } else {
            i64::from(role.line_height_px()) * 64
        }
    }
    fn width_of(&self, text: &str, s: Style) -> Result<i64, LayoutError> {
        let metric = if self.cell() {
            Metric::Cell
        } else {
            Metric::Vector {
                size_px: to_i32(s.size)?,
                weight: s.role.weight(),
                font_family: self.font_family,
            }
        };
        Ok(i64::from(metric.width(text)?))
    }
    fn fit(&self, text: &str, avail: i64, s: Style) -> Result<Option<(String, i64)>, LayoutError> {
        if text.is_empty() {
            return Ok(None);
        }
        let width = self.width_of(text, s)?;
        if width <= avail {
            return Ok(Some((text.to_owned(), width)));
        }
        if self.width_of("...", s)? > avail {
            return Ok(None);
        }
        let clusters = segment(text);
        let mut lo = 0;
        let mut hi = clusters.len().saturating_sub(1);
        let prefix = |k: usize| {
            let mut out = String::new();
            for c in &clusters[..k] {
                out.push_str(c.text);
            }
            out.push_str("...");
            out
        };
        while lo < hi {
            let mid = (lo + hi).div_ceil(2);
            if self.width_of(&prefix(mid), s)? <= avail {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        let shown = prefix(lo);
        let width = self.width_of(&shown, s)?;
        Ok(Some((shown, width)))
    }
    fn put(&mut self, k: usize, shown: String, r: Area, s: Style) -> Result<(), LayoutError> {
        let rect = r.to_rect()?;
        let l = &mut self.labels[k];
        l.rect = rect;
        l.shown = Some(shown);
        l.size = to_i32(s.size)?;
        Ok(())
    }
    pub(super) fn place_all(&mut self) -> Result<(), LayoutError> {
        if !self.title.is_empty() {
            self.place_title()?;
        }
        for i in 1..self.nodes.len() {
            if self.nodes[i].kids.is_empty() {
                self.place_leaf(i)?;
            } else {
                self.place_header(i)?;
            }
        }
        Ok(())
    }
    fn place_title(&mut self) -> Result<(), LayoutError> {
        let s = Style {
            role: Role::Title,
            size: i64::from(Role::Title.size_px()),
        };
        let Some((shown, w)) = self.fit(&self.labels[0].text, self.width, s)? else {
            return Ok(());
        };
        let lh = self.line_height(s.role);
        self.put(
            0,
            shown,
            Area::new(
                floor_div(self.width - w, 2),
                floor_div(self.c("title_band") - lh, 2),
                w,
                lh,
            ),
            s,
        )
    }
    fn place_header(&mut self, i: usize) -> Result<(), LayoutError> {
        let n = &self.nodes[i];
        let r = n.rect.rect()?;
        let r = Area::new(
            i64::from(r.x),
            i64::from(r.y),
            i64::from(r.w),
            i64::from(r.h),
        );
        let name = Style {
            role: Role::Label,
            size: self.c("header_label_size") / 64,
        };
        let value = Style {
            role: Role::Body,
            size: self.c("header_value_size") / 64,
        };
        let lh = self.line_height(Role::Label);
        let top = self.c("header_border")
            + floor_div(self.c("section_header") - self.c("header_border") - lh, 2);
        if r.h <= top + lh {
            return Ok(());
        }
        let value_w = match n.value_label {
            Some(k) => self.width_of(&self.labels[k].text, value)?,
            None => 0,
        };
        let reserve = self.c("header_value_inset") + value_w + self.c("header_gap");
        let inset = self.c("header_label_inset");
        let show_value = n.value_label.is_some()
            && value_w + self.c("header_value_inset") + inset <= r.w
            && (n.name_label.is_none() || r.w - inset - reserve >= self.c("header_label_min"));
        let avail = if show_value {
            r.w - inset - reserve
        } else {
            r.w - 2 * inset
        };
        let name_k = n.name_label;
        let value_k = n.value_label;
        if let Some(k) = name_k
            && let Some((shown, w)) = self.fit(&self.labels[k].text, avail, name)?
        {
            self.labels[k].align = Align::Start;
            self.put(k, shown, Area::new(r.x + inset, r.y + top, w, lh), name)?;
        }
        if let Some(k) = value_k.filter(|_| show_value) {
            self.labels[k].align = Align::End;
            self.labels[k].italic = true;
            self.put(
                k,
                self.labels[k].text.clone(),
                Area::new(
                    r.x + r.w - self.c("header_value_inset") - value_w,
                    r.y + top,
                    value_w,
                    lh,
                ),
                value,
            )?;
        }
        Ok(())
    }
    fn bounds(&self, i: usize) -> Result<Option<Bounds>, LayoutError> {
        let suffix = if i64::try_from(self.leaves).unwrap_or(i64::MAX) > self.c("dense_leaves") {
            "_dense"
        } else {
            ""
        };
        let leaf = |key: &str| self.c(&format!("leaf_{key}{suffix}"));
        let pad = leaf("pad");
        let r = self.nodes[i].rect.rect()?;
        let r = Area::new(
            i64::from(r.x),
            i64::from(r.y),
            i64::from(r.w),
            i64::from(r.h),
        );
        let w = r.w - 2 * pad;
        let h = r.h - 2 * pad;
        if w < leaf("min_display") || h < leaf("min_display") {
            return Ok(None);
        }
        Ok(Some(Bounds {
            r,
            w,
            h,
            pad,
            spacing: leaf("spacing"),
            label_size: leaf("label_size"),
            label_min: leaf("label_min"),
            value_size: leaf("value_size"),
            value_min: leaf("value_min"),
        }))
    }
    fn leaf_size(&self, text: &str, b: &Bounds) -> Result<i64, LayoutError> {
        if self.cell() {
            return Ok(0);
        }
        let mut size = b.label_size / 64;
        let smallest = b.label_min / 64;
        while size > smallest {
            if self.width_of(
                text,
                Style {
                    role: Role::Label,
                    size,
                },
            )? <= b.w
            {
                break;
            }
            size -= 1;
        }
        while size > smallest && size * 64 > b.h {
            size -= 1;
        }
        Ok(size)
    }
    fn place_leaf(&mut self, i: usize) -> Result<(), LayoutError> {
        let Some(k) = self.nodes[i].name_label else {
            return Ok(());
        };
        let Some(b) = self.bounds(i)? else {
            return Ok(());
        };
        let size = self.leaf_size(&self.labels[k].text, &b)?;
        let name = Style {
            role: Role::Label,
            size,
        };
        let Some((shown, w)) = self.fit(&self.labels[k].text, b.w, name)? else {
            return Ok(());
        };
        let lh = self.line_height(Role::Label);
        if !self.cell() && lh > b.r.h {
            return Ok(());
        }
        let value_size = if self.cell() {
            0
        } else {
            let scaled = floor_div(2 * size * self.c("value_scale_percent") + 100, 200);
            (b.value_min / 64).max((b.value_size / 64).min(scaled))
        };
        let value = Style {
            role: Role::Body,
            size: value_size,
        };
        let pair = 2 * lh + b.spacing;
        let room = pair <= if self.cell() { b.h } else { b.r.h };
        let value_k = self.nodes[i].value_label;
        let value_w = match value_k.filter(|_| room) {
            Some(v) => self.width_of(&self.labels[v].text, value)?,
            None => 0,
        };
        let show_value = room && value_k.is_some() && value_w <= b.w;
        let rows = if show_value { pair } else { lh };
        let top = if self.cell() {
            b.r.y + b.pad + floor_div(b.h - rows, 2)
        } else {
            b.r.y + floor_div(b.r.h - rows, 2)
        };
        self.put(
            k,
            shown,
            Area::new(b.r.x + b.pad + floor_div(b.w - w, 2), top, w, lh),
            name,
        )?;
        if let Some(v) = value_k.filter(|_| show_value) {
            self.put(
                v,
                self.labels[v].text.clone(),
                Area::new(
                    b.r.x + b.pad + floor_div(b.w - value_w, 2),
                    top + lh + b.spacing,
                    value_w,
                    lh,
                ),
                value,
            )?;
        }
        Ok(())
    }
}
