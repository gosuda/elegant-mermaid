//! Treemap normalization, deterministic child ordering, and nested strip placement.
use super::super::layered::LayoutError;
use super::treemap_squarify::{Tile, normalize, squarify};
use super::treemap_text::{Label, LabelKind};
use super::{Skeleton, ZERO_RECT, constant, to_i32};
use crate::geom::{GeomError, Rect, Size, floor_div};
use crate::scene::{
    BoxRole, Direction, Dump, DumpOptions, DumpValue, Group, GroupRole, Item, Profile, RectItem,
    Scene, SceneBox, SceneLabel, Shape, ShapeStyle,
};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct TreemapNode {
    pub name: String,
    pub value_text: String,
    pub value: i64,
    pub parent: Option<usize>,
    pub index: usize,
}
#[derive(Debug, Clone, Default)]
pub struct Treemap {
    pub title: String,
    pub config: BTreeMap<String, DumpValue>,
    pub nodes: Vec<TreemapNode>,
}
#[derive(Clone)]
pub(super) struct Node {
    pub name: String,
    pub value_text: String,
    pub parent: usize,
    pub kids: Vec<usize>,
    pub order: Vec<usize>,
    pub norm: i64,
    pub series: usize,
    pub rect: Tile,
    pub name_label: Option<usize>,
    pub value_label: Option<usize>,
}
pub(super) struct Plan {
    pub profile: Profile,
    pub font_family: bool,
    pub title: String,
    pub nodes: Vec<Node>,
    pub labels: Vec<Label>,
    pub leaves: usize,
    pub width: i64,
    pub height: i64,
    pub constants: BTreeMap<String, i64>,
    pub capped: bool,
}
const KEYS: [&str; 34] = [
    "width",
    "height",
    "title_band",
    "section_header",
    "header_border",
    "section_padding_x",
    "section_padding_y",
    "inner_padding_x",
    "inner_padding_y",
    "rho_q30",
    "value_bits",
    "squarify_cap",
    "header_label_inset",
    "header_value_inset",
    "header_gap",
    "header_label_min",
    "header_label_size",
    "header_value_size",
    "dense_leaves",
    "value_scale_percent",
    "leaf_label_size",
    "leaf_value_size",
    "leaf_label_min",
    "leaf_value_min",
    "leaf_pad",
    "leaf_min_display",
    "leaf_spacing",
    "leaf_label_size_dense",
    "leaf_value_size_dense",
    "leaf_label_min_dense",
    "leaf_value_min_dense",
    "leaf_pad_dense",
    "leaf_min_display_dense",
    "leaf_spacing_dense",
];
impl Tile {
    pub(super) fn rect(self) -> Result<Rect, LayoutError> {
        Ok(Rect {
            x: to_i32(self.x0)?,
            y: to_i32(self.y0)?,
            w: to_i32(self.x1 - self.x0)?,
            h: to_i32(self.y1 - self.y0)?,
        })
    }
}
fn contained_span(mut lo: i64, mut hi: i64, parent_lo: i64, parent_hi: i64) -> (i64, i64) {
    if hi < lo {
        let mid = floor_div(lo + hi, 2);
        lo = mid;
        hi = mid;
    }
    (
        lo.clamp(parent_lo, parent_hi),
        hi.clamp(parent_lo, parent_hi),
    )
}
pub(super) fn box_id(i: usize) -> String {
    if i == 0 {
        "root".to_owned()
    } else {
        format!("n{}", i - 1)
    }
}
impl Plan {
    pub(super) fn c(&self, key: &str) -> i64 {
        self.constants[key]
    }
    pub(super) fn cell(&self) -> bool {
        self.profile == Profile::Cell
    }
    pub(super) fn role(&self, i: usize) -> BoxRole {
        if i == 0 || !self.nodes[i].kids.is_empty() {
            BoxRole::Group
        } else {
            BoxRole::Node
        }
    }
    fn constants(chart: &Treemap, profile: Profile) -> Result<BTreeMap<String, i64>, LayoutError> {
        let mut constants = BTreeMap::new();
        for key in KEYS {
            constants.insert(
                key.to_owned(),
                constant(profile, &format!("treemap.{key}"))?,
            );
        }
        for (key, value) in &chart.config {
            let DumpValue::Integer(n) = value else {
                continue;
            };
            let (target, factor, cell_px) = match key.as_str() {
                "nodeWidth" => ("width", 10, 8),
                "nodeHeight" => ("height", 10, 16),
                _ => continue,
            };
            constants.insert(
                target.to_owned(),
                side(
                    profile,
                    n.checked_mul(factor).ok_or(GeomError::Overflow)?,
                    cell_px,
                )?,
            );
        }
        if let Some(DumpValue::Integer(n)) = chart.config.get("padding") {
            constants.insert("inner_padding_x".to_owned(), side(profile, *n, 8)?);
            constants.insert("inner_padding_y".to_owned(), side(profile, *n, 16)?);
        }
        Ok(constants)
    }

    fn new(chart: &Treemap, profile: Profile) -> Result<Self, LayoutError> {
        let constants = Self::constants(chart, profile)?;
        let root = Node {
            name: String::new(),
            value_text: String::new(),
            parent: 0,
            kids: Vec::new(),
            order: Vec::new(),
            norm: 0,
            series: 0,
            rect: Tile::default(),
            name_label: None,
            value_label: None,
        };
        let mut nodes = vec![root];
        let mut raw = Vec::new();
        let mut leaves = Vec::new();
        for (i, n) in chart.nodes.iter().enumerate() {
            let parent = n.parent.map_or(0, |p| p + 1);
            if parent >= nodes.len() {
                return Err(GeomError::Domain);
            }
            nodes[parent].kids.push(i + 1);
            nodes.push(Node {
                name: n.name.clone(),
                value_text: n.value_text.clone(),
                parent,
                kids: Vec::new(),
                order: Vec::new(),
                norm: n.value,
                series: 0,
                rect: Tile::default(),
                name_label: None,
                value_label: None,
            });
        }
        for (i, n) in nodes.iter().enumerate().skip(1) {
            if n.kids.is_empty() {
                leaves.push(i);
                raw.push(n.norm);
            }
        }
        let bits = u32::try_from(constants["value_bits"]).map_err(|_| GeomError::Domain)?;
        for (i, v) in leaves.iter().zip(normalize(&raw, bits)?) {
            nodes[*i].norm = v;
        }
        for n in &mut nodes {
            if !n.kids.is_empty() {
                n.norm = 0;
            }
        }
        for i in (1..nodes.len()).rev() {
            let parent = nodes[i].parent;
            nodes[parent].norm = nodes[parent]
                .norm
                .checked_add(nodes[i].norm)
                .ok_or(GeomError::Overflow)?;
        }
        for i in 0..nodes.len() {
            let mut order = nodes[i].kids.clone();
            order.sort_by(|a, b| nodes[*b].norm.cmp(&nodes[*a].norm).then(a.cmp(b)));
            nodes[i].order = order;
        }
        let roots = nodes[0].kids.clone();
        for (series, i) in roots.into_iter().enumerate() {
            nodes[i].series = series;
        }
        for i in 1..nodes.len() {
            let parent = nodes[i].parent;
            if parent > 0 {
                nodes[i].series = nodes[parent].series;
            }
        }
        let band = if chart.title.is_empty() {
            0
        } else {
            constants["title_band"]
        };
        let width = constants["width"];
        let height = constants["height"];
        nodes[0].rect = Tile {
            x0: 0,
            y0: band,
            x1: width,
            y1: band + height,
        };
        let mut p = Self {
            profile,
            font_family: crate::scene::has_font_family(&chart.config),
            title: chart.title.clone(),
            nodes,
            labels: Vec::new(),
            leaves: leaves.len(),
            width,
            height: band + height,
            constants,
            capped: false,
        };
        p.label_specs();
        Ok(p)
    }
    fn label_specs(&mut self) {
        if !self.title.is_empty() {
            self.labels.push(Label::new(
                "title".to_owned(),
                "root".to_owned(),
                self.title.clone(),
                LabelKind::Title,
            ));
        }
        for i in 1..self.nodes.len() {
            let id = box_id(i);
            for (kind, suffix, text) in [
                (LabelKind::Name, ".name", self.nodes[i].name.clone()),
                (LabelKind::Value, ".value", self.nodes[i].value_text.clone()),
            ] {
                if text.is_empty() {
                    continue;
                }
                let k = self.labels.len();
                self.labels
                    .push(Label::new(format!("{id}{suffix}"), id.clone(), text, kind));
                match kind {
                    LabelKind::Name => self.nodes[i].name_label = Some(k),
                    LabelKind::Value => self.nodes[i].value_label = Some(k),
                    LabelKind::Title => {}
                }
            }
        }
    }
    fn tile_all(&mut self) -> Result<(), LayoutError> {
        let hx = floor_div(self.c("inner_padding_x"), 2);
        let hy = floor_div(self.c("inner_padding_y"), 2);
        for i in 0..self.nodes.len() {
            if self.nodes[i].order.is_empty() {
                continue;
            }
            let r = self.nodes[i].rect;
            let (x0, x1) = contained_span(
                r.x0 + self.c("section_padding_x") - hx,
                r.x1 - self.c("section_padding_x") + hx,
                r.x0,
                r.x1,
            );
            let (y0, y1) = contained_span(
                r.y0 + self.c("section_header") + self.c("section_padding_y") - hy,
                r.y1 - self.c("section_padding_y") + hy,
                r.y0,
                r.y1,
            );
            let values = self.nodes[i]
                .order
                .iter()
                .map(|k| self.nodes[*k].norm)
                .collect::<Vec<_>>();
            let rho = u64::try_from(self.c("rho_q30")).map_err(|_| GeomError::Domain)?;
            let fuel = usize::try_from(self.c("squarify_cap")).map_err(|_| GeomError::Domain)?;
            let (cells, capped) = squarify(&values, Tile { x0, y0, x1, y1 }, rho, fuel)?;
            self.capped |= capped;
            for (k, cell) in cells.into_iter().enumerate() {
                let id = self.nodes[i].order[k];
                let (x0, x1) = contained_span(cell.x0 + hx, cell.x1 - hx, cell.x0, cell.x1);
                let (y0, y1) = contained_span(cell.y0 + hy, cell.y1 - hy, cell.y0, cell.y1);
                self.nodes[id].rect = Tile { x0, y0, x1, y1 };
            }
        }
        Ok(())
    }
    fn boxes(&self) -> Vec<SceneBox> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(i, n)| SceneBox {
                id: box_id(i),
                role: self.role(i),
                rect: ZERO_RECT,
                parent: if i == 0 {
                    String::new()
                } else {
                    box_id(n.parent)
                },
                exclusive: false,
            })
            .collect()
    }
    fn dump_labels(&self) -> Vec<SceneLabel> {
        self.labels
            .iter()
            .map(|l| SceneLabel {
                id: l.id.clone(),
                owner: l.owner.clone(),
                text: l.text.clone(),
                rect: l.rect,
                lines: l.shown.iter().cloned().collect(),
            })
            .collect()
    }
    fn groups(&self) -> Result<Vec<Group>, LayoutError> {
        let mut groups = Vec::new();
        for role in [BoxRole::Group, BoxRole::Node] {
            for (i, n) in self
                .nodes
                .iter()
                .enumerate()
                .filter(|(i, _)| self.role(*i) == role)
            {
                let mut items = Vec::new();
                let rect = n.rect.rect()?;
                if i != 0 && rect.w > 0 && rect.h > 0 {
                    let style = if role == BoxRole::Group {
                        ShapeStyle::Group
                    } else if self.cell() {
                        ShapeStyle::Series
                    } else {
                        ShapeStyle::SeriesTint
                    };
                    let mut shape = Shape::plain(style);
                    if role == BoxRole::Node {
                        shape.series =
                            u8::try_from(n.series % 12).map_err(|_| GeomError::Domain)?;
                    }
                    items.push(Item::Rect(RectItem { shape, rect }));
                }
                let indexes = if i == 0 {
                    if self.title.is_empty() {
                        Vec::new()
                    } else {
                        vec![0]
                    }
                } else {
                    n.name_label.into_iter().chain(n.value_label).collect()
                };
                for k in indexes {
                    if let Some(item) = self.labels[k].item() {
                        items.push(item);
                    }
                }
                let group_role = if role == BoxRole::Group {
                    GroupRole::Group
                } else {
                    GroupRole::Node
                };
                groups.push(Group::new(group_role, box_id(i)).with_items(items));
            }
        }
        Ok(groups)
    }
}
fn side(profile: Profile, n: i64, cell_px: i64) -> Result<i64, LayoutError> {
    if profile == Profile::Cell {
        Ok(floor_div(n + cell_px - 1, cell_px))
    } else {
        n.checked_mul(64).ok_or(GeomError::Overflow)
    }
}
pub fn treemap_skeleton(chart: &Treemap) -> Result<Skeleton, LayoutError> {
    let p = Plan::new(chart, Profile::Vector)?;
    Ok(Skeleton {
        boxes: p.boxes(),
        labels: p.dump_labels(),
    })
}
pub fn layout_treemap(
    chart: &Treemap,
    options: &DumpOptions,
) -> Result<(Scene, bool), LayoutError> {
    let mut p = Plan::new(chart, options.profile)?;
    p.tile_all()?;
    p.place_all()?;
    let canvas = Size {
        w: to_i32(p.width)?,
        h: to_i32(p.height)?,
    };
    let mut options = options.clone();
    options.direction = Direction::Tb;
    let mut dump = Dump::new("treemap", options);
    dump.boxes = p.boxes();
    dump.labels = p.dump_labels();
    for (b, n) in dump.boxes.iter_mut().zip(&p.nodes) {
        b.rect = n.rect.rect()?;
    }
    let groups = p.groups()?;
    Ok((Scene::new(canvas, dump, groups), p.capped))
}

pub fn treemap_normalize(raw: &[i64]) -> Result<Vec<i64>, LayoutError> {
    let bits = u32::try_from(constant(Profile::Vector, "treemap.value_bits")?)
        .map_err(|_| GeomError::Domain)?;
    normalize(raw, bits)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn treemap_exhausted_insets_stay_inside_parents() -> Result<(), LayoutError> {
        for value in [0, 1] {
            let mut chart = Treemap::default();
            if value == 1 {
                chart
                    .config
                    .insert("nodeWidth".to_owned(), DumpValue::Integer(1));
                chart
                    .config
                    .insert("nodeHeight".to_owned(), DumpValue::Integer(1));
            }
            for (index, name) in ["A", "B", "C"].into_iter().enumerate() {
                chart.nodes.push(TreemapNode {
                    name: name.to_owned(),
                    value_text: String::new(),
                    value: if index == 2 { value } else { 0 },
                    parent: index.checked_sub(1),
                    index,
                });
            }
            for profile in [Profile::Vector, Profile::Cell] {
                let mut plan = Plan::new(&chart, profile)?;
                plan.tile_all()?;
                assert_eq!(plan.nodes.len(), 4);
                for n in plan.nodes.iter().skip(1) {
                    let parent = plan.nodes[n.parent].rect;
                    assert!(
                        parent.x0 <= n.rect.x0 && n.rect.x0 <= n.rect.x1 && n.rect.x1 <= parent.x1
                    );
                    assert!(
                        parent.y0 <= n.rect.y0 && n.rect.y0 <= n.rect.y1 && n.rect.y1 <= parent.y1
                    );
                }
            }
        }
        Ok(())
    }
}
