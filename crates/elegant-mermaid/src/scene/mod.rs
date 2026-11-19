//! The scene: its four parts, the closed primitive set, and the closed role lists of
//! `spec/scene.md`.
//!
//! A scene holds `profile`, `canvas`, the dump part, and `items`. The dump part is the
//! relation section that `spec/layout-dump.md` fixes; validators, metrics, and the Lean
//! reference read only the dump part, and back ends read only `profile`, `canvas`, and
//! `items`.
//!
//! Style names are the data rows of `spec/data/styles.json`. This module names the closed
//! lists and never resolves a colour, a stroke width, or a glyph: paint is a back end's
//! decision, and the theme supplies the colour.

use std::collections::BTreeMap;

#[cfg(test)]
use crate::r#gen;
use crate::geom::{Point, Rect, Size};

pub(crate) mod dump;
pub mod metrics;
mod projection;
mod validate;
pub(crate) use projection::project_cell_attachments;

pub use dump::{Stage, push_int, push_layout, push_model};
pub use validate::{CLAUSES, Clause, Malformed, check, validate, well_formed};

/// The layout profile of a scene, which selects the unit of every coordinate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Profile {
    /// One unit is 1/64 px, and text width comes from the font advance table.
    #[default]
    Vector,
    /// One unit is one character cell, and text width comes from the Unicode width table.
    Cell,
}

impl Profile {
    /// The profile name of the dump, `vector` or `cell`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Profile::Vector => "vector",
            Profile::Cell => "cell",
        }
    }
}

/// The resolved layout direction of the dump.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Direction {
    /// Top to bottom, which a `TD` header also names.
    #[default]
    Tb,
    /// Bottom to top.
    Bt,
    /// Left to right.
    Lr,
    /// Right to left.
    Rl,
}

impl Direction {
    /// The direction name of the dump.
    pub const fn as_str(self) -> &'static str {
        match self {
            Direction::Tb => "TB",
            Direction::Bt => "BT",
            Direction::Lr => "LR",
            Direction::Rl => "RL",
        }
    }

    /// The direction a header token names, or `None` when it names none. `TD` resolves to
    /// [`Direction::Tb`], and ASCII case is folded.
    pub fn from_token(token: &str) -> Option<Direction> {
        let token = token.trim_matches(|c: char| c.is_ascii_whitespace());
        [
            ("TB", Direction::Tb),
            ("TD", Direction::Tb),
            ("BT", Direction::Bt),
            ("LR", Direction::Lr),
            ("RL", Direction::Rl),
        ]
        .into_iter()
        .find(|(name, _)| token.eq_ignore_ascii_case(name))
        .map(|(_, direction)| direction)
    }
}

/// The model size limits that the dump's `options` object carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The largest accepted node count.
    pub max_nodes: u32,
    /// The largest accepted edge count.
    pub max_edges: u32,
    /// The largest accepted source size in bytes.
    pub max_text_bytes: u32,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_nodes: 2000,
            max_edges: 5000,
            max_text_bytes: 1_048_576,
        }
    }
}

/// The value of one honoured config key that affects layout, as the dump writes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DumpValue {
    /// A boolean.
    Bool(bool),
    /// An integer, written in minimal decimal.
    Integer(i64),
    /// A string.
    String(String),
}

/// The resolved options of the dump's `options` object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DumpOptions {
    /// The layout profile.
    pub profile: Profile,
    /// The thoroughness, 1 to 5.
    pub thoroughness: u8,
    /// The packing and wrapping target in columns, or 0 for the natural width.
    pub max_width: u32,
    /// The resolved layout direction.
    pub direction: Direction,
    /// The model size limits.
    pub limits: Limits,
    /// Every honoured config key that affects layout, keyed by name, so the dump writes
    /// them in ascending byte order.
    pub config: BTreeMap<String, DumpValue>,
}

impl Default for DumpOptions {
    fn default() -> Self {
        DumpOptions {
            profile: Profile::default(),
            thoroughness: 3,
            max_width: 0,
            direction: Direction::default(),
            limits: Limits::default(),
            config: BTreeMap::new(),
        }
    }
}

/// The role of a dump box.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoxRole {
    /// A node.
    Node,
    /// A frame around other boxes.
    Group,
}

impl BoxRole {
    /// The role name of the dump, `node` or `group`.
    pub const fn as_str(self) -> &'static str {
        match self {
            BoxRole::Node => "node",
            BoxRole::Group => "group",
        }
    }

    /// The role a dump role name denotes, or `None`.
    pub fn from_name(name: &str) -> Option<BoxRole> {
        match name {
            "node" => Some(BoxRole::Node),
            "group" => Some(BoxRole::Group),
            _ => None,
        }
    }
}

/// One box of the dump part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SceneBox {
    /// The box id, unique among boxes.
    pub id: String,
    /// The box role.
    pub role: BoxRole,
    /// The box rectangle in profile units; the model stage leaves it unwritten.
    pub rect: Rect,
    /// The id of the parent box, or the empty string for a box with no parent.
    pub parent: String,
    /// Whether the box is exclusive, which means no exclusive sibling, unrelated route,
    /// or unrelated label may reach its interior.
    pub exclusive: bool,
}

/// One route of the dump part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SceneRoute {
    /// The route id, unique among routes.
    pub id: String,
    /// The id of the box the route starts at.
    pub from: String,
    /// The id of the box the route ends at.
    pub to: String,
    /// Whether every segment of the route is horizontal or vertical.
    pub orthogonal: bool,
    /// The route points in profile units; the model stage leaves them unwritten.
    pub points: Vec<Point>,
    pub marker_start: String,
    pub marker_end: String,
    pub stroke: String,
}

/// One label of the dump part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SceneLabel {
    /// The label id, unique among labels.
    pub id: String,
    /// The id of the route or box the label belongs to.
    pub owner: String,
    /// The unwrapped label text that the model stage writes.
    pub text: String,
    /// The label rectangle in profile units; the model stage leaves it unwritten.
    pub rect: Rect,
    /// The wrapped lines that measurement fills; empty before measurement.
    pub lines: Vec<String>,
}

/// The dump part of a scene: the relation section of `spec/layout-dump.md`.
///
/// The model stage fixes `kind`, the options, the box ids and roles, the containment
/// tree, the route endpoints, and the label text. Measurement fills [`SceneLabel::lines`].
/// Layout fills the canvas, every rectangle, and every route point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dump {
    /// The kind id, for example `flowchart`.
    pub kind: &'static str,
    /// The resolved options.
    pub options: DumpOptions,
    /// The boxes, in declaration order.
    pub boxes: Vec<SceneBox>,
    /// The routes, in declaration order.
    pub routes: Vec<SceneRoute>,
    /// The labels, in declaration order.
    pub labels: Vec<SceneLabel>,
}

impl Dump {
    /// An empty dump of one kind with resolved options.
    pub fn new(kind: &'static str, options: DumpOptions) -> Dump {
        Dump {
            kind,
            options,
            boxes: Vec::new(),
            routes: Vec::new(),
            labels: Vec::new(),
        }
    }

    /// The canonical layout dump of `spec/layout-dump.md`, given the canvas that layout
    /// produced.
    pub fn dump_layout(&self, canvas: Size) -> String {
        let mut out = String::new();
        dump::push_layout(&mut out, self, canvas);
        out
    }

    /// The model-stage dump of `spec/model-dump.md`: no canvas, no coordinates, and an
    /// empty `lines` array on every label.
    pub fn dump_model(&self, directions: &[(&str, Direction)]) -> String {
        let mut out = String::new();
        dump::push_model(&mut out, self, directions);
        out
    }
}

/// A scene: the canvas, the relation section, and the display list that back ends draw.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scene {
    canvas: Size,
    dump: Dump,
    items: Vec<Group>,
}

impl Scene {
    /// A scene from its canvas, its dump part, and its groups.
    pub fn new(canvas: Size, dump: Dump, items: Vec<Group>) -> Scene {
        Scene {
            canvas,
            dump,
            items,
        }
    }

    /// The canvas size in profile units.
    pub fn canvas(&self) -> Size {
        self.canvas
    }

    /// The layout profile, which is the profile of the dump options.
    pub fn profile(&self) -> Profile {
        self.dump.options.profile
    }

    /// The boxes of the dump part.
    pub fn boxes(&self) -> &[SceneBox] {
        &self.dump.boxes
    }

    /// The routes of the dump part.
    pub fn routes(&self) -> &[SceneRoute] {
        &self.dump.routes
    }

    /// The labels of the dump part.
    pub fn labels(&self) -> &[SceneLabel] {
        &self.dump.labels
    }

    /// The dump part.
    pub fn dump_part(&self) -> &Dump {
        &self.dump
    }

    /// The groups, in draw order.
    pub fn items(&self) -> &[Group] {
        &self.items
    }

    pub(crate) fn items_mut(&mut self) -> &mut [Group] {
        &mut self.items
    }

    /// The canonical layout dump of `spec/layout-dump.md`.
    pub fn dump(&self) -> String {
        self.dump.dump_layout(self.canvas)
    }

    /// The first clause of `spec/layout-dump.md` that the scene violates, or `None`.
    pub fn validate(&self) -> Result<Option<Clause>, crate::geom::GeomError> {
        validate(self.canvas, &self.dump)
    }

    /// True exactly when no clause fails.
    pub fn check(&self) -> Result<bool, crate::geom::GeomError> {
        check(self.canvas, &self.dump)
    }
}

mod groups;
mod items;

pub use groups::{Group, GroupOrder, GroupRole, check_groups};
pub use items::{
    Align, EllipseItem, Item, ItemClass, Line, MarkerAxis, MarkerName, MarkerRefItem, PathCommand,
    PathItem, PolygonItem, PolylineItem, RectItem, RoundRectItem, Run, Shape, ShapeStyle,
    StyleClass, SymbolName, SymbolRefItem, TextItem, TextRole, TextStyle, Width,
};

#[cfg(test)]
#[path = "scene_contract_tests.rs"]
mod tests;
