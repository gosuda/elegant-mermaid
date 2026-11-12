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

use crate::r#gen;
use crate::geom::{Point, Rect, Size};

mod dump;
mod validate;

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
    pub fn dump_model(&self) -> String {
        let mut out = String::new();
        dump::push_model(&mut out, self);
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

/// One style of the closed shape style list of `spec/scene.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeStyle {
    /// A node surface with a border stroke.
    Node,
    /// A frame around other boxes.
    Group,
    /// A background band without a stroke.
    Band,
    /// A note surface with an accent stroke.
    Note,
    /// A route with the line stroke.
    Edge,
    /// A divider, an axis, a tick, a grid line, a guide, or a lifeline.
    Rule,
    /// A filled marker.
    Mark,
    /// A hollow marker.
    MarkHollow,
    /// A filled symbol.
    Ink,
    /// A stroke-only symbol.
    InkLine,
    /// A filled series shape.
    Series,
    /// An open series line.
    SeriesLine,
    /// A series area that can overlap another.
    SeriesTint,
    /// A series flow, such as a sankey link.
    SeriesFlow,
    /// An error symbol.
    Error,
    /// A warning symbol.
    Warning,
    /// A success symbol.
    Success,
    /// A plate behind a label, filled with the background token.
    Plate,
}

impl ShapeStyle {
    /// The style name of the `styles` table.
    pub const fn name(self) -> &'static str {
        match self {
            ShapeStyle::Node => "node",
            ShapeStyle::Group => "group",
            ShapeStyle::Band => "band",
            ShapeStyle::Note => "note",
            ShapeStyle::Edge => "edge",
            ShapeStyle::Rule => "rule",
            ShapeStyle::Mark => "mark",
            ShapeStyle::MarkHollow => "mark-hollow",
            ShapeStyle::Ink => "ink",
            ShapeStyle::InkLine => "ink-line",
            ShapeStyle::Series => "series",
            ShapeStyle::SeriesLine => "series-line",
            ShapeStyle::SeriesTint => "series-tint",
            ShapeStyle::SeriesFlow => "series-flow",
            ShapeStyle::Error => "error",
            ShapeStyle::Warning => "warning",
            ShapeStyle::Success => "success",
            ShapeStyle::Plate => "plate",
        }
    }
}

/// One style of the closed text style list of `spec/scene.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextStyle {
    /// The foreground token.
    Text,
    /// The muted token.
    TextMuted,
    /// The background token, for text on a filled symbol.
    TextInverse,
    /// The choice for the active theme and the series index of the fill.
    TextOnSeries,
}

impl TextStyle {
    /// The style name of the `styles` table.
    pub const fn name(self) -> &'static str {
        match self {
            TextStyle::Text => "text",
            TextStyle::TextMuted => "text-muted",
            TextStyle::TextInverse => "text-inverse",
            TextStyle::TextOnSeries => "text-on-series",
        }
    }
}

/// The mask of the shape style table, which is the row class of `spec/data/styles.json`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StyleClass {
    /// A shape style row.
    Shape,
    /// A text style row.
    Text,
}

impl StyleClass {
    /// The class number of the generated table.
    pub const fn code(self) -> u8 {
        match self {
            StyleClass::Shape => 0,
            StyleClass::Text => 1,
        }
    }
}

/// The stroke width of a shape primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Width {
    /// One px, which is 64 units.
    #[default]
    Normal,
    /// Two px, which is 128 units.
    Emphasis,
    /// An explicit width in units, used only by sankey links and treeview guides.
    Units(i32),
}

/// The line kind of a shape primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Line {
    /// An unbroken line.
    #[default]
    Solid,
    /// A dashed line.
    Dashed,
    /// A dotted line.
    Dotted,
    /// A double line, which only a cell-profile scene holds.
    Double,
}

impl Line {
    /// The line kind name of the style tables.
    pub const fn as_str(self) -> &'static str {
        match self {
            Line::Solid => "solid",
            Line::Dashed => "dashed",
            Line::Dotted => "dotted",
            Line::Double => "double",
        }
    }

    /// The line kind of a series line: `floor_mod(n, 3)` of the series index, so a series
    /// line never rests on colour alone.
    pub const fn for_series(series: u8) -> Line {
        match series % 3 {
            0 => Line::Solid,
            1 => Line::Dashed,
            _ => Line::Dotted,
        }
    }
}

/// The four fields that every shape primitive carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Shape {
    /// The shape style.
    pub style: ShapeStyle,
    /// The series index, 0 to 11; only a series style reads it.
    pub series: u8,
    /// The stroke width.
    pub width: Width,
    /// The line kind.
    pub line: Line,
}

impl Shape {
    /// A shape in one style, with stroke width `normal`, line kind `solid`, and series 0.
    pub const fn plain(style: ShapeStyle) -> Shape {
        Shape {
            style,
            series: 0,
            width: Width::Normal,
            line: Line::Solid,
        }
    }

    /// The same shape with another series index.
    pub const fn with_series(self, series: u8) -> Shape {
        Shape { series, ..self }
    }

    /// The same shape with another stroke width.
    pub const fn with_width(self, width: Width) -> Shape {
        Shape { width, ..self }
    }

    /// The same shape with another line kind.
    pub const fn with_line(self, line: Line) -> Shape {
        Shape { line, ..self }
    }
}

/// The role of a text item, which sets its size and weight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextRole {
    /// The diagram title.
    Title,
    /// Node, edge, group, actor, axis, and legend text.
    Label,
    /// Note and message text, and text with no other role.
    Body,
}

impl TextRole {
    /// The role name of the text tables.
    pub const fn as_str(self) -> &'static str {
        match self {
            TextRole::Title => "title",
            TextRole::Label => "label",
            TextRole::Body => "body",
        }
    }
}

/// The horizontal alignment of a text item inside its box.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Align {
    /// The box left edge.
    Start,
    /// The box centre.
    Middle,
    /// The box right edge.
    End,
}

impl Align {
    /// The alignment name of the back-end mappings.
    pub const fn as_str(self) -> &'static str {
        match self {
            Align::Start => "start",
            Align::Middle => "middle",
            Align::End => "end",
        }
    }
}

/// One styled run of a text line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Run {
    /// The run text.
    pub text: String,
    /// Whether the run is bold.
    pub bold: bool,
    /// Whether the run is italic.
    pub italic: bool,
}

impl Run {
    /// A plain run.
    pub fn plain(text: impl Into<String>) -> Run {
        Run {
            text: text.into(),
            bold: false,
            italic: false,
        }
    }
}

/// A text item: the text box, the role, the size, the alignment, the text style, the
/// series index of the fill the text sits on, and the wrapped lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextItem {
    /// The text box.
    pub rect: Rect,
    /// The text role.
    pub role: TextRole,
    /// The size in px.
    pub size: i32,
    /// The horizontal alignment.
    pub align: Align,
    /// The text style.
    pub style: TextStyle,
    /// The series index of the fill that the text sits on, or 0.
    pub series: u8,
    /// The wrapped lines; each line is a list of styled runs.
    pub lines: Vec<Vec<Run>>,
}

/// The direction from a route end toward the end point, which orients a marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MarkerAxis {
    /// Toward positive x.
    PlusX,
    /// Toward negative x.
    MinusX,
    /// Toward positive y, which points down on a page.
    PlusY,
    /// Toward negative y.
    MinusY,
}

impl MarkerAxis {
    /// The axis name of `spec/scene.md`.
    pub const fn as_str(self) -> &'static str {
        match self {
            MarkerAxis::PlusX => "+x",
            MarkerAxis::MinusX => "-x",
            MarkerAxis::PlusY => "+y",
            MarkerAxis::MinusY => "-y",
        }
    }
}

/// A marker name from `spec/data/markers.json`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MarkerName {
    name: &'static str,
}

impl MarkerName {
    /// The marker of that name, or `None` when the table holds no such row.
    pub fn new(name: &'static str) -> Option<MarkerName> {
        Self::row(name).map(|_| MarkerName { name })
    }

    fn row(name: &'static str) -> Option<&'static r#gen::markers::Marker> {
        r#gen::markers::MARKERS.iter().find(|row| row.name == name)
    }

    /// The marker name.
    pub const fn as_str(self) -> &'static str {
        self.name
    }

    /// The `paint` field of the marker, which selects its shape style.
    pub fn paint(self) -> Option<&'static str> {
        Self::row(self.name).map(|row| row.paint)
    }

    /// The flattened outline points of the marker, in units.
    pub fn points(self) -> &'static [(i32, i32)] {
        match Self::row(self.name) {
            Some(row) => row.points,
            None => &[],
        }
    }

    /// The reference point of the marker, in units.
    pub fn anchor(self) -> Option<(i32, i32)> {
        Self::row(self.name).map(|row| row.anchor)
    }
}

/// A cell symbol name from `spec/data/cell-symbols.json`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolName {
    name: &'static str,
}

impl SymbolName {
    /// The symbol of that name, or `None` when the table holds no such row.
    pub fn new(name: &'static str) -> Option<SymbolName> {
        Self::row(name).map(|_| SymbolName { name })
    }

    fn row(name: &'static str) -> Option<&'static r#gen::cellsymbols::Symbol> {
        r#gen::cellsymbols::CELL_SYMBOLS
            .iter()
            .find(|row| row.name == name)
    }

    /// The symbol name.
    pub const fn as_str(self) -> &'static str {
        self.name
    }

    /// The Unicode glyph code point of the symbol.
    pub fn unicode(self) -> Option<char> {
        Self::row(self.name).and_then(|row| char::from_u32(row.unicode))
    }

    /// The ASCII glyph of the symbol.
    pub fn ascii(self) -> Option<char> {
        Self::row(self.name).and_then(|row| char::from_u32(row.ascii))
    }
}

/// A rectangle primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RectItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The rectangle.
    pub rect: Rect,
}

/// A rectangle primitive with rounded corners.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RoundRectItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The rectangle.
    pub rect: Rect,
    /// The corner radius in units; 0 in the cell profile, where the primitive type alone
    /// selects rounded corners.
    pub r: i32,
}

/// An ellipse primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EllipseItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The centre x.
    pub cx: i32,
    /// The centre y.
    pub cy: i32,
    /// The x radius.
    pub rx: i32,
    /// The y radius.
    pub ry: i32,
}

/// A closed polygon primitive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolygonItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The vertices, at least three.
    pub points: Vec<Point>,
}

/// An open polyline primitive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolylineItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The points, at least two.
    pub points: Vec<Point>,
    /// The corner radius in units, where 0 means a sharp corner.
    pub corner: i32,
}

/// One command of a path primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathCommand {
    /// `M x y`, the start of a subpath.
    Move(Point),
    /// `L x y`, a line to a point.
    Line(Point),
    /// `C x1 y1 x2 y2 x y`, a cubic curve with two control points to an end point.
    Curve {
        /// The first control point.
        c1: Point,
        /// The second control point.
        c2: Point,
        /// The end point.
        to: Point,
    },
    /// `A cx cy r a0 sweep`, a circular arc given by centre, radius, start angle, and
    /// signed sweep, with angles in 1/65536 turn.
    Arc {
        /// The centre.
        centre: Point,
        /// The radius.
        r: i32,
        /// The start angle.
        start: i32,
        /// The signed sweep.
        sweep: i32,
    },
    /// `Z`, which closes the subpath.
    Close,
}

/// A path primitive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathItem {
    /// The four shape fields.
    pub shape: Shape,
    /// The commands.
    pub commands: Vec<PathCommand>,
}

/// A marker at a route end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MarkerRefItem {
    /// The marker name.
    pub marker: MarkerName,
    /// The route end point.
    pub at: Point,
    /// The direction toward the end point.
    pub axis: MarkerAxis,
}

/// One cell-profile symbol drawn at a cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRefItem {
    /// The symbol name.
    pub symbol: SymbolName,
    /// The cell.
    pub at: Point,
    /// The shape style, used for colour only.
    pub style: ShapeStyle,
}

/// The class of a scene item, which fixes its place inside a group.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ItemClass {
    /// A shape primitive.
    Shape,
    /// A marker.
    Marker,
    /// A cell symbol.
    Symbol,
    /// A text item.
    Text,
}

impl ItemClass {
    /// The class name, for reports.
    pub const fn as_str(self) -> &'static str {
        match self {
            ItemClass::Shape => "shape",
            ItemClass::Marker => "marker",
            ItemClass::Symbol => "symbol",
            ItemClass::Text => "text",
        }
    }
}

/// One primitive of the closed primitive set of `spec/scene.md`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// A rectangle.
    Rect(RectItem),
    /// A rectangle with rounded corners.
    RoundRect(RoundRectItem),
    /// An ellipse.
    Ellipse(EllipseItem),
    /// A closed polygon.
    Polygon(PolygonItem),
    /// An open polyline.
    Polyline(PolylineItem),
    /// A path.
    Path(PathItem),
    /// A text item.
    Text(TextItem),
    /// A marker at a route end.
    MarkerRef(MarkerRefItem),
    /// A cell-profile symbol.
    SymbolRef(SymbolRefItem),
}

impl Item {
    /// The class of the item, which fixes its place inside a group.
    pub const fn class(&self) -> ItemClass {
        match self {
            Item::Rect(_)
            | Item::RoundRect(_)
            | Item::Ellipse(_)
            | Item::Polygon(_)
            | Item::Polyline(_)
            | Item::Path(_) => ItemClass::Shape,
            Item::MarkerRef(_) => ItemClass::Marker,
            Item::SymbolRef(_) => ItemClass::Symbol,
            Item::Text(_) => ItemClass::Text,
        }
    }
}

/// The role of a group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupRole {
    /// A decoration under the diagram, over it, or both.
    Decor,
    /// A frame: one group for each dump box with role `group`.
    Group,
    /// One group for each dump route.
    Edge,
    /// One group for each dump box with role `node`.
    Node,
}

impl GroupRole {
    /// The role name of the group's class attribute.
    pub const fn as_str(self) -> &'static str {
        match self {
            GroupRole::Decor => "decor",
            GroupRole::Group => "group",
            GroupRole::Edge => "edge",
            GroupRole::Node => "node",
        }
    }
}

/// One group of the display list: a role, an owner, and its primitives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    /// The group role.
    pub role: GroupRole,
    /// The id of the dump box for roles `group` and `node`, the id of the dump route for
    /// role `edge`, and the empty string for `decor`.
    pub owner: String,
    /// The primitives, in draw order.
    pub items: Vec<Item>,
}

impl Group {
    /// A group of one role with one owner.
    pub fn new(role: GroupRole, owner: impl Into<String>) -> Group {
        Group {
            role,
            owner: owner.into(),
            items: Vec::new(),
        }
    }

    /// The same group with its items replaced.
    pub fn with_items(mut self, items: Vec<Item>) -> Group {
        self.items = items;
        self
    }
}

/// The first violation of the group rules of `spec/scene.md`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum GroupOrder {
    /// A decor group is neither the first group nor the last group.
    #[error("group {group} is neither the leading nor the trailing decor group")]
    UnexpectedDecor {
        /// The group index.
        group: usize,
    },
    /// A decor group carries an owner.
    #[error("decor group {group} carries the owner {owner}")]
    DecorOwner {
        /// The group index.
        group: usize,
        /// The owner the group carries.
        owner: String,
    },
    /// A group draws an owner other than the one its place calls for.
    #[error("group {group} draws {expected} {owner_expected}, not {owner}")]
    OwnerMismatch {
        /// The group index.
        group: usize,
        /// The group role the place calls for.
        expected: &'static str,
        /// The owner the place calls for.
        owner_expected: String,
        /// The owner the group carries.
        owner: String,
    },
    /// A group draws an owner that the dump does not hold.
    #[error("group {group} draws a {role} that the dump does not hold")]
    UnexpectedGroup {
        /// The group index.
        group: usize,
        /// The group role.
        role: &'static str,
    },
    /// A dump box or route has no group.
    #[error("{role} {id} has no group")]
    MissingGroup {
        /// The group role that is missing.
        role: &'static str,
        /// The owner id that has no group.
        id: String,
    },
    /// A group places an item of an earlier class after a later one.
    #[error("group {group} places a {later} item after a {earlier} item")]
    ItemOrder {
        /// The group index.
        group: usize,
        /// The class of the earlier item.
        earlier: &'static str,
        /// The class of the later item.
        later: &'static str,
    },
}

/// One owner that the body groups must draw, in group order.
struct Expected {
    role: GroupRole,
    owner: String,
}

/// The owners that the body groups must draw, in the group order of `spec/scene.md`: one
/// group per dump box with role `group`, then one per dump route, then one per dump box
/// with role `node`.
fn expected_owners(dump: &Dump) -> Vec<Expected> {
    let mut expected = Vec::new();
    let groups = dump.boxes.iter().filter(|b| b.role == BoxRole::Group);
    expected.extend(groups.map(|b| Expected {
        role: GroupRole::Group,
        owner: b.id.clone(),
    }));
    expected.extend(dump.routes.iter().map(|r| Expected {
        role: GroupRole::Edge,
        owner: r.id.clone(),
    }));
    let nodes = dump.boxes.iter().filter(|b| b.role == BoxRole::Node);
    expected.extend(nodes.map(|b| Expected {
        role: GroupRole::Node,
        owner: b.id.clone(),
    }));
    expected
}

/// Checks the group rules of `spec/scene.md`: at most one decor group before and one after
/// the body, one group per dump owner in dump order, an empty owner for decor, and the item
/// classes of a group in non-decreasing order.
pub fn check_groups(groups: &[Group], dump: &Dump) -> Result<(), GroupOrder> {
    let last = groups.len().saturating_sub(1);
    for (index, group) in groups.iter().enumerate() {
        check_item_order(index, &group.items)?;
        if group.role != GroupRole::Decor {
            continue;
        }
        if !group.owner.is_empty() {
            return Err(GroupOrder::DecorOwner {
                group: index,
                owner: group.owner.clone(),
            });
        }
        if index != 0 && index != last {
            return Err(GroupOrder::UnexpectedDecor { group: index });
        }
    }
    let expected = expected_owners(dump);
    let body: Vec<(usize, &Group)> = groups
        .iter()
        .enumerate()
        .filter(|(_, group)| group.role != GroupRole::Decor)
        .collect();
    for (position, (index, group)) in body.iter().enumerate() {
        let Some(want) = expected.get(position) else {
            return Err(GroupOrder::UnexpectedGroup {
                group: *index,
                role: group.role.as_str(),
            });
        };
        if want.role != group.role || want.owner != group.owner {
            return Err(GroupOrder::OwnerMismatch {
                group: *index,
                expected: want.role.as_str(),
                owner_expected: want.owner.clone(),
                owner: group.owner.clone(),
            });
        }
    }
    match expected.get(body.len()) {
        None => Ok(()),
        Some(want) => Err(GroupOrder::MissingGroup {
            role: want.role.as_str(),
            id: want.owner.clone(),
        }),
    }
}

/// Checks that the item classes of one group do not decrease.
fn check_item_order(group: usize, items: &[Item]) -> Result<(), GroupOrder> {
    items.windows(2).try_for_each(|pair| {
        let earlier = pair[0].class();
        let later = pair[1].class();
        if later < earlier {
            return Err(GroupOrder::ItemOrder {
                group,
                earlier: earlier.as_str(),
                later: later.as_str(),
            });
        }
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geom::{Point, Rect};

    fn rect(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect { x, y, w, h }
    }

    fn node(id: &str) -> SceneBox {
        SceneBox {
            id: id.to_owned(),
            role: BoxRole::Node,
            rect: rect(0, 0, 10, 10),
            parent: String::new(),
            exclusive: true,
        }
    }

    fn text_item() -> Item {
        Item::Text(TextItem {
            rect: rect(0, 0, 10, 10),
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: vec![vec![Run::plain("A")]],
        })
    }

    fn shape_item() -> Item {
        Item::Rect(RectItem {
            shape: Shape::plain(ShapeStyle::Node),
            rect: rect(0, 0, 10, 10),
        })
    }

    fn marker_item() -> Option<Item> {
        Some(Item::MarkerRef(MarkerRefItem {
            marker: MarkerName::new("arrowhead")?,
            at: Point { x: 0, y: 0 },
            axis: MarkerAxis::PlusX,
        }))
    }

    fn symbol_item() -> Option<Item> {
        Some(Item::SymbolRef(SymbolRefItem {
            symbol: SymbolName::new("disc")?,
            at: Point { x: 0, y: 0 },
            style: ShapeStyle::Ink,
        }))
    }

    fn two_node_dump() -> Dump {
        let mut dump = Dump::new("flowchart", DumpOptions::default());
        dump.boxes.push(node("A"));
        let mut b = node("B");
        b.rect.y = 20;
        dump.boxes.push(b);
        dump.routes.push(SceneRoute {
            id: String::from("e0"),
            from: String::from("A"),
            to: String::from("B"),
            orthogonal: true,
            points: vec![Point { x: 0, y: 10 }, Point { x: 0, y: 20 }],
            marker_start: String::new(),
            marker_end: String::new(),
            stroke: String::new(),
        });
        dump
    }

    fn group(role: GroupRole, owner: &str, items: Vec<Item>) -> Group {
        Group::new(role, owner).with_items(items)
    }

    #[test]
    fn every_shape_style_is_a_shape_row_of_the_table() {
        let table: Vec<&str> = r#gen::styles::STYLES
            .iter()
            .filter(|row| row.class == StyleClass::Shape.code())
            .map(|row| row.name)
            .collect();
        let names: Vec<&str> = [
            ShapeStyle::Node,
            ShapeStyle::Group,
            ShapeStyle::Band,
            ShapeStyle::Note,
            ShapeStyle::Edge,
            ShapeStyle::Rule,
            ShapeStyle::Mark,
            ShapeStyle::MarkHollow,
            ShapeStyle::Ink,
            ShapeStyle::InkLine,
            ShapeStyle::Series,
            ShapeStyle::SeriesLine,
            ShapeStyle::SeriesTint,
            ShapeStyle::SeriesFlow,
            ShapeStyle::Error,
            ShapeStyle::Warning,
            ShapeStyle::Success,
            ShapeStyle::Plate,
        ]
        .iter()
        .map(|style| style.name())
        .collect();
        assert_eq!(names.len(), table.len());
        for name in names {
            assert!(table.contains(&name), "{name} is not a shape row");
        }
    }

    #[test]
    fn every_text_style_is_a_text_row_of_the_table() {
        let table: Vec<&str> = r#gen::styles::STYLES
            .iter()
            .filter(|row| row.class == StyleClass::Text.code())
            .map(|row| row.name)
            .collect();
        let names: Vec<&str> = [
            TextStyle::Text,
            TextStyle::TextMuted,
            TextStyle::TextInverse,
            TextStyle::TextOnSeries,
        ]
        .iter()
        .map(|style| style.name())
        .collect();
        assert_eq!(names.len(), table.len());
        for name in names {
            assert!(table.contains(&name), "{name} is not a text row");
        }
    }

    #[test]
    fn profile_and_direction_names_are_fixed() {
        assert_eq!(Profile::Vector.as_str(), "vector");
        assert_eq!(Profile::Cell.as_str(), "cell");
        assert_eq!(Direction::Tb.as_str(), "TB");
        assert_eq!(Direction::Bt.as_str(), "BT");
        assert_eq!(Direction::Lr.as_str(), "LR");
        assert_eq!(Direction::Rl.as_str(), "RL");
        assert_eq!(Profile::default(), Profile::Vector);
        assert_eq!(Direction::default(), Direction::Tb);
    }

    #[test]
    fn td_resolves_to_tb() {
        assert_eq!(Direction::from_token("TD"), Some(Direction::Tb));
        assert_eq!(Direction::from_token("tb"), Some(Direction::Tb));
        assert_eq!(Direction::from_token(" RL "), Some(Direction::Rl));
        assert_eq!(Direction::from_token("TB"), Some(Direction::Tb));
        assert_eq!(Direction::from_token("XX"), None);
        assert_eq!(Direction::from_token(""), None);
    }

    #[test]
    fn limits_defaults_match_the_dump_spec() {
        let limits = Limits::default();
        assert_eq!(limits.max_nodes, 2000);
        assert_eq!(limits.max_edges, 5000);
        assert_eq!(limits.max_text_bytes, 1_048_576);
        let options = DumpOptions::default();
        assert_eq!(options.thoroughness, 3);
        assert_eq!(options.max_width, 0);
        assert!(options.config.is_empty());
    }

    #[test]
    fn series_lines_never_rest_on_colour_alone() {
        let kinds: Vec<Line> = (0..12u8).map(Line::for_series).collect();
        assert_eq!(kinds[0], Line::Solid);
        assert_eq!(kinds[1], Line::Dashed);
        assert_eq!(kinds[2], Line::Dotted);
        assert_eq!(kinds[3], Line::Solid);
        assert_eq!(kinds[11], Line::Dotted);
        assert_eq!(Line::Dotted.as_str(), "dotted");
        assert_eq!(Line::Double.as_str(), "double");
        assert_eq!(Line::default(), Line::Solid);
        assert_eq!(Width::default(), Width::Normal);
    }

    #[test]
    fn marker_names_are_checked_against_the_table() {
        let arrowhead = MarkerName::new("arrowhead").map(MarkerName::as_str);
        assert_eq!(arrowhead, Some("arrowhead"));
        assert_eq!(MarkerName::new("no-such-marker"), None);
        let paint = MarkerName::new("point").and_then(MarkerName::paint);
        assert_eq!(paint, Some("filled"));
        let hollow = MarkerName::new("extension").and_then(MarkerName::paint);
        assert_eq!(hollow, Some("hollow"));
        let open = MarkerName::new("openArrow").and_then(MarkerName::paint);
        assert_eq!(open, Some("open"));
    }

    #[test]
    fn symbol_names_are_checked_against_the_table() {
        let disc = SymbolName::new("disc").map(SymbolName::as_str);
        assert_eq!(disc, Some("disc"));
        assert_eq!(SymbolName::new("no-such-symbol"), None);
        assert_eq!(
            SymbolName::new("disc").and_then(SymbolName::unicode),
            Some('●')
        );
        assert_eq!(
            SymbolName::new("disc").and_then(SymbolName::ascii),
            Some('*')
        );
        assert_eq!(
            SymbolName::new("bullseye").and_then(SymbolName::ascii),
            Some('@')
        );
    }

    #[test]
    fn item_classes_follow_the_closed_order() {
        assert_eq!(shape_item().class(), ItemClass::Shape);
        assert_eq!(
            marker_item().map(|item| item.class()),
            Some(ItemClass::Marker)
        );
        assert_eq!(
            symbol_item().map(|item| item.class()),
            Some(ItemClass::Symbol)
        );
        assert_eq!(text_item().class(), ItemClass::Text);
        assert!(ItemClass::Shape < ItemClass::Marker);
        assert!(ItemClass::Marker < ItemClass::Symbol);
        assert!(ItemClass::Symbol < ItemClass::Text);
    }

    #[test]
    fn shape_builders_change_one_field_at_a_time() {
        let shape = Shape::plain(ShapeStyle::SeriesLine)
            .with_series(4)
            .with_line(Line::for_series(4))
            .with_width(Width::Emphasis);
        assert_eq!(shape.style, ShapeStyle::SeriesLine);
        assert_eq!(shape.series, 4);
        assert_eq!(shape.line, Line::Dashed);
        assert_eq!(shape.width, Width::Emphasis);
        let plain = Shape::plain(ShapeStyle::Node);
        assert_eq!(plain.series, 0);
        assert_eq!(plain.width, Width::Normal);
        assert_eq!(plain.line, Line::Solid);
    }

    #[test]
    fn roles_and_alignments_have_fixed_names() {
        assert_eq!(TextRole::Title.as_str(), "title");
        assert_eq!(TextRole::Label.as_str(), "label");
        assert_eq!(TextRole::Body.as_str(), "body");
        assert_eq!(Align::Start.as_str(), "start");
        assert_eq!(Align::Middle.as_str(), "middle");
        assert_eq!(Align::End.as_str(), "end");
    }

    #[test]
    fn group_and_box_roles_have_fixed_names() {
        assert_eq!(GroupRole::Decor.as_str(), "decor");
        assert_eq!(GroupRole::Group.as_str(), "group");
        assert_eq!(GroupRole::Edge.as_str(), "edge");
        assert_eq!(GroupRole::Node.as_str(), "node");
        assert_eq!(BoxRole::Node.as_str(), "node");
        assert_eq!(BoxRole::Group.as_str(), "group");
        assert_eq!(BoxRole::from_name("group"), Some(BoxRole::Group));
        assert_eq!(BoxRole::from_name("frame"), None);
        assert_eq!(MarkerAxis::MinusY.as_str(), "-y");
        assert_eq!(ItemClass::Text.as_str(), "text");
        assert_eq!(StyleClass::Text.code(), 1);
    }

    #[test]
    fn scene_reports_its_parts() {
        let dump = two_node_dump();
        let scene = Scene::new(
            Size { w: 30, h: 40 },
            dump,
            vec![group(GroupRole::Node, "A", vec![shape_item()])],
        );
        assert_eq!(scene.canvas(), Size { w: 30, h: 40 });
        assert_eq!(scene.profile(), Profile::Vector);
        assert_eq!(scene.boxes().len(), 2);
        assert_eq!(scene.routes().len(), 1);
        assert!(scene.labels().is_empty());
        assert_eq!(scene.items().len(), 1);
        assert_eq!(scene.dump_part().kind, "flowchart");
        assert!(scene.check().unwrap_or(false));
    }

    #[test]
    fn a_well_ordered_scene_passes_the_group_rules() {
        let dump = two_node_dump();
        let groups = vec![
            group(GroupRole::Decor, "", vec![shape_item()]),
            group(GroupRole::Edge, "e0", vec![shape_item()]),
            group(GroupRole::Node, "A", vec![shape_item(), text_item()]),
            group(GroupRole::Node, "B", vec![text_item()]),
            group(GroupRole::Decor, "", vec![text_item()]),
        ];
        assert_eq!(check_groups(&groups, &dump), Ok(()));
    }

    #[test]
    fn a_decor_group_in_the_middle_is_rejected() {
        let dump = two_node_dump();
        let groups = vec![
            group(GroupRole::Node, "A", Vec::new()),
            group(GroupRole::Decor, "", Vec::new()),
            group(GroupRole::Node, "B", Vec::new()),
        ];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::UnexpectedDecor { group: 1 })
        );
    }

    #[test]
    fn a_decor_group_with_an_owner_is_rejected() {
        let dump = two_node_dump();
        let groups = vec![group(GroupRole::Decor, "A", Vec::new())];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::DecorOwner {
                group: 0,
                owner: String::from("A"),
            })
        );
    }

    #[test]
    fn groups_must_follow_dump_order() {
        let mut dump = two_node_dump();
        dump.routes.clear();
        let groups = vec![
            group(GroupRole::Node, "B", Vec::new()),
            group(GroupRole::Node, "A", Vec::new()),
        ];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::OwnerMismatch {
                group: 0,
                expected: "node",
                owner_expected: String::from("A"),
                owner: String::from("B"),
            })
        );
    }

    #[test]
    fn groups_must_follow_the_role_order() {
        let dump = two_node_dump();
        let groups = vec![
            group(GroupRole::Node, "A", Vec::new()),
            group(GroupRole::Edge, "e0", Vec::new()),
            group(GroupRole::Node, "B", Vec::new()),
        ];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::OwnerMismatch {
                group: 0,
                expected: "edge",
                owner_expected: String::from("e0"),
                owner: String::from("A"),
            })
        );
    }

    #[test]
    fn a_missing_group_is_rejected() {
        let dump = two_node_dump();
        let groups = vec![
            group(GroupRole::Edge, "e0", Vec::new()),
            group(GroupRole::Node, "A", Vec::new()),
        ];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::MissingGroup {
                role: "node",
                id: String::from("B"),
            })
        );
    }

    #[test]
    fn an_extra_group_is_rejected() {
        let dump = two_node_dump();
        let groups = vec![
            group(GroupRole::Edge, "e0", Vec::new()),
            group(GroupRole::Node, "A", Vec::new()),
            group(GroupRole::Node, "B", Vec::new()),
            group(GroupRole::Edge, "e1", Vec::new()),
        ];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::UnexpectedGroup {
                group: 3,
                role: "edge",
            })
        );
    }

    #[test]
    fn item_classes_must_not_decrease() {
        let dump = two_node_dump();
        let groups = vec![group(GroupRole::Node, "A", vec![text_item(), shape_item()])];
        assert_eq!(
            check_groups(&groups, &dump),
            Err(GroupOrder::ItemOrder {
                group: 0,
                earlier: "text",
                later: "shape",
            })
        );
    }

    #[test]
    fn scene_is_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Scene>();
        assert_send_sync::<Dump>();
        assert_send_sync::<Group>();
    }
}
