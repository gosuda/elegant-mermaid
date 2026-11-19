use crate::r#gen;
use crate::geom::{Point, Rect};

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
