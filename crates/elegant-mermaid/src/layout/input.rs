use crate::scene::{BoxRole, Direction, DumpOptions, Profile, TextRole};

/// The physical sizing policy for a layout box.
#[derive(Debug, Clone, Copy, Default)]
pub enum SizeRule {
    /// Measure text, then apply ordinary minimum sizes and port widening.
    #[default]
    Measured,
    /// Override content size, retaining ordinary minima and port widening.
    /// A zero-by-zero size falls back to text measurement.
    Content(crate::geom::Size),
    /// Preserve nonnegative physical dimensions through ports and self-loops.
    /// External loop geometry takes separate layout reservations.
    Exact(crate::geom::Size),
}

#[derive(Debug, Clone)]
pub struct Input {
    pub kind: &'static str,
    pub profile: Profile,
    pub direction: Direction,
    pub options: DumpOptions,
    pub boxes: Vec<Box>,
    pub routes: Vec<Route>,
    pub labels: Vec<Label>,
    pub groups: Vec<Group>,
    pub sizes: Vec<SizeRule>,
    /// Side constraints over original box indices; envelopes never enter the dump.
    pub attachments: Vec<Attachment>,
    pub region_sets: Vec<RegionSet>,
    pub spacing: Spacing,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Spacing {
    pub node_gap: i32,
    pub rank_gap: i32,
    pub canvas_margin: i32,
}

impl Spacing {
    pub fn for_kind(profile: Profile, kind: &str) -> Self {
        let value = |name: &str| {
            let key = format!("{}.{kind}.{name}", profile.as_str());
            crate::r#gen::layoutconst::LAYOUT_CONST
                .iter()
                .find(|row| row.name == key)
                .map_or(0, |row| row.value)
        };
        Self {
            node_gap: value("node_spacing"),
            rank_gap: value("rank_spacing"),
            canvas_margin: value("diagram_padding"),
        }
    }
}

/// Ordered child groups of one concurrent composite, using group indices.
#[derive(Debug, Clone, Default)]
pub struct RegionSet {
    pub parent: usize,
    pub regions: Vec<usize>,
}

/// A note and its target share a semantic parent. A target may have several notes.
#[derive(Debug, Clone, Copy)]
pub struct Attachment {
    pub target: usize,
    pub note: usize,
    pub side: AttachmentSide,
}

/// The note's side in final screen coordinates, independent of layout direction.
#[derive(Debug, Clone, Copy)]
pub enum AttachmentSide {
    Left,
    Right,
}
#[derive(Debug, Clone)]
pub struct Box {
    pub id: String,
    pub role: BoxRole,
    pub shape: String,
    pub icon: bool,
    pub parent: String,
    pub exclusive: bool,
    pub text: String,
    pub direction: String,
}
/// An endpoint face in final screen coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RouteSide {
    Up,
    Down,
    Left,
    Right,
}

impl RouteSide {
    pub(crate) const fn token(self) -> &'static str {
        match self {
            Self::Up => "T",
            Self::Down => "B",
            Self::Left => "L",
            Self::Right => "R",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Route {
    pub id: String,
    pub from: String,
    pub to: String,
    pub orthogonal: bool,
    pub marker_start: String,
    pub marker_end: String,
    pub line: String,
    pub min_length: usize,
    pub from_side: Option<RouteSide>,
    pub to_side: Option<RouteSide>,
}
#[derive(Debug, Clone)]
pub struct Label {
    pub id: String,
    pub owner: String,
    pub role: TextRole,
    pub text: String,
}
#[derive(Debug, Clone)]
pub struct Group {
    pub id: String,
    pub parent: String,
    pub direction: String,
    pub direction_span: crate::source::Span,
}
