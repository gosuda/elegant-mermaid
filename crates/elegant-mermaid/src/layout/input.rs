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
}
#[derive(Debug, Clone)]
pub struct Box {
    pub id: String,
    pub role: BoxRole,
    pub shape: String,
    pub parent: String,
    pub exclusive: bool,
    pub text: String,
    pub direction: String,
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
