use crate::scene::{BoxRole, Direction, DumpOptions, Profile, TextRole};

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
}
#[derive(Debug, Clone)]
pub struct Box {
    pub id: String,
    pub role: BoxRole,
    pub shape: String,
    pub parent: String,
    pub exclusive: bool,
    pub text: String,
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
    pub text: String,
}
