pub mod braille;
pub mod canvas;
pub mod colour;
pub mod join;
pub mod place;
pub mod render;
pub mod serialise;
pub use canvas::{Canvas, Cell, Label, merge_cell};
pub use colour::{ColorMode, Rgb, Token};
pub use join::Charset;
pub use render::{Options, ProfileError, RenderError, RenderResult, render};
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Style {
    #[default]
    None,
    Dotted,
    Rounded,
    Light,
    Heavy,
    Double,
}
#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests;
