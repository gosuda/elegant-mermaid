pub mod braille;
pub mod canvas;
pub mod colour;
pub mod join;
pub mod serialise;
pub use canvas::{Canvas, Cell, Label, merge_cell};
pub use colour::{ColorMode, Rgb, Token};
pub use join::Charset;
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
