//! Pre-routing cross-axis reservations in internal TB space.
//! Reservations describe complete algorithmic footprints, not physical symbol boxes.
//! Internal return lanes occupy the trailing interior strip of their owning frame;
//! minimum-width slack belongs before that strip, not between it and the frame.

mod metadata;
mod placement;
mod reserve;

pub use super::LayoutError;
pub use metadata::{ComponentSets, Footprints, Metadata};
pub use placement::{CoordinateInput, CrossTree, Placement};
pub use reserve::Constraints;

#[cfg(test)]
use reserve::*;

#[cfg(test)]
mod tests;
