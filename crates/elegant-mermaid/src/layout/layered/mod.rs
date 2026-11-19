mod cluster_order;
pub mod clusters;
pub mod coords;
mod cost;
pub mod cycles;
pub mod graph;
mod gutters;
mod isolate;
pub mod labels;
pub mod lanes;
pub mod loops;
pub mod normalize;
pub mod order;
pub mod pack;
pub mod pipeline;
pub mod portfolio;
pub mod rank;
mod regions;
pub mod route;
mod sibling_order;

pub use crate::geom::GeomError as LayoutError;

#[cfg(test)]
mod proxy_span_tests;

#[cfg(test)]
mod region_tests;
