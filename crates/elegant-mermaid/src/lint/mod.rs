//! The lint engine: rule registry order, effective severities, suppression
//! comments, `emd.json` configuration, fix application, and the four output
//! formats of `spec/lint.md` and `spec/diagnostics.md`.

mod architecture;
mod block;
mod c4;
mod class;
mod common;
mod config;
mod describe;
mod engine;
mod er;
mod eventmodeling;
#[cfg(test)]
mod eventmodeling_test;
mod flowchart;
pub mod format;
mod gantt;
mod gitgraph;
mod host;
mod ishikawa;
mod journey;
mod kanban;
mod mindmap;
mod packet;
#[cfg(test)]
mod packet_test;
mod pie;
mod quadrant;
mod radar;
#[cfg(test)]
mod radar_test;
mod requirement;
mod sankey;
mod sequence;
mod state;
pub mod suppression;
#[cfg(test)]
mod tests;
mod timeline;
#[cfg(test)]
mod timeline_test;
mod treemap;
mod treeview;
mod venn;
mod wardley;
mod xychart;
#[cfg(test)]
mod xychart_test;

pub use config::{ConfigError, find_config, load_config, parse_config};
pub use describe::{Described, describe, validate_codes};
pub use engine::{apply_fixes, lint, lint_document};
pub use host::{HostReport, apply_host_fixes, lint_host};
