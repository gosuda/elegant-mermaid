//! Parse, check, lint, lay out, and render Mermaid diagrams as SVG, PNG, or
//! terminal text.
//!
//! # Determinism
//!
//! The core library never reads the network, the host font set, the clock,
//! or a random source. Output depends only on the input text and the options
//! passed to a call. All geometry is integer; floating point does not appear
//! in the layout path. Parsing never fails: every input problem is reported
//! as a diagnostic with a byte span.
//!
//! # Concurrency and safety
//!
//! Documents are immutable after parsing. Documents and rendered scenes are
//! safe for concurrent use: they are `Send` and `Sync`. The crate forbids
//! `unsafe` code outright.
//!
//! # Targets
//!
//! The minimum supported Rust version is 1.99. The crate builds for
//! `wasm32-unknown-unknown` in addition to native targets.
//!
//! # Stability
//!
//! Diagnostic codes are stable identifiers. A renamed code keeps its old
//! name as an alias in the registry, and a code is never reused. Before
//! 1.0, a minor version may change the public API.
#![forbid(unsafe_code)]
#![deny(clippy::disallowed_methods, clippy::disallowed_types)]

pub mod cells;
pub mod diag;
pub mod error;
pub(crate) mod r#gen;
pub mod geom;
pub mod kind;
pub mod layout;
pub mod markdown;
pub mod measure;
pub mod model;
pub mod options;
pub mod scene;
pub mod source;
pub mod syntax;

pub use diag::{Diagnostic, Edit, Fix, FixSafety, Related, Severity};
pub use error::{IconPackError, RasterError, RenderError};
pub use kind::DiagramKind;
pub use options::{
    Cancel, Charset, ColorMode, FixOutcome, LayoutOptions, Limits, LintConfig, Profile, SvgOptions,
    TextMode, TextOptions,
};
pub use source::{Position, Span};
