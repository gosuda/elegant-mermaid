//! The failures of every command, worded as the Go CLI words them.
//!
//! A usage or input failure exits 2. A command prints its failure as one line
//! on stderr.

use crate::termgfx::GfxError;
use elegant_mermaid::cells::render::RenderError as CellsError;
use elegant_mermaid::geom::GeomError;
use elegant_mermaid::lint::ConfigError;
use elegant_mermaid::scene::metrics::DumpError;
use elegant_mermaid::theme::ThemeError;
use elegant_mermaid::{IconPackError, RasterError, RenderError, svg};
use std::io;
use std::num::TryFromIntError;

/// The text of an operating-system failure, as Go's `syscall.Errno` words it:
/// the system message in lower case, without the operation, the path, or the
/// error number.
pub fn os_text(error: &io::Error) -> String {
    let text = error.to_string();
    let message = error
        .raw_os_error()
        .and_then(|code| text.strip_suffix(&format!(" (os error {code})")))
        .unwrap_or(&text);
    let mut characters = message.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}

/// A command line that the command cannot run.
#[derive(Debug, thiserror::Error)]
pub enum UsageError {
    #[error("unknown flag {flag}; run emd {command} --help")]
    UnknownFlag { flag: String, command: &'static str },
    #[error("unknown command {command}; run emd --help")]
    UnknownCommand { command: String },
    #[error("missing value for {flag}")]
    MissingValue { flag: String },
    #[error("invalid value {value} for {flag}; expected one of: {choices}")]
    InvalidValue {
        value: String,
        flag: String,
        choices: String,
    },
    #[error("{command} accepts one INPUT")]
    ExtraInput { command: &'static str },
    #[error("pass input either as INPUT or with -i, not both")]
    InputTwice,
    #[error("cannot infer the output format from {output}; pass -e")]
    UnknownFormat { output: String },
    #[error("cannot write PNG to a terminal; use -o FILE.png or redirect stdout to a file")]
    PngToTerminal,
    #[error("--metrics needs --profile vector")]
    MetricsNeedVector,
    #[error("--dump requires --metrics")]
    DumpNeedsMetrics,
    #[error("--unsafe-fixes requires --fix")]
    UnsafeFixesNeedFix,
    #[error(
        "lint --fix - supports only text diagnostics; remove --output-format or pass a file path"
    )]
    FixStdinFormat,
    #[error("missing CODE; run emd explain --help")]
    MissingCode,
    #[error("unexpected argument {extra}; run emd explain --help")]
    ExtraCode { extra: String },
    #[error("view requires a readable file path; stdin is not supported")]
    ViewNeedsFile,
    #[error("view requires a terminal unless --script is used")]
    ViewNeedsTerminal,
}

/// A file or stream that cannot be read.
#[derive(Debug, thiserror::Error)]
pub enum InputError {
    #[error("missing INPUT; pass a path or pipe Mermaid source")]
    Missing,
    #[error("cannot read {path}: {}", os_text(.source))]
    Read { path: String, source: io::Error },
}

/// A failure of `check`, `lint`, `explain`, `layout`, or `render`.
#[derive(Debug, thiserror::Error)]
pub enum CliError {
    #[error(transparent)]
    Usage(#[from] UsageError),
    #[error(transparent)]
    Input(#[from] InputError),
    #[error(transparent)]
    Config(#[from] ConfigError),
    #[error("cannot write {path}: {}", os_text(.source))]
    Write { path: String, source: io::Error },
    #[error("no Mermaid files found in {root}")]
    NoFiles { root: String },
    #[error("unsupported diagram kind")]
    UnsupportedKind,
    #[error("{path}: invalid config: {message}")]
    InvalidConfig { path: String, message: String },
    #[error("{path}: {source}")]
    MalformedIconPack { path: String, source: IconPackError },
    #[error("{path}: {source}")]
    MalformedDump { path: String, source: DumpError },
    #[error(transparent)]
    Render(#[from] RenderError),
    #[error(transparent)]
    Raster(#[from] RasterError),
    #[error(transparent)]
    Svg(#[from] svg::ConfigError),
    #[error(transparent)]
    Cells(#[from] CellsError),
    #[error(transparent)]
    Geom(#[from] GeomError),
    #[error(transparent)]
    Io(#[from] io::Error),
}

/// A failure of one line of a `view --script` file.
#[derive(Debug, thiserror::Error)]
pub enum ReplayError {
    #[error("unknown verb {verb}")]
    UnknownVerb { verb: String },
    #[error("settle takes no arguments")]
    SettleArguments,
    #[error("file-delete takes no arguments")]
    DeleteArguments,
    #[error("missing source path")]
    MissingSource,
    #[error("expected resize W H")]
    ResizeArguments,
    #[error("size requires W >= 20 and H >= 5")]
    SizeBelowMinimum,
    #[error("invalid key")]
    InvalidKey,
    #[error("invalid UTF-8")]
    InvalidUtf8,
    #[error(transparent)]
    Input(#[from] InputError),
    #[error(transparent)]
    Overflow(#[from] TryFromIntError),
}

/// A failure of `view`.
#[derive(Debug, thiserror::Error)]
pub enum ViewError {
    #[error(transparent)]
    Usage(#[from] UsageError),
    #[error(transparent)]
    Input(#[from] InputError),
    #[error(transparent)]
    Theme(#[from] ThemeError),
    #[error("{script}:{line}: {source}")]
    Script {
        script: String,
        line: usize,
        source: ReplayError,
    },
    #[error("cannot configure terminal input")]
    TerminalInput,
    #[error("cannot configure terminal probe")]
    ProbeConfigure,
    #[error("cannot restore terminal probe")]
    ProbeRestore,
    #[error("missing parent directory")]
    NoParent,
    #[error("render worker failed")]
    WorkerFailed,
    #[error("invalid graphics mode")]
    GraphicsMode,
    #[error("viewport too large")]
    ViewportTooLarge,
    #[error(transparent)]
    Watch(#[from] notify::Error),
    #[error(transparent)]
    Render(#[from] RenderError),
    #[error(transparent)]
    Raster(#[from] RasterError),
    #[error(transparent)]
    Gfx(#[from] GfxError),
    #[error(transparent)]
    Overflow(#[from] TryFromIntError),
    #[error(transparent)]
    Io(#[from] io::Error),
}
