use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

pub use crate::diag::FixSafety;
use crate::diag::Severity;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixOutcome {
    pub text: String,
    pub applied: usize,
}

pub const DEFAULT_THEME: &str = "elegant-light";
pub const DEFAULT_THOROUGHNESS: u8 = 3;
pub const MIN_THOROUGHNESS: u8 = 1;
pub const MAX_THOROUGHNESS: u8 = 5;
pub const DEFAULT_MAX_NODES: u32 = 2000;
pub const DEFAULT_MAX_EDGES: u32 = 5000;
pub const DEFAULT_MAX_TEXT_BYTES: u32 = 1_048_576;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LintConfig {
    pub select: Vec<String>,
    pub ignore: Vec<String>,
    pub severity: BTreeMap<String, Severity>,
    pub off: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Profile {
    #[default]
    Vector,
    Cell,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    pub max_nodes: u32,
    pub max_edges: u32,
    pub max_text_bytes: u32,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            max_nodes: DEFAULT_MAX_NODES,
            max_edges: DEFAULT_MAX_EDGES,
            max_text_bytes: DEFAULT_MAX_TEXT_BYTES,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Cancel(Option<Arc<AtomicBool>>);

impl Cancel {
    pub fn new() -> Cancel {
        Cancel(Some(Arc::new(AtomicBool::new(false))))
    }

    pub fn cancel(&self) {
        if let Some(flag) = &self.0 {
            flag.store(true, Ordering::SeqCst);
        }
    }

    pub fn is_cancelled(&self) -> bool {
        match &self.0 {
            Some(flag) => flag.load(Ordering::SeqCst),
            None => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LayoutOptions {
    pub profile: Profile,
    pub theme: String,
    pub thoroughness: u8,
    pub max_width: u32,
    pub limits: Limits,
    pub config: Option<String>,
    pub cancel: Cancel,
}

impl Default for LayoutOptions {
    fn default() -> LayoutOptions {
        LayoutOptions {
            profile: Profile::Vector,
            theme: DEFAULT_THEME.to_owned(),
            thoroughness: DEFAULT_THOROUGHNESS,
            max_width: 0,
            limits: Limits::default(),
            config: None,
            cancel: Cancel::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TextMode {
    #[default]
    Font,
    Paths,
}

#[derive(Debug, Clone, Default)]
pub struct SvgOptions {
    pub layout: LayoutOptions,
    pub background: String,
    pub text: TextMode,
    pub id_prefix: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Charset {
    #[default]
    Unicode,
    Ascii,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ColorMode {
    #[default]
    None,
    Ansi16,
    Ansi256,
    Truecolor,
}

#[derive(Debug, Clone, Default)]
pub struct TextOptions {
    pub layout: LayoutOptions,
    pub charset: Charset,
    pub color: ColorMode,
}

#[cfg(test)]
mod tests {
    use super::{
        Cancel, Charset, ColorMode, LayoutOptions, Limits, LintConfig, Profile, SvgOptions,
        TextMode, TextOptions,
    };

    const EXPECTED_LIMITS: (u32, u32, u32) = (2000, 5000, 1_048_576);

    #[test]
    fn layout_options_defaults_are_house_defaults() {
        let options = LayoutOptions::default();
        assert_eq!(options.profile, Profile::Vector);
        assert_eq!(options.theme, "elegant-light");
        assert_eq!(options.thoroughness, 3);
        assert_eq!(options.max_width, 0);
        assert!(options.config.is_none());
        assert!(!options.cancel.is_cancelled());
    }

    #[test]
    fn limits_defaults_match_the_spec() {
        let limits = Limits::default();
        let got = (limits.max_nodes, limits.max_edges, limits.max_text_bytes);
        assert_eq!(got, EXPECTED_LIMITS);
    }

    #[test]
    fn text_options_defaults() {
        let text = TextOptions::default();
        assert_eq!(text.charset, Charset::Unicode);
        assert_eq!(text.color, ColorMode::None);
        assert_eq!(text.layout.theme, "elegant-light");
    }

    #[test]
    fn svg_options_defaults() {
        let svg = SvgOptions::default();
        assert_eq!(svg.background, "");
        assert_eq!(svg.text, TextMode::Font);
        assert_eq!(svg.id_prefix, "");
        assert_eq!(svg.layout.profile, Profile::Vector);
    }

    #[test]
    fn lint_config_default_is_empty() {
        let config = LintConfig::default();
        assert!(config.select.is_empty());
        assert!(config.ignore.is_empty());
        assert!(config.severity.is_empty());
        assert!(config.off.is_empty());
    }

    #[test]
    fn cancel_clones_share_one_flag() {
        let first = Cancel::new();
        let second = first.clone();
        assert!(!first.is_cancelled());
        assert!(!second.is_cancelled());
        second.cancel();
        assert!(first.is_cancelled());
        assert!(second.is_cancelled());
    }

    #[test]
    fn default_cancel_never_fires() {
        let cancel = Cancel::default();
        assert!(!cancel.is_cancelled());
        cancel.cancel();
        assert!(!cancel.is_cancelled());
    }

    #[test]
    fn separate_cancel_instances_are_independent() {
        let fired = Cancel::new();
        let quiet = Cancel::new();
        fired.cancel();
        assert!(fired.is_cancelled());
        assert!(!quiet.is_cancelled());
    }

    #[test]
    fn cancel_is_usable_across_threads() {
        let cancel = Cancel::new();
        let worker = cancel.clone();
        let handle = std::thread::spawn(move || worker.cancel());
        let joined = handle.join();
        assert!(joined.is_ok());
        assert!(cancel.is_cancelled());
    }

    #[test]
    fn severity_override_map_orders_by_code() {
        let mut config = LintConfig::default();
        config
            .severity
            .insert("flowchart/b".to_owned(), crate::diag::Severity::Warning);
        config
            .severity
            .insert("flowchart/a".to_owned(), crate::diag::Severity::Error);
        let codes: Vec<&str> = config.severity.keys().map(String::as_str).collect();
        assert_eq!(codes, ["flowchart/a", "flowchart/b"]);
    }
}
