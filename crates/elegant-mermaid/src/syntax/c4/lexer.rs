use std::borrow::Cow;

use crate::source::{Span, cleaned::Cleaned};

pub const MODES: &[&str] = &[
    "INITIAL",
    "person",
    "person_ext",
    "system",
    "system_db",
    "system_queue",
    "system_ext",
    "system_ext_db",
    "system_ext_queue",
    "boundary",
    "enterprise_boundary",
    "system_boundary",
    "container",
    "container_db",
    "container_queue",
    "container_ext",
    "container_ext_db",
    "container_ext_queue",
    "container_boundary",
    "component",
    "component_db",
    "component_queue",
    "component_ext",
    "component_ext_db",
    "component_ext_queue",
    "rel",
    "birel",
    "rel_u",
    "rel_d",
    "rel_l",
    "rel_r",
    "rel_b",
    "rel_index",
    "node",
    "node_l",
    "node_r",
    "update_el_style",
    "update_rel_style",
    "update_layout_config",
    "attribute",
    "string",
    "string_kv",
    "string_kv_key",
    "string_kv_value",
    "acc_title",
    "acc_descr",
    "acc_descr_multiline",
    "index",
    "rel_bi",
];

pub const MACROS: &[(&str, &str, &str)] = &[
    ("Person_Ext", "PERSON_EXT", "person_ext"),
    ("Person", "PERSON", "person"),
    ("SystemQueue_Ext", "SYSTEM_EXT_QUEUE", "system_ext_queue"),
    ("SystemDb_Ext", "SYSTEM_EXT_DB", "system_ext_db"),
    ("System_Ext", "SYSTEM_EXT", "system_ext"),
    ("SystemQueue", "SYSTEM_QUEUE", "system_queue"),
    ("SystemDb", "SYSTEM_DB", "system_db"),
    ("System", "SYSTEM", "system"),
    ("Boundary", "BOUNDARY", "boundary"),
    (
        "Enterprise_Boundary",
        "ENTERPRISE_BOUNDARY",
        "enterprise_boundary",
    ),
    ("System_Boundary", "SYSTEM_BOUNDARY", "system_boundary"),
    (
        "ContainerQueue_Ext",
        "CONTAINER_EXT_QUEUE",
        "container_ext_queue",
    ),
    ("ContainerDb_Ext", "CONTAINER_EXT_DB", "container_ext_db"),
    ("Container_Ext", "CONTAINER_EXT", "container_ext"),
    ("ContainerQueue", "CONTAINER_QUEUE", "container_queue"),
    ("ContainerDb", "CONTAINER_DB", "container_db"),
    ("Container", "CONTAINER", "container"),
    (
        "Container_Boundary",
        "CONTAINER_BOUNDARY",
        "container_boundary",
    ),
    (
        "ComponentQueue_Ext",
        "COMPONENT_EXT_QUEUE",
        "component_ext_queue",
    ),
    ("ComponentDb_Ext", "COMPONENT_EXT_DB", "component_ext_db"),
    ("Component_Ext", "COMPONENT_EXT", "component_ext"),
    ("ComponentQueue", "COMPONENT_QUEUE", "component_queue"),
    ("ComponentDb", "COMPONENT_DB", "component_db"),
    ("Component", "COMPONENT", "component"),
    ("Deployment_Node", "NODE", "node"),
    ("Node", "NODE", "node"),
    ("Node_L", "NODE_L", "node_l"),
    ("Node_R", "NODE_R", "node_r"),
    ("Rel", "REL", "rel"),
    ("BiRel", "BIREL", "birel"),
    ("Rel_Up", "REL_U", "rel_u"),
    ("Rel_U", "REL_U", "rel_u"),
    ("Rel_Down", "REL_D", "rel_d"),
    ("Rel_D", "REL_D", "rel_d"),
    ("Rel_Left", "REL_L", "rel_l"),
    ("Rel_L", "REL_L", "rel_l"),
    ("Rel_Right", "REL_R", "rel_r"),
    ("Rel_R", "REL_R", "rel_r"),
    ("Rel_Back", "REL_B", "rel_b"),
    ("RelIndex", "REL_INDEX", "rel_index"),
    ("UpdateElementStyle", "UPDATE_EL_STYLE", "update_el_style"),
    ("UpdateRelStyle", "UPDATE_REL_STYLE", "update_rel_style"),
    (
        "UpdateLayoutConfig",
        "UPDATE_LAYOUT_CONFIG",
        "update_layout_config",
    ),
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: &'static str,
    pub text: Cow<'a, str>,
    pub span: Span,
}

pub fn lex<'a>(source: &'a str, removed: &[Span]) -> Vec<Token<'a>> {
    lex_cleaned(&Cleaned::new(source, removed))
}

pub(crate) fn lex_cleaned<'a>(cleaned: &Cleaned<'a>) -> Vec<Token<'a>> {
    Scanner {
        cleaned,
        source: cleaned.text(),
        at: 0,
        mode: "INITIAL",
        opening: None,
        argument: None,
        tokens: Vec::new(),
    }
    .run()
}

struct Scanner<'a, 't> {
    cleaned: &'t Cleaned<'a>,
    source: &'t str,
    at: usize,
    mode: &'static str,
    opening: Option<usize>,
    argument: Option<usize>,
    tokens: Vec<Token<'a>>,
}

impl<'a, 't> Scanner<'a, 't> {
    fn tail(&self) -> &'t str {
        self.source.get(self.at..).unwrap_or("")
    }
    fn push(&mut self, kind: &'static str, start: usize, end: usize, text: Cow<'a, str>) {
        self.tokens.push(Token {
            kind,
            text,
            span: self.cleaned.span(start, end.min(self.source.len())),
        });
    }
    fn emit(&mut self, kind: &'static str, length: usize, text: Cow<'a, str>) {
        self.push(kind, self.at, self.at + length, text);
        self.at = (self.at + length).min(self.source.len());
    }
    fn trimmed(&self, at: usize, s: &str) -> Cow<'a, str> {
        let lead = s.len() - s.trim_start().len();
        self.cleaned.cow(at + lead, at + lead + s.trim().len())
    }
    fn raw(&mut self, kind: &'static str, length: usize) {
        let end = (self.at + length).min(self.source.len());
        let text = self.cleaned.cow(self.at, end);
        self.emit(kind, length, text);
    }
    fn run(mut self) -> Vec<Token<'a>> {
        while self.at < self.source.len() {
            let before = (self.at, self.mode);
            self.next();
            if before == (self.at, self.mode) {
                self.raw(
                    "INVALID",
                    self.tail().chars().next().map_or(1, char::len_utf8),
                );
            }
        }
        self.finish();
        self.tokens
    }
    fn finish(&mut self) {
        if matches!(self.mode, "acc_title" | "acc_descr") {
            self.line_value();
        }
        if self.mode != "INITIAL" {
            let start = self.unclosed_start();
            let end = self.source.len();
            self.push("UNTERMINATED", start, end, self.cleaned.cow(start, end));
        }
        self.push("EOF", self.at, self.at, Cow::Borrowed(""));
    }
    fn unclosed_start(&self) -> usize {
        if self.mode == "acc_descr_multiline" {
            return self.opening.unwrap_or(self.at);
        }
        self.argument.or(self.opening).unwrap_or(self.at)
    }
    fn next(&mut self) {
        match self.mode {
            "INITIAL" => self.initial(),
            "attribute" => self.attribute(),
            "string" => self.quoted(),
            "string_kv" => self.named_key(),
            "string_kv_key" => self.named_equals(),
            "string_kv_value" => self.named_value(),
            "acc_title" | "acc_descr" => self.line_value(),
            "acc_descr_multiline" => self.description_block(),
            _ => self.call_open(),
        }
    }
    fn initial(&mut self) {
        let s = self.tail();
        let line = line_len(s);
        if let Some(kind) = direction(s.get(..line).unwrap_or("")) {
            self.raw(kind, line);
            return;
        }
        if self.metadata(s) || self.whitespace(s) || self.header(s) || self.macro_name(s) {
            return;
        }
        match s.chars().next() {
            Some('{') => self.raw("LBRACE", 1),
            Some('}') => self.raw("RBRACE", 1),
            _ => self.unknown(s),
        }
    }
    fn metadata(&mut self, s: &'t str) -> bool {
        for (name, kind) in [("title", "title"), ("accDescription", "accDescription")] {
            let Some(rest) = s.strip_prefix(name) else {
                continue;
            };
            if !rest.starts_with(char::is_whitespace) {
                continue;
            }
            let length = rest.find(['#', '\r', '\n', ';']).unwrap_or(rest.len());
            if length <= 1 {
                continue;
            }
            self.raw(kind, name.len() + length);
            return true;
        }
        self.accessibility(s)
    }
    fn accessibility(&mut self, s: &'t str) -> bool {
        for (name, mode) in [("accTitle", "acc_title"), ("accDescr", "acc_descr")] {
            let Some(rest) = s.strip_prefix(name) else {
                continue;
            };
            let tail = rest.trim_start_matches(char::is_whitespace);
            let prefix = s.len() - tail.len();
            if let Some(value) = tail.strip_prefix(':') {
                let ws = value.len() - value.trim_start_matches(char::is_whitespace).len();
                self.mode = mode;
                self.raw(mode, prefix + 1 + ws);
                return true;
            }
            if mode == "acc_descr" && tail.starts_with('{') {
                self.opening = Some(self.at + prefix);
                self.argument = Some(self.at);
                self.mode = "acc_descr_multiline";
                self.at += prefix + 1;
                return true;
            }
        }
        false
    }
    fn whitespace(&mut self, s: &str) -> bool {
        if s.starts_with("%%") {
            self.at += line_len(s);
            return true;
        }
        let length = s.len() - s.trim_start_matches(char::is_whitespace).len();
        if length == 0 {
            return false;
        }
        if s.get(..length).is_some_and(|s| s.contains(['\r', '\n'])) {
            self.raw("NEWLINE", length);
        } else {
            self.at += length;
        }
        true
    }
    fn header(&mut self, s: &str) -> bool {
        for (name, kind) in [
            ("C4Context", "C4_CONTEXT"),
            ("C4Container", "C4_CONTAINER"),
            ("C4Component", "C4_COMPONENT"),
            ("C4Dynamic", "C4_DYNAMIC"),
            ("C4Deployment", "C4_DEPLOYMENT"),
        ] {
            let Some(rest) = s.strip_prefix(name) else {
                continue;
            };
            if rest
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_'))
            {
                continue;
            }
            self.raw(kind, name.len());
            return true;
        }
        false
    }
    fn macro_name(&mut self, s: &str) -> bool {
        for &(name, kind, mode) in MACROS {
            let Some(rest) = s.strip_prefix(name) else {
                continue;
            };
            if !rest
                .trim_start_matches(char::is_whitespace)
                .starts_with('(')
            {
                continue;
            }
            self.mode = mode;
            self.raw(kind, name.len());
            return true;
        }
        false
    }
    fn unknown(&mut self, s: &str) {
        let length = s
            .find(|c: char| c.is_whitespace() || matches!(c, '{' | '}'))
            .unwrap_or(s.len());
        self.raw(
            "INVALID",
            length.max(s.chars().next().map_or(1, char::len_utf8)),
        );
    }
    fn call_open(&mut self) {
        let s = self.tail();
        let ws = s.len() - s.trim_start_matches(char::is_whitespace).len();
        if ws > 0 {
            self.at += ws;
            return;
        }
        if !s.starts_with('(') {
            return;
        }
        self.opening = Some(self.at);
        self.raw("LPAREN", 1);
        self.mode = "attribute";
        let s = self.tail();
        let spaces = s.bytes().take_while(|b| *b == b' ').count();
        if s.get(spaces..).is_some_and(|s| s.starts_with(',')) {
            self.raw("ATTRIBUTE_EMPTY", spaces + 1);
        }
    }
    fn attribute(&mut self) {
        let s = self.tail();
        if s.starts_with(')') {
            self.raw("RPAREN", 1);
            self.mode = "INITIAL";
            self.opening = None;
            return;
        }
        if s.starts_with(",,") {
            self.raw("ATTRIBUTE_EMPTY", 2);
            return;
        }
        if s.starts_with(',') {
            self.at += 1;
            return;
        }
        let spaces = s.bytes().take_while(|b| *b == b' ').count();
        let rest = s.get(spaces..).unwrap_or("");
        if rest.starts_with("\"\"") {
            self.raw("ATTRIBUTE_EMPTY", spaces + 2);
            return;
        }
        self.attribute_text(rest, spaces);
    }
    fn attribute_text(&mut self, rest: &'t str, spaces: usize) {
        let mode = match rest.chars().next() {
            Some('"') => "string",
            Some('$') => "string_kv",
            _ => {
                let s = self.tail();
                let length = s.find(',').unwrap_or(s.len());
                self.emit(
                    "STR",
                    length,
                    self.trimmed(self.at, s.get(..length).unwrap_or("")),
                );
                return;
            }
        };
        self.argument = Some(self.at + spaces);
        self.at += spaces + 1;
        self.mode = mode;
    }
    fn quoted(&mut self) {
        let s = self.tail();
        let Some(length) = s.find('"') else {
            self.at += s.len();
            return;
        };
        let start = self.argument.take().unwrap_or(self.at);
        self.push(
            "STR",
            start,
            self.at + length + 1,
            self.trimmed(self.at, s.get(..length).unwrap_or("")),
        );
        self.at += length + 1;
        self.mode = "attribute";
    }
    fn named_key(&mut self) {
        let s = self.tail();
        let Some(length) = s.find('=') else {
            self.at += s.len();
            return;
        };
        let start = self.argument.unwrap_or(self.at);
        self.push(
            "STR_KEY",
            start,
            self.at + length,
            self.trimmed(self.at, s.get(..length).unwrap_or("")),
        );
        self.at += length;
        self.mode = "string_kv_key";
    }
    fn named_equals(&mut self) {
        let s = self.tail();
        let Some(rest) = s.strip_prefix('=') else {
            return;
        };
        let spaces = rest.bytes().take_while(|b| *b == b' ').count();
        if !rest.get(spaces..).is_some_and(|s| s.starts_with('"')) {
            return;
        }
        self.at += spaces + 2;
        self.mode = "string_kv_value";
    }
    fn named_value(&mut self) {
        let s = self.tail();
        let Some(length) = s.find('"') else {
            self.at += s.len();
            return;
        };
        if length > 0 {
            self.emit(
                "STR_VALUE",
                length + 1,
                self.trimmed(self.at, s.get(..length).unwrap_or("")),
            );
        } else {
            self.at += 1;
        }
        self.argument = None;
        self.mode = "attribute";
    }
    fn line_value(&mut self) {
        let s = self.tail();
        let kind = if self.mode == "acc_title" {
            "acc_title_value"
        } else {
            "acc_descr_value"
        };
        self.emit(
            kind,
            line_len(s),
            self.trimmed(self.at, s.get(..line_len(s)).unwrap_or("")),
        );
        self.mode = "INITIAL";
    }
    fn description_block(&mut self) {
        let s = self.tail();
        let Some(length) = s.find('}') else {
            self.at += s.len();
            return;
        };
        let start = self.argument.take().unwrap_or(self.at);
        self.push(
            "acc_descr_multiline_value",
            start,
            self.at + length + 1,
            self.trimmed(self.at, s.get(..length).unwrap_or("")),
        );
        self.at += length + 1;
        self.opening = None;
        self.mode = "INITIAL";
    }
}

fn line_len(s: &str) -> usize {
    s.find(['\r', '\n']).unwrap_or(s.len())
}
fn direction(s: &str) -> Option<&'static str> {
    for (axis, kind) in [
        ("TB", "direction_tb"),
        ("BT", "direction_bt"),
        ("RL", "direction_rl"),
        ("LR", "direction_lr"),
    ] {
        for (at, _) in s.match_indices("direction") {
            let rest = s.get(at + 9..).unwrap_or("");
            let value = rest.trim_start_matches(char::is_whitespace);
            if value.len() < rest.len() && value.starts_with(axis) {
                return Some(kind);
            }
        }
    }
    None
}
