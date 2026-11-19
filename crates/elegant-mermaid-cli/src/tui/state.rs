pub const DEFAULT_THEME: &str = "elegant-light";
pub const BUILTIN_THEMES: [&str; 9] = [
    "elegant-light",
    "elegant-dark",
    "github-light",
    "github-dark",
    "catppuccin-latte",
    "catppuccin-mocha",
    "nord",
    "solarized-light",
    "solarized-dark",
];
pub const MIN_ZOOM: usize = 10;
pub const MAX_ZOOM: usize = 800;
pub const MIN_WIDTH: usize = 20;
pub const MIN_HEIGHT: usize = 5;
pub const DEFAULT_CELL_W: usize = 8;
pub const DEFAULT_CELL_H: usize = 16;
pub const EMPTY_MESSAGE: &str =
    "Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes";
pub const UNKNOWN_KIND_CODE: &str = "common/unknown-diagram-kind";
pub const EMPTY_SOURCE_CODE: &str = "common/empty-source";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Mode {
    #[default]
    Cells,
    Kitty,
    Iterm,
    Sixel,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::Cells => "cells",
            Mode::Kitty => "kitty",
            Mode::Iterm => "iterm",
            Mode::Sixel => "sixel",
        }
    }

    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "cells" => Some(Mode::Cells),
            "kitty" => Some(Mode::Kitty),
            "iterm" => Some(Mode::Iterm),
            "sixel" => Some(Mode::Sixel),
            _ => None,
        }
    }

    pub fn is_pixel(self) -> bool {
        !matches!(self, Mode::Cells)
    }

    pub fn next(self) -> Self {
        match self {
            Mode::Cells => Mode::Kitty,
            Mode::Kitty => Mode::Iterm,
            Mode::Iterm => Mode::Sixel,
            Mode::Sixel => Mode::Cells,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Charset {
    #[default]
    Unicode,
    Ascii,
}

impl Charset {
    pub fn toggled(self) -> Self {
        match self {
            Charset::Unicode => Charset::Ascii,
            Charset::Ascii => Charset::Unicode,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Options {
    pub theme: String,
    pub charset: Charset,
}

impl Options {
    pub fn new(theme: &str) -> Self {
        Self {
            theme: theme.to_string(),
            charset: Charset::Unicode,
        }
    }
}

pub fn next_theme(current: &str) -> &'static str {
    match BUILTIN_THEMES.iter().position(|name| *name == current) {
        Some(index) => BUILTIN_THEMES[(index + 1) % BUILTIN_THEMES.len()],
        None => BUILTIN_THEMES[0],
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Panel {
    #[default]
    None,
    Diagnostics,
    Keys,
}

impl Panel {
    pub fn title(self) -> &'static str {
        match self {
            Panel::None => "",
            Panel::Diagnostics => "Diagnostics",
            Panel::Keys => "Keys",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Severity {
    #[default]
    Error,
    Warning,
    Info,
}

impl Severity {
    pub fn name(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        }
    }
}

pub fn format_diagnostic(
    severity: Severity,
    code: &str,
    line: u32,
    column: u32,
    message: &str,
) -> String {
    format!(
        "{} {} {}:{} {}",
        severity.name(),
        code,
        line,
        column,
        message
    )
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum PanDir {
    #[default]
    Left,
    Down,
    Up,
    Right,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Key {
    #[default]
    None,
    Left,
    Down,
    Up,
    Right,
    ZoomIn,
    ZoomOut,
    Fit,
    NextBlock,
    PrevBlock,
    Theme,
    Charset,
    Graphics,
    Diagnostics,
    Keys,
    Reload,
    Escape,
    Quit,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KeyEffect {
    pub edited: bool,
    pub quit: bool,
}

impl KeyEffect {
    const IDLE: Self = Self {
        edited: false,
        quit: false,
    };
    const EDITED: Self = Self {
        edited: true,
        quit: false,
    };
    const QUIT: Self = Self {
        edited: false,
        quit: true,
    };
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ViewState {
    pub path: String,
    pub width: usize,
    pub height: usize,
    pub kind: Option<String>,
    pub block: Option<(u32, u32)>,
    pub mode: Mode,
    pub fit: bool,
    pub zoom: usize,
    pub errors: u32,
    pub warnings: u32,
    pub empty: bool,
    pub displayed: u64,
    pub frame_rev: u64,
    pub panel: Panel,
    pub auto_panel: bool,
    pub diagnostics: Vec<String>,
    pub watch_lost: bool,
    pub text: Vec<String>,
    pub content_w: usize,
    pub content_h: usize,
    pub offset_x: usize,
    pub offset_y: usize,
    pub src_w: usize,
    pub src_h: usize,
    pub cell_w: usize,
    pub cell_h: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FrameData {
    pub text: Vec<String>,
    pub content_w: usize,
    pub content_h: usize,
    pub src_w: usize,
    pub src_h: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionResult {
    pub number: u64,
    pub kind: Option<String>,
    pub block: Option<(u32, u32)>,
    pub errors: u32,
    pub warnings: u32,
    pub empty: bool,
    pub diagnostics: Vec<String>,
    pub frame: Option<FrameData>,
    pub error_codes: Vec<String>,
}

impl RevisionResult {
    pub fn new(number: u64) -> Self {
        Self {
            number,
            kind: None,
            block: None,
            errors: 0,
            warnings: 0,
            empty: false,
            diagnostics: Vec::new(),
            frame: None,
            error_codes: Vec::new(),
        }
    }

    pub fn has_error(&self) -> bool {
        self.errors > 0
    }

    pub fn has_error_other_than_empty_source(&self) -> bool {
        self.has_error() && (!self.empty || self.errors > 1)
    }

    pub fn has_unknown_kind(&self) -> bool {
        self.error_codes
            .iter()
            .any(|code| code == UNKNOWN_KIND_CODE)
    }
}

impl ViewState {
    pub fn new(path: &str, width: usize, height: usize, mode: Mode) -> Self {
        Self {
            path: path.to_string(),
            width,
            height,
            mode,
            fit: mode.is_pixel(),
            cell_w: DEFAULT_CELL_W,
            cell_h: DEFAULT_CELL_H,
            ..Self::default()
        }
    }

    pub fn viewport_rows(&self) -> usize {
        self.height.saturating_sub(2)
    }

    pub fn cell_width(&self) -> usize {
        if self.cell_w == 0 {
            DEFAULT_CELL_W
        } else {
            self.cell_w
        }
    }

    pub fn cell_height(&self) -> usize {
        if self.cell_h == 0 {
            DEFAULT_CELL_H
        } else {
            self.cell_h
        }
    }

    pub fn viewport_pixel_width(&self) -> usize {
        self.width.saturating_mul(self.cell_width())
    }

    pub fn viewport_pixel_height(&self) -> usize {
        self.viewport_rows().saturating_mul(self.cell_height())
    }

    pub fn scaled_width(&self) -> usize {
        scaled_size(self.src_w, self.zoom)
    }

    pub fn scaled_height(&self) -> usize {
        scaled_size(self.src_h, self.zoom)
    }

    pub fn fit_to_screen(mut self) -> Self {
        self.fit = true;
        self.zoom = fit_zoom(
            self.src_w,
            self.src_h,
            self.viewport_pixel_width(),
            self.viewport_pixel_height(),
        );
        self.offset_x = 0;
        self.offset_y = 0;
        self
    }

    pub fn zoom_in(mut self) -> Self {
        if !self.mode.is_pixel() {
            return self;
        }
        self.fit = false;
        self.zoom = clamp_zoom(self.zoom.saturating_mul(5) / 4);
        self.clamp_offsets()
    }

    pub fn zoom_out(mut self) -> Self {
        if !self.mode.is_pixel() {
            return self;
        }
        self.fit = false;
        self.zoom = clamp_zoom(self.zoom.saturating_mul(4) / 5);
        self.clamp_offsets()
    }

    pub fn pan(mut self, dir: PanDir) -> Self {
        if self.mode.is_pixel() {
            let dx = self.cell_width();
            let dy = self.cell_height();
            match dir {
                PanDir::Left => self.offset_x = self.offset_x.saturating_sub(dx),
                PanDir::Right => self.offset_x = self.offset_x.saturating_add(dx),
                PanDir::Up => self.offset_y = self.offset_y.saturating_sub(dy),
                PanDir::Down => self.offset_y = self.offset_y.saturating_add(dy),
            }
            return self.clamp_offsets();
        }
        match dir {
            PanDir::Left => self.offset_x = self.offset_x.saturating_sub(1),
            PanDir::Right => self.offset_x = self.offset_x.saturating_add(1),
            PanDir::Up => self.offset_y = self.offset_y.saturating_sub(1),
            PanDir::Down => self.offset_y = self.offset_y.saturating_add(1),
        }
        self.clamp_cell_offsets()
    }

    pub fn clamp_offsets(mut self) -> Self {
        let max_x = max_offset(self.scaled_width(), self.viewport_pixel_width());
        let max_y = max_offset(self.scaled_height(), self.viewport_pixel_height());
        self.offset_x = self.offset_x.min(max_x);
        self.offset_y = self.offset_y.min(max_y);
        self
    }

    pub fn clamp_cell_offsets(mut self) -> Self {
        let max_x = self.content_w.saturating_sub(self.width);
        let max_y = self.content_h.saturating_sub(self.viewport_rows());
        self.offset_x = self.offset_x.min(max_x);
        self.offset_y = self.offset_y.min(max_y);
        self
    }

    pub fn home(mut self) -> Self {
        if self.mode.is_pixel() {
            return self.fit_to_screen();
        }
        self.offset_x = 0;
        self.offset_y = 0;
        self
    }

    pub fn next_block(mut self) -> Self {
        let Some((index, count)) = self.block else {
            return self;
        };
        if count == 0 {
            return self;
        }
        let next = if index >= count { 1 } else { index + 1 };
        self.block = Some((next, count));
        self
    }

    pub fn prev_block(mut self) -> Self {
        let Some((index, count)) = self.block else {
            return self;
        };
        if count == 0 {
            return self;
        }
        let next = if index <= 1 { count } else { index - 1 };
        self.block = Some((next, count));
        self
    }

    pub fn toggle_panel(mut self, panel: Panel) -> Self {
        if self.panel == panel {
            self.panel = Panel::None;
            self.auto_panel = false;
            return self;
        }
        self.panel = panel;
        self.auto_panel = false;
        self
    }

    pub fn close_panel(mut self) -> Self {
        if self.panel == Panel::None {
            return self;
        }
        self.panel = Panel::None;
        self.auto_panel = false;
        self
    }

    pub fn key(mut self, key: Key, options: &mut Options) -> (Self, KeyEffect) {
        match key {
            Key::Left => (self.pan(PanDir::Left), KeyEffect::IDLE),
            Key::Down => (self.pan(PanDir::Down), KeyEffect::IDLE),
            Key::Up => (self.pan(PanDir::Up), KeyEffect::IDLE),
            Key::Right => (self.pan(PanDir::Right), KeyEffect::IDLE),
            Key::ZoomIn => (self.zoom_in(), KeyEffect::IDLE),
            Key::ZoomOut => (self.zoom_out(), KeyEffect::IDLE),
            Key::Fit => (self.home(), KeyEffect::IDLE),
            Key::NextBlock => (self.next_block(), KeyEffect::EDITED),
            Key::PrevBlock => (self.prev_block(), KeyEffect::EDITED),
            Key::Theme => {
                options.theme = next_theme(&options.theme).to_string();
                (self, KeyEffect::EDITED)
            }
            Key::Charset => {
                options.charset = options.charset.toggled();
                (self, KeyEffect::EDITED)
            }
            Key::Graphics => {
                self.mode = self.mode.next();
                if self.mode.is_pixel() {
                    self = self.fit_to_screen();
                }
                (self, KeyEffect::EDITED)
            }
            Key::Diagnostics => (self.toggle_panel(Panel::Diagnostics), KeyEffect::IDLE),
            Key::Keys => (self.toggle_panel(Panel::Keys), KeyEffect::IDLE),
            Key::Reload => (self, KeyEffect::EDITED),
            Key::Escape => (self.close_panel(), KeyEffect::IDLE),
            Key::Quit => (self, KeyEffect::QUIT),
            Key::None => (self, KeyEffect::IDLE),
        }
    }

    pub fn resize(mut self, width: usize, height: usize) -> Self {
        let old_vw = self.viewport_pixel_width();
        let old_vh = self.viewport_pixel_height();
        let old_w = self.width;
        let old_rows = self.viewport_rows();
        self.width = width;
        self.height = height;
        if self.mode.is_pixel() {
            self.offset_x = shift_offset(self.offset_x, old_vw, self.viewport_pixel_width());
            self.offset_y = shift_offset(self.offset_y, old_vh, self.viewport_pixel_height());
            if self.fit {
                return self.fit_to_screen();
            }
            return self.clamp_offsets();
        }
        self.offset_x = shift_offset(self.offset_x, old_w, width);
        self.offset_y = shift_offset(self.offset_y, old_rows, self.viewport_rows());
        self.clamp_cell_offsets()
    }

    pub fn size_text(&self) -> String {
        let (columns, lines) = self.size_cells();
        format!("{columns}x{lines} cells")
    }

    pub fn size_cells(&self) -> (usize, usize) {
        if self.mode.is_pixel() {
            let cw = self.cell_width();
            let ch = self.cell_height();
            (
                ceil_div(self.scaled_width(), cw),
                ceil_div(self.scaled_height(), ch),
            )
        } else {
            (self.content_w, self.content_h)
        }
    }

    pub fn larger_than_viewport(&self) -> bool {
        if self.mode.is_pixel() {
            return self.scaled_width() > self.viewport_pixel_width()
                || self.scaled_height() > self.viewport_pixel_height();
        }
        self.content_w > self.width || self.content_h > self.viewport_rows()
    }

    pub fn zoom_text(&self) -> String {
        if !self.mode.is_pixel() {
            return String::from("-");
        }
        if self.fit {
            return String::from("fit");
        }
        format!("{}%", self.zoom)
    }

    pub fn kind_text(&self) -> String {
        if self.displayed == 0 || self.empty {
            return String::from("-");
        }
        let Some(kind) = &self.kind else {
            return String::from("-");
        };
        match self.block {
            Some((index, count)) => format!("{kind} {index}/{count}"),
            None => kind.clone(),
        }
    }

    pub fn message_parts(&self) -> Vec<String> {
        let mut parts = Vec::new();
        if self.watch_lost {
            parts.push(format!("WATCH LOST: recreate {}; retrying", self.path));
        }
        if self.displayed != 0 && self.errors > 0 {
            if self.frame_rev == 0 {
                parts.push(String::from(
                    "No valid revision yet; fix the source or press r",
                ));
            } else {
                parts.push(format!(
                    "STALE revision {}; latest revision {} has errors",
                    self.frame_rev, self.displayed
                ));
            }
        }
        if self.larger_than_viewport() {
            parts.push(format!("{}; pan available", self.size_text()));
        }
        parts
    }

    pub fn message_text(&self) -> String {
        self.message_parts().join(" | ")
    }

    pub fn status_parts(&self) -> Vec<String> {
        let mut parts = Vec::new();
        let message = self.message_text();
        if !message.is_empty() {
            parts.push(message);
        }
        parts.push(self.kind_text());
        parts.push(String::from(self.mode.name()));
        parts.push(self.zoom_text());
        parts.push(format!(
            "E {} errors W {} warnings",
            self.errors, self.warnings
        ));
        if self.displayed == 0 {
            parts.push(String::from("REV -"));
        } else {
            parts.push(format!("REV {}", self.displayed));
        }
        parts
    }

    pub fn status_rest(&self) -> String {
        self.status_parts().join(" | ")
    }

    pub fn display(&mut self, result: &RevisionResult) {
        self.displayed = result.number;
        self.errors = result.errors;
        self.warnings = result.warnings;
        self.diagnostics = result.diagnostics.clone();
        self.kind = result.kind.clone();
        self.block = result.block;
        self.empty = result.empty;
        match &result.frame {
            Some(frame) => self.apply_frame(result.number, frame),
            None => self.apply_missing_frame(result),
        }
    }

    fn apply_frame(&mut self, number: u64, frame: &FrameData) {
        self.text = frame.text.clone();
        self.content_w = frame.content_w;
        self.content_h = frame.content_h;
        self.src_w = frame.src_w;
        self.src_h = frame.src_h;
        self.frame_rev = number;
        if self.fit {
            self.zoom = fit_zoom(
                self.src_w,
                self.src_h,
                self.viewport_pixel_width(),
                self.viewport_pixel_height(),
            );
        }
        let clamped = if self.mode.is_pixel() {
            self.clone().clamp_offsets()
        } else {
            self.clone().clamp_cell_offsets()
        };
        self.offset_x = clamped.offset_x;
        self.offset_y = clamped.offset_y;
        if self.auto_panel {
            self.panel = Panel::None;
            self.auto_panel = false;
        }
    }

    fn apply_missing_frame(&mut self, result: &RevisionResult) {
        if self.watch_lost {
            return;
        }
        let auto = result.has_unknown_kind()
            || (self.frame_rev == 0 && result.has_error_other_than_empty_source());
        if auto {
            self.panel = Panel::Diagnostics;
            self.auto_panel = true;
        }
    }
}

pub fn fit_zoom(src_w: usize, src_h: usize, view_w: usize, view_h: usize) -> usize {
    if src_w == 0 || src_h == 0 {
        return MIN_ZOOM;
    }
    let horizontal = view_w.saturating_mul(100) / src_w;
    let vertical = view_h.saturating_mul(100) / src_h;
    clamp_zoom(horizontal.min(vertical))
}

pub fn clamp_zoom(zoom: usize) -> usize {
    zoom.clamp(MIN_ZOOM, MAX_ZOOM)
}

pub fn scaled_size(src: usize, zoom: usize) -> usize {
    if zoom == 0 || src == 0 {
        return 0;
    }
    src.saturating_mul(zoom).saturating_add(99) / 100
}

pub fn max_offset(scaled: usize, viewport: usize) -> usize {
    scaled.saturating_sub(viewport)
}

pub fn origin_offset(scaled: usize, viewport: usize) -> usize {
    viewport.saturating_sub(scaled) / 2
}

pub fn ceil_div(value: usize, divisor: usize) -> usize {
    if divisor == 0 {
        return 0;
    }
    value.saturating_add(divisor - 1) / divisor
}

fn shift_offset(offset: usize, old_span: usize, new_span: usize) -> usize {
    let shifted = offset.saturating_add(old_span / 2);
    shifted.saturating_sub(new_span / 2)
}

#[cfg(test)]
#[path = "state_tests.rs"]
mod tests;
