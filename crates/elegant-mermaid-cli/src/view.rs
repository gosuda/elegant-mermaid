use crate::error::{ReplayError, UsageError, ViewError};
use crate::termgfx;
use crate::tui::{
    frame::frame,
    scheduler::{self, Command, Event, SchedulerState},
    state::*,
};
use crate::{input, paths};
use crossterm::terminal;
use elegant_mermaid::{self as mermaid, Cancel};
use notify::Watcher;
use quanta::Instant;
use std::{
    fs,
    io::{self, IsTerminal, Read, Write},
    num::TryFromIntError,
    path::Path,
    sync::mpsc,
    time::Duration,
};

pub struct Environment {
    pub colorfgbg: String,
    pub kitty_window_id: String,
    pub term: String,
    pub term_program: String,
    pub auto_colour: bool,
    pub depth: mermaid::cells::ColorMode,
}

struct Image {
    width: usize,
    height: usize,
    data: Vec<u8>,
}
struct ResultFrame {
    revision: RevisionResult,
    image: Option<Image>,
}
struct Viewer {
    state: ViewState,
    options: Options,
    source: Vec<u8>,
    image: Option<Image>,
    scheduler: SchedulerState,
    colour: bool,
    depth: mermaid::cells::ColorMode,
}
impl Viewer {
    fn edited(&mut self) {
        self.scheduler = scheduler::step(self.scheduler, Event::Edited).0;
        debug_assert!(
            self.scheduler.invariants_hold(),
            "Edited violated scheduler invariants: {:?}",
            self.scheduler
        );
    }
    fn display(&mut self, result: ResultFrame) {
        self.state.display(&result.revision);
        if result.image.is_some() {
            self.image = result.image;
        }
    }
    fn settle(&mut self) -> Result<(), TryFromIntError> {
        while self.scheduler.inflight != 0 {
            if self.scheduler.cancelled {
                self.scheduler = scheduler::step(self.scheduler, Event::RenderAborted).0;
                continue;
            }
            let result = render(
                &self.source,
                &self.state,
                &self.options,
                self.scheduler.inflight,
                Cancel::default(),
            )?;
            self.scheduler = scheduler::step(self.scheduler, Event::RenderDone).0;
            self.display(result);
        }
        Ok(())
    }
    fn key(&mut self, name: &str, reload: bool) -> bool {
        if matches!(name, "n" | "p") && self.state.block.is_none() {
            return false;
        }
        if name == "r" && reload {
            match fs::read(&self.state.path) {
                Ok(bytes) => {
                    self.source = bytes;
                    self.state.watch_lost = false;
                }
                Err(_) => self.state.watch_lost = true,
            }
        }
        let (state, effect) = std::mem::take(&mut self.state).key(key(name), &mut self.options);
        self.state = state;
        if effect.edited {
            self.edited();
        }
        effect.quit
    }
}
fn key(name: &str) -> Key {
    match name {
        "left" | "h" => Key::Left,
        "down" | "j" => Key::Down,
        "up" | "k" => Key::Up,
        "right" | "l" => Key::Right,
        "+" => Key::ZoomIn,
        "-" => Key::ZoomOut,
        "0" => Key::Fit,
        "n" => Key::NextBlock,
        "p" => Key::PrevBlock,
        "t" => Key::Theme,
        "c" => Key::Charset,
        "g" => Key::Graphics,
        "d" => Key::Diagnostics,
        "?" => Key::Keys,
        "r" => Key::Reload,
        "esc" => Key::Escape,
        "q" | "ctrl-c" => Key::Quit,
        _ => Key::None,
    }
}
fn render(
    source: &[u8],
    state: &ViewState,
    options: &Options,
    number: u64,
    cancel: Cancel,
) -> Result<ResultFrame, TryFromIntError> {
    if cancel.is_cancelled() {
        return Ok(ResultFrame {
            revision: RevisionResult::new(number),
            image: None,
        });
    }
    let blocks = mermaid::markdown::blocks(source);
    let markdown = Path::new(&state.path)
        .extension()
        .is_some_and(|extension| matches!(extension.to_str(), Some("md" | "markdown" | "mdx")));
    if markdown && blocks.is_empty() {
        return Ok(ResultFrame {
            revision: RevisionResult {
                errors: 1,
                diagnostics: vec![format!(
                    "no Mermaid blocks found in {}; add a fenced code block labelled mermaid",
                    state.path
                )],
                ..RevisionResult::new(number)
            },
            image: None,
        });
    }
    let selected = usize::try_from(state.block.map_or(1, |block| block.0).max(1))?;
    let (bytes, block) = if markdown {
        let index = selected.min(blocks.len());
        let block = (u32::try_from(index)?, u32::try_from(blocks.len())?);
        (blocks[index - 1].source.as_ref(), Some(block))
    } else {
        (source, None)
    };
    let document = mermaid::parse_bytes(bytes);
    let revision = diagnose_revision(&document, number, block)?;
    if revision.errors != 0 {
        return Ok(ResultFrame {
            revision,
            image: None,
        });
    }
    match render_content(&document, options, state.mode, cancel) {
        Ok((frame, image)) => Ok(ResultFrame {
            revision: RevisionResult {
                frame: Some(frame),
                ..revision
            },
            image,
        }),
        Err(error) => Ok(ResultFrame {
            revision: RevisionResult {
                errors: revision.errors + 1,
                diagnostics: revision
                    .diagnostics
                    .into_iter()
                    .chain(std::iter::once(error.to_string()))
                    .collect(),
                ..revision
            },
            image: None,
        }),
    }
}

fn diagnose_revision(
    document: &mermaid::Document<'_>,
    number: u64,
    block: Option<(u32, u32)>,
) -> Result<RevisionResult, TryFromIntError> {
    let initial = RevisionResult {
        kind: Some(document.kind().map_or("unknown", |kind| kind.id()).into()),
        block,
        ..RevisionResult::new(number)
    };
    document
        .diagnostics()
        .iter()
        .try_fold(initial, |mut revision, diagnostic| {
            let position = document.position(diagnostic.span.start);
            let severity = match diagnostic.severity {
                mermaid::Severity::Error => {
                    revision.errors += 1;
                    revision.error_codes.push(diagnostic.code.into());
                    Severity::Error
                }
                mermaid::Severity::Warning => {
                    revision.warnings += 1;
                    Severity::Warning
                }
                mermaid::Severity::Info => Severity::Info,
            };
            revision.empty |= diagnostic.code == EMPTY_SOURCE_CODE;
            revision.diagnostics.push(format_diagnostic(
                severity,
                diagnostic.code,
                u32::try_from(position.line)?,
                u32::try_from(position.column)?,
                &diagnostic.message,
            ));
            Ok(revision)
        })
}
fn render_content(
    document: &mermaid::Document<'_>,
    options: &Options,
    mode: Mode,
    cancel: Cancel,
) -> Result<(FrameData, Option<Image>), ViewError> {
    let layout = mermaid::LayoutOptions {
        theme: options.theme.clone(),
        cancel,
        ..Default::default()
    };
    let text = mermaid::render_text(
        document,
        &mermaid::TextOptions {
            layout: layout.clone(),
            charset: if options.charset == Charset::Ascii {
                mermaid::Charset::Ascii
            } else {
                mermaid::Charset::Unicode
            },
            ..Default::default()
        },
    )?;
    let lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let image = if mode.is_pixel() {
        let scene = mermaid::layout(document, &layout)?;
        let rgba = mermaid::raster::rgba(
            &scene,
            &mermaid::raster::PngOptions::default(),
            &options.theme,
        )?;
        Some(Image {
            width: usize::try_from(rgba.width)?,
            height: usize::try_from(rgba.height)?,
            data: rgba.pixels,
        })
    } else {
        None
    };
    let frame = FrameData {
        content_w: lines
            .iter()
            .map(|line| line.chars().count())
            .max()
            .unwrap_or(0),
        content_h: lines.len(),
        text: lines,
        src_w: image.as_ref().map_or(0, |image| image.width),
        src_h: image.as_ref().map_or(0, |image| image.height),
    };
    Ok((frame, image))
}
pub fn run(args: &[String], environment: &Environment) -> (String, String, i32) {
    match prepare(args, environment) {
        Ok(output) => (output, String::new(), 0),
        Err(error) => (String::new(), format!("{error}\n"), 2),
    }
}
struct ViewArguments {
    path: Option<String>,
    script: Option<String>,
    mode: String,
    theme: String,
    color: String,
}

impl Default for ViewArguments {
    fn default() -> Self {
        Self {
            path: None,
            script: None,
            mode: "auto".into(),
            theme: String::new(),
            color: "auto".into(),
        }
    }
}

impl ViewArguments {
    fn parse(mut self, args: &[String]) -> Result<Self, UsageError> {
        let mut flags = true;
        let mut index = 0;
        while index < args.len() {
            let arg = &args[index];
            index += 1;
            if flags && arg == "--" {
                flags = false;
                continue;
            }
            if flags && crate::options::is_flag(arg) {
                self.set_flag(arg, args, &mut index)?;
            } else if self.path.replace(arg.clone()).is_some() {
                return Err(UsageError::ExtraInput { command: "view" });
            }
        }
        Ok(self)
    }

    fn set_flag(
        &mut self,
        arg: &str,
        args: &[String],
        index: &mut usize,
    ) -> Result<(), UsageError> {
        let flag = crate::options::split_flag(arg)
            .filter(|flag| matches!(flag.name, "script" | "graphics" | "t" | "color"))
            .ok_or_else(|| UsageError::UnknownFlag {
                flag: arg.to_owned(),
                command: "view",
            })?;
        let value = flag.value(arg, || {
            let next = args.get(*index).cloned();
            *index += usize::from(next.is_some());
            next
        })?;
        match flag.name {
            "script" => self.script = Some(value),
            "graphics" => self.mode = value,
            "t" => self.theme = value,
            _ => self.color = value,
        }
        Ok(())
    }
}

fn prepare(args: &[String], environment: &Environment) -> Result<String, ViewError> {
    let ViewArguments {
        path,
        script,
        mode,
        theme,
        color,
    } = ViewArguments::default().parse(args)?;
    let path = path.filter(|p| p != "-").ok_or(UsageError::ViewNeedsFile)?;
    crate::options::choice(
        &mode,
        "--graphics",
        &["auto", "kitty", "iterm", "sixel", "cells"],
    )?;
    crate::options::choice(&color, "--color", &["auto", "always", "never"])?;
    let theme = if !theme.is_empty() {
        theme
    } else if environment
        .colorfgbg
        .rsplit(';')
        .next()
        .and_then(|field| field.parse::<u8>().ok())
        .is_some_and(|background| background <= 6 || background == 8)
    {
        "elegant-dark".into()
    } else {
        DEFAULT_THEME.into()
    };
    mermaid::theme::resolve(&theme)?;
    let source = fs::read(&path).map_err(|source| input::read_error(&path, source))?;
    let mut viewer = Viewer {
        state: ViewState::new(&path, 80, 24, Mode::Cells),
        options: Options::new(&theme),
        source,
        image: None,
        scheduler: SchedulerState::initial(),
        colour: crate::options::colour(&color, environment),
        depth: environment.depth,
    };
    viewer.edited();
    if let Some(script) = script {
        replay(&mut viewer, &script)?;
        return Ok(frame(&viewer.state));
    }
    live(&mut viewer, &mode, environment)?;
    Ok(String::new())
}
fn replay(viewer: &mut Viewer, script: &str) -> Result<(), ViewError> {
    let bytes = fs::read(script).map_err(|source| input::read_error(script, source))?;
    for (line, raw) in bytes.split(|byte| *byte == b'\n').enumerate() {
        let event = std::str::from_utf8(raw)
            .map_err(|_| ReplayError::InvalidUtf8)
            .and_then(|text| replay_event(viewer, script, text));
        match event {
            Ok(true) => break,
            Ok(false) => {}
            Err(source) => {
                return Err(ViewError::Script {
                    script: script.to_owned(),
                    line: line + 1,
                    source,
                });
            }
        }
    }
    Ok(viewer.settle()?)
}

fn replay_event(viewer: &mut Viewer, script: &str, raw: &str) -> Result<bool, ReplayError> {
    let text = raw.trim();
    if text.is_empty() || text.starts_with('#') {
        return Ok(false);
    }
    let (verb, rest) = text.split_once(' ').unwrap_or((text, ""));
    let rest = rest.trim();
    match verb {
        "settle" => {
            no_arguments(rest, ReplayError::SettleArguments)?;
            viewer.settle()?;
        }
        "file-delete" => {
            no_arguments(rest, ReplayError::DeleteArguments)?;
            viewer.state.watch_lost = true;
        }
        "file-change" | "file-create" => replay_source(viewer, script, verb, rest)?,
        "resize" => {
            let (width, height) = replay_size(rest)?;
            viewer.state = std::mem::take(&mut viewer.state).resize(width, height);
        }
        "key" => return replay_key(viewer, rest),
        _ => {
            return Err(ReplayError::UnknownVerb {
                verb: verb.to_owned(),
            });
        }
    }
    Ok(false)
}

fn no_arguments(rest: &str, error: ReplayError) -> Result<(), ReplayError> {
    if rest.is_empty() { Ok(()) } else { Err(error) }
}

fn replay_source(
    viewer: &mut Viewer,
    script: &str,
    verb: &str,
    argument: &str,
) -> Result<(), ReplayError> {
    if argument.is_empty() {
        return Err(ReplayError::MissingSource);
    }
    let path = if argument.starts_with('/') {
        argument.to_owned()
    } else {
        paths::join(&paths::directory(script), argument)
    };
    viewer.source = fs::read(&path).map_err(|source| input::read_error(&path, source))?;
    if verb == "file-create" {
        viewer.state.watch_lost = false;
    }
    viewer.edited();
    Ok(())
}

fn replay_key(viewer: &mut Viewer, name: &str) -> Result<bool, ReplayError> {
    if !valid_key(name) {
        return Err(ReplayError::InvalidKey);
    }
    Ok(viewer.key(name, true))
}

fn replay_size(arguments: &str) -> Result<(usize, usize), ReplayError> {
    let fields: Vec<&str> = arguments.split_whitespace().collect();
    let [width, height] = fields[..] else {
        return Err(ReplayError::ResizeArguments);
    };
    match (decimal(width), decimal(height)) {
        (Some(width), Some(height)) if width >= MIN_WIDTH && height >= MIN_HEIGHT => {
            Ok((width, height))
        }
        _ => Err(ReplayError::SizeBelowMinimum),
    }
}

fn decimal(text: &str) -> Option<usize> {
    if !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    text.parse::<i64>()
        .ok()
        .and_then(|value| usize::try_from(value).ok())
}

fn valid_key(s: &str) -> bool {
    (s.len() == 1 && s.as_bytes()[0].is_ascii_graphic())
        || matches!(s, "up" | "down" | "left" | "right" | "esc" | "ctrl-c")
}
struct TerminalGuard;
impl Drop for TerminalGuard {
    fn drop(&mut self) {
        let _ = terminal::disable_raw_mode();
        let mut stdout = io::stdout().lock();
        let _ = stdout.write_all(b"\x1b_Ga=d,d=A,q=2\x1b\\\x1b[?25h\x1b[?1049l");
        let _ = stdout.flush();
    }
}
fn live(viewer: &mut Viewer, mode: &str, environment: &Environment) -> Result<(), ViewError> {
    if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
        return Err(UsageError::ViewNeedsTerminal.into());
    }
    terminal::enable_raw_mode()?;
    let _guard = TerminalGuard;
    if mode != "cells" {
        probe(viewer, mode, environment)?;
    }
    let status = std::process::Command::new("stty")
        .args(["min", "0", "time", "0"])
        .status()?;
    if !status.success() {
        return Err(ViewError::TerminalInput);
    }
    io::stdout().write_all(b"\x1b[?1049h\x1b[?25l")?;
    let size = terminal::size()?;
    viewer.state = std::mem::take(&mut viewer.state).resize(
        usize::from(size.0).max(MIN_WIDTH),
        usize::from(size.1).max(MIN_HEIGHT),
    );
    let target = fs::canonicalize(&viewer.state.path)?;
    let (watch_tx, watch_rx) = mpsc::sync_channel(1);
    let watched = target.clone();
    let mut watcher = notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
        if event
            .as_ref()
            .is_ok_and(|event| !event.paths.iter().any(|path| path == &watched))
        {
            return;
        }
        let _ = watch_tx.try_send(event);
    })?;
    watcher.watch(
        target.parent().ok_or(ViewError::NoParent)?,
        notify::RecursiveMode::NonRecursive,
    )?;
    LiveSession::new().run(viewer, &target, &watch_rx)
}

type RenderCompletion = (bool, Result<ResultFrame, TryFromIntError>);

struct LiveSession {
    worker: Option<std::thread::JoinHandle<()>>,
    cancel: Cancel,
    completion_sender: mpsc::SyncSender<RenderCompletion>,
    completions: mpsc::Receiver<RenderCompletion>,
    watch_timing: WatchTiming,
    pending: Vec<u8>,
    escape_at: Option<Instant>,
    dirty: bool,
}

impl LiveSession {
    fn new() -> Self {
        let (completion_sender, completions) = mpsc::sync_channel(1);
        Self {
            worker: None,
            cancel: Cancel::default(),
            completion_sender,
            completions,
            watch_timing: WatchTiming {
                debounce: None,
                poll: Instant::now(),
            },
            pending: Vec::new(),
            escape_at: None,
            dirty: true,
        }
    }

    fn run(
        mut self,
        viewer: &mut Viewer,
        target: &Path,
        events: &mpsc::Receiver<notify::Result<notify::Event>>,
    ) -> Result<(), ViewError> {
        loop {
            let was_watch_lost = viewer.state.watch_lost;
            self.service_render(viewer)?;
            self.watch_timing.service(viewer, target, events);
            let size = terminal::size()?;
            let size = (
                usize::from(size.0).max(MIN_WIDTH),
                usize::from(size.1).max(MIN_HEIGHT),
            );
            if size != (viewer.state.width, viewer.state.height) {
                viewer.state = std::mem::take(&mut viewer.state).resize(size.0, size.1);
                self.dirty = true;
            }
            if self.service_input(viewer)? {
                return Ok(());
            }
            self.dirty |= was_watch_lost != viewer.state.watch_lost;
            if self.dirty {
                draw(viewer)?;
                self.dirty = false;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn service_render(&mut self, viewer: &mut Viewer) -> Result<(), ViewError> {
        if self.worker.is_none() && viewer.scheduler.inflight != 0 {
            self.cancel = Cancel::new();
            let flag = self.cancel.clone();
            let source = viewer.source.clone();
            let state = viewer.state.clone();
            let options = viewer.options.clone();
            let revision = viewer.scheduler.inflight;
            let sender = self.completion_sender.clone();
            self.worker = Some(std::thread::spawn(move || {
                let result = render(&source, &state, &options, revision, flag.clone());
                let _ = sender.send((flag.is_cancelled(), result));
            }));
        }
        if viewer.scheduler.cancelled {
            self.cancel.cancel();
        }
        let Ok((aborted, result)) = self.completions.try_recv() else {
            return Ok(());
        };
        if let Some(handle) = self.worker.take() {
            handle.join().map_err(|_| ViewError::WorkerFailed)?;
        }
        let event = if aborted && viewer.scheduler.cancelled {
            Event::RenderAborted
        } else {
            Event::RenderDone
        };
        let (next, command) = scheduler::step(viewer.scheduler, event);
        viewer.scheduler = next;
        if matches!(command, Command::Display(_)) {
            viewer.display(result?);
            self.dirty = true;
        }
        Ok(())
    }

    fn service_input(&mut self, viewer: &mut Viewer) -> Result<bool, ViewError> {
        let mut input = [0; 256];
        let count = io::stdin().read(&mut input)?;
        self.pending.extend_from_slice(&input[..count]);
        while let Some(name) = next_key(&mut self.pending, &mut self.escape_at) {
            self.dirty |= key(&name) != Key::None;
            if viewer.key(&name, true) {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

impl Drop for LiveSession {
    fn drop(&mut self) {
        self.cancel.cancel();
        if let Some(handle) = self.worker.take() {
            let _ = handle.join();
        }
    }
}
struct WatchTiming {
    debounce: Option<Instant>,
    poll: Instant,
}

impl WatchTiming {
    fn service(
        &mut self,
        viewer: &mut Viewer,
        target: &Path,
        events: &mpsc::Receiver<notify::Result<notify::Event>>,
    ) {
        for event in events.try_iter() {
            match event {
                Ok(event) if event.paths.iter().any(|path| path == target) => {
                    self.debounce = Some(Instant::now());
                }
                Err(_) => viewer.state.watch_lost = true,
                _ => {}
            }
        }
        if self
            .debounce
            .is_some_and(|time| time.elapsed() >= Duration::from_millis(50))
        {
            self.debounce = None;
            match fs::read(target) {
                Ok(bytes) => {
                    viewer.source = bytes;
                    viewer.state.watch_lost = false;
                    viewer.edited();
                }
                Err(_) => viewer.state.watch_lost = true,
            }
        }
        if viewer.state.watch_lost && self.poll.elapsed() >= Duration::from_millis(500) {
            self.poll = Instant::now();
            if let Ok(bytes) = fs::read(target) {
                viewer.source = bytes;
                viewer.state.watch_lost = false;
                viewer.edited();
            }
        }
    }
}

fn next_key(pending: &mut Vec<u8>, escape_at: &mut Option<Instant>) -> Option<String> {
    let first = *pending.first()?;
    if first != 0x1b {
        pending.remove(0);
        return Some(if first == 3 {
            "ctrl-c".into()
        } else {
            char::from(first).to_string()
        });
    }
    let started = *escape_at.get_or_insert_with(Instant::now);
    if pending.len() >= 3 && (pending[1] == b'[' || pending[1] == b'O') {
        let name = match pending[2] {
            b'A' => "up",
            b'B' => "down",
            b'C' => "right",
            b'D' => "left",
            _ => "",
        };
        pending.drain(..3);
        *escape_at = None;
        return Some(name.into());
    }
    if started.elapsed() < Duration::from_millis(50) {
        return None;
    }
    pending.remove(0);
    *escape_at = None;
    Some("esc".into())
}

fn probe(viewer: &mut Viewer, requested: &str, environment: &Environment) -> Result<(), ViewError> {
    let env = termgfx::probe::Environment {
        kitty_window_id: &environment.kitty_window_id,
        term: &environment.term,
        term_program: &environment.term_program,
    };
    let status = std::process::Command::new("stty")
        .args(["min", "0", "time", "0"])
        .status()?;
    if !status.success() {
        return Err(ViewError::ProbeConfigure);
    }
    let probe_result = probe_replies(&env);
    let restored = std::process::Command::new("stty")
        .args(["min", "1", "time", "0"])
        .status()?;
    if !restored.success() {
        return Err(ViewError::ProbeRestore);
    }
    let replies = probe_result?;
    let capability = replies.capability();
    viewer.state.cell_w = capability.cell_w as usize;
    viewer.state.cell_h = capability.cell_h as usize;
    let selected = if requested == "auto" {
        termgfx::probe::choose(&env, &replies).name()
    } else {
        requested
    };
    viewer.state.mode = Mode::parse(selected).ok_or(ViewError::GraphicsMode)?;
    viewer.state.fit = viewer.state.mode.is_pixel();
    Ok(())
}

fn probe_replies(
    environment: &termgfx::probe::Environment<'_>,
) -> io::Result<termgfx::probe::Replies> {
    let queries = termgfx::probe::queries(environment);
    io::stdout().write_all(&queries)?;
    io::stdout().flush()?;
    let deadline = Instant::now() + Duration::from_millis(100);
    let mut replies = termgfx::probe::Replies::new();
    let mut bytes = Vec::new();
    while Instant::now() < deadline {
        let mut byte = [0];
        if io::stdin().read(&mut byte)? == 0 {
            std::thread::sleep(Duration::from_millis(1));
            continue;
        }
        if Instant::now() >= deadline {
            break;
        }
        bytes.push(byte[0]);
        if bytes.len() > 4096 {
            bytes.clear();
        }
        if byte[0] == b'c' || byte[0] == b't' || byte[0] == b'\\' {
            if replies.push(&bytes) {
                break;
            }
            bytes.clear();
        }
    }
    Ok(replies)
}
fn composite(viewer: &Viewer, image: &Image) -> Result<Vec<u8>, ViewError> {
    let state = &viewer.state;
    let w = state.viewport_pixel_width();
    let h = state.viewport_pixel_height();
    let length = w
        .checked_mul(h)
        .and_then(|n| n.checked_mul(4))
        .filter(|n| *n <= 268435456)
        .ok_or(ViewError::ViewportTooLarge)?;
    let theme = mermaid::theme::resolve(&viewer.options.theme)?;
    let bg = theme.colour(mermaid::theme::Token::Background);
    let mut pixels = vec![0; length];
    let x0 = origin_offset(state.scaled_width(), w);
    let y0 = origin_offset(state.scaled_height(), h);
    for (index, pixel) in pixels.as_chunks_mut::<4>().0.iter_mut().enumerate() {
        pixel.copy_from_slice(&[bg.r, bg.g, bg.b, 255]);
        let Some(x) = (index % w + state.offset_x).checked_sub(x0) else {
            continue;
        };
        let Some(y) = (index / w + state.offset_y).checked_sub(y0) else {
            continue;
        };
        if x >= state.scaled_width() || y >= state.scaled_height() {
            continue;
        }
        let sx = (x * 100 / state.zoom).min(image.width - 1);
        let sy = (y * 100 / state.zoom).min(image.height - 1);
        let source = (sy * image.width + sx) * 4;
        pixel.copy_from_slice(&image.data[source..source + 4]);
    }
    Ok(pixels)
}

fn draw(viewer: &Viewer) -> Result<(), ViewError> {
    let mut output = b"\x1b[H".to_vec();
    let text = frame(&viewer.state);
    if viewer.colour {
        let theme = mermaid::theme::resolve(&viewer.options.theme)?;
        for line in text.lines() {
            let token = if line.contains("error ") {
                mermaid::theme::Token::Error
            } else {
                mermaid::theme::Token::Foreground
            };
            let colour = theme.colour(token);
            let sgr = mermaid::cells::colour::sgr(colour, token, viewer.depth);
            write!(output, "{sgr}{line}\x1b[39m\r\n")?;
        }
    } else {
        output.extend_from_slice(text.replace('\n', "\r\n").as_bytes());
    }
    if viewer.state.mode.is_pixel()
        && viewer.state.panel == Panel::None
        && !viewer.state.empty
        && let Some(image) = &viewer.image
    {
        draw_image(viewer, image, &mut output)?;
    }
    let mut stdout = io::stdout().lock();
    stdout.write_all(&output)?;
    stdout.flush()?;
    Ok(())
}

fn draw_image(viewer: &Viewer, image: &Image, output: &mut Vec<u8>) -> Result<(), ViewError> {
    let pixels = composite(viewer, image)?;
    let width = u32::try_from(viewer.state.viewport_pixel_width())?;
    let height = u32::try_from(viewer.state.viewport_pixel_height())?;
    output.extend_from_slice(b"\x1b[1;1H");
    if viewer.state.mode == Mode::Sixel {
        termgfx::sixel::encode(
            &pixels,
            i32::try_from(width)?,
            i32::try_from(height)?,
            output,
        )?;
        return Ok(());
    }
    let png = mermaid::raster::encode_rgba(width, height, pixels)?;
    match viewer.state.mode {
        Mode::Kitty => termgfx::kitty::encode(&png, output),
        Mode::Iterm => termgfx::iterm::encode(&png, width, height, output),
        Mode::Cells | Mode::Sixel => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod pixel_tests;
