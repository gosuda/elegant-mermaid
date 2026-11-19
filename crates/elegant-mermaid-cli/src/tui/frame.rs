use crate::tui::state::{EMPTY_MESSAGE, Mode, Panel, ViewState};

pub const KEY_ROW: &str = "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit";

pub const KEYS_CONTENT: [&str; 12] = [
    "arrows, hjkl    pan",
    "+ -             zoom (pixel modes)",
    "0               fit / origin",
    "n, p            next, previous block",
    "t               cycle theme",
    "c               toggle charset",
    "g               cycle graphics mode",
    "d               diagnostics panel",
    "r               reload INPUT",
    "?               this key reference",
    "Esc             close panel",
    "q, Ctrl-C       quit",
];

pub const NO_DIAGNOSTICS: &str = "No diagnostics";

pub fn frame(state: &ViewState) -> String {
    let width = state.width;
    let mut rows = viewport_rows(state);
    rows.push(status_row(state));
    rows.push(String::from(KEY_ROW));
    let mut out = String::new();
    for row in &rows {
        out.push_str(&fit_row(row, width));
        out.push('\n');
    }
    out
}

pub fn viewport_rows(state: &ViewState) -> Vec<String> {
    let rows = state.viewport_rows();
    if state.panel != Panel::None {
        return panel_rows(state, rows);
    }
    if state.empty {
        return empty_rows(state.width, rows);
    }
    if state.mode == Mode::Cells && state.frame_rev != 0 {
        return text_rows(state, rows);
    }
    vec![String::new(); rows]
}

pub fn status_row(state: &ViewState) -> String {
    let rest = state.status_rest();
    let row = format!("{} | {}", state.path, rest);
    if scalar_len(&row) <= state.width {
        return row;
    }
    format!("{} | {}", shortened_path(state, &rest), rest)
}

pub fn scalar_len(text: &str) -> usize {
    text.chars().count()
}

pub fn fit_row(row: &str, width: usize) -> String {
    let mut chars: Vec<char> = row.chars().take(width).collect();
    chars.resize(width, ' ');
    chars.into_iter().collect()
}

pub fn wrap_words(text: &str, width: usize) -> Vec<String> {
    if width == 0 {
        return Vec::new();
    }
    let mut lines: Vec<String> = Vec::new();
    let mut current = String::new();
    for word in text.split(' ') {
        if scalar_len(&current) + usize::from(!current.is_empty()) + scalar_len(word) <= width {
            if !current.is_empty() {
                current.push(' ');
            }
            current.push_str(word);
            continue;
        }
        if !current.is_empty() {
            lines.push(std::mem::take(&mut current));
        }
        let mut rest = word;
        while scalar_len(rest) > width {
            let (head, tail) = split_at_scalar(rest, width);
            lines.push(head);
            rest = tail;
        }
        current.push_str(rest);
    }
    if !current.is_empty() {
        lines.push(current);
    }
    lines
}

fn split_at_scalar(text: &str, at: usize) -> (String, &str) {
    let mut boundary = text.len();
    for (taken, (index, symbol)) in text.char_indices().enumerate() {
        if taken == at {
            boundary = index;
            break;
        }
        boundary = index + symbol.len_utf8();
    }
    (text[..boundary].to_string(), &text[boundary..])
}

fn empty_rows(width: usize, rows: usize) -> Vec<String> {
    let mut out = vec![String::new(); rows];
    for (index, line) in wrap_words(EMPTY_MESSAGE, width).into_iter().enumerate() {
        if index >= rows {
            break;
        }
        out[index] = line;
    }
    out
}

fn text_rows(state: &ViewState, rows: usize) -> Vec<String> {
    (0..rows)
        .map(|offset| window_line(state, offset).unwrap_or_default())
        .collect()
}

fn window_line(state: &ViewState, offset: usize) -> Option<String> {
    let index = offset.checked_add(state.offset_y)?;
    let line = state.text.get(index).map_or("", String::as_str);
    Some(
        line.chars()
            .skip(state.offset_x)
            .take(state.width)
            .collect(),
    )
}

fn panel_rows(state: &ViewState, rows: usize) -> Vec<String> {
    let body = rows.saturating_sub(2);
    let mut out = Vec::with_capacity(rows);
    out.push(panel_title(state.panel, state.width));
    out.extend(panel_body(state, body));
    out.push(panel_bottom(state.width));
    out
}

fn panel_title(panel: Panel, width: usize) -> String {
    let title = panel.title();
    let rule = width.saturating_sub(scalar_len(title)).saturating_sub(5);
    format!("+- {title} {}+", "-".repeat(rule))
}

fn panel_bottom(width: usize) -> String {
    format!("+{}+", "-".repeat(width.saturating_sub(2)))
}

fn panel_body(state: &ViewState, slots: usize) -> Vec<String> {
    let content = panel_content(state);
    let inner = state.width.saturating_sub(4);
    let (shown, footer) = panel_split(&content, slots);
    let mut out: Vec<String> = shown
        .iter()
        .map(|line| format!("| {} |", fit_row(line, inner)))
        .collect();
    out.extend(footer.map(|line| format!("| {} |", fit_row(&line, inner))));
    out.resize(slots, format!("| {} |", fit_row("", inner)));
    out
}

fn panel_split(content: &[String], slots: usize) -> (&[String], Option<String>) {
    if slots == 0 || content.len() <= slots {
        return (content, None);
    }
    let shown = slots - 1;
    let hidden = content.len() - shown;
    (&content[..shown], Some(format!("... {hidden} more")))
}

fn panel_content(state: &ViewState) -> Vec<String> {
    match state.panel {
        Panel::Diagnostics => diagnostics_content(state),
        Panel::Keys => KEYS_CONTENT
            .iter()
            .map(|line| (*line).to_string())
            .collect(),
        Panel::None => Vec::new(),
    }
}

fn diagnostics_content(state: &ViewState) -> Vec<String> {
    if state.diagnostics.is_empty() {
        return vec![String::from(NO_DIAGNOSTICS)];
    }
    state.diagnostics.clone()
}

fn shortened_path(state: &ViewState, rest: &str) -> String {
    let room = state
        .width
        .saturating_sub(scalar_len(rest))
        .saturating_sub(6);
    if room == 0 {
        return String::from("...");
    }
    let path: Vec<char> = state.path.chars().collect();
    let skip = path.len().saturating_sub(room);
    let tail: String = path.into_iter().skip(skip).collect();
    format!("...{tail}")
}

#[cfg(test)]
mod tests {
    use super::{frame, scalar_len, wrap_words};
    use crate::tui::state::{EMPTY_MESSAGE, Mode, Panel, ViewState};

    const EMPTY_ROWS: [&str; 6] = [
        "Empty diagram: add a Mermaid header such",
        "as flowchart TD; waiting for changes",
        "",
        "",
        "... | No valid revision yet; fix the sou",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const EMPTY_ROWS_WIDE: [&str; 24] = [
        "Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "... | No valid revision yet; fix the source or press r | - | cells | - | E 1 err",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const CELLS_ROWS: [&str; 6] = [
        " |  A  |",
        " +-----+",
        "     |",
        "     v",
        "... | flowchart | cells | - | E 0 errors",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const CELLS_ROWS_WIDE: [&str; 24] = [
        " |  A  |",
        " +-----+",
        "     |",
        "     v",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "diagram.mmd | flowchart | cells | - | E 0 errors W 0 warnings | REV 2",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const DIAG_ROWS: [&str; 6] = [
        "+- Diagnostics ------------------------+",
        "| error flowchart/unexpected-token 2:4 |",
        "| ... 2 more                           |",
        "+--------------------------------------+",
        "... | No valid revision yet; fix the sou",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const DIAG_ROWS_WIDE: [&str; 24] = [
        "+- Diagnostics ----------------------------------------------------------------+",
        "| error flowchart/unexpected-token 2:4 unexpected ]                            |",
        "| warning flowchart/duplicate-ids 3:3 id A declared twice                      |",
        "| info layout/budget-exhausted 0:0 layout stopped at its iteration cap         |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "+------------------------------------------------------------------------------+",
        "... | No valid revision yet; fix the source or press r | - | cells | - | E 3 err",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const KEYS_ROWS: [&str; 6] = [
        "+- Keys -------------------------------+",
        "| arrows, hjkl    pan                  |",
        "| ... 11 more                          |",
        "+--------------------------------------+",
        "... | sequence | kitty | 95% | E 0 error",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const KEYS_ROWS_WIDE: [&str; 24] = [
        "+- Keys -----------------------------------------------------------------------+",
        "| arrows, hjkl    pan                                                          |",
        "| + -             zoom (pixel modes)                                           |",
        "| 0               fit / origin                                                 |",
        "| n, p            next, previous block                                         |",
        "| t               cycle theme                                                  |",
        "| c               toggle charset                                               |",
        "| g               cycle graphics mode                                          |",
        "| d               diagnostics panel                                            |",
        "| r               reload INPUT                                                 |",
        "| ?               this key reference                                           |",
        "| Esc             close panel                                                  |",
        "| q, Ctrl-C       quit                                                         |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "|                                                                              |",
        "+------------------------------------------------------------------------------+",
        "keys.mmd | sequence | kitty | 95% | E 0 errors W 0 warnings | REV 1",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const LONG_PATH_ROWS: [&str; 6] = [
        "A --> B",
        "B --> C",
        "",
        "",
        "... | flowchart | cells | - | E 0 errors",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const LONG_PATH_ROWS_WIDE: [&str; 24] = [
        "A --> B",
        "B --> C",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        ".../very-long-name.mmd | flowchart | cells | - | E 0 errors W 0 warnings | REV 3",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const WATCH_ROWS: [&str; 6] = [
        "A --> B",
        "B --> C",
        "",
        "",
        "... | WATCH LOST: recreate a.mmd; retryi",
        "? help  q quit  d diagnostics  arrows/hj",
    ];

    const WATCH_ROWS_WIDE: [&str; 24] = [
        "A --> B",
        "B --> C",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "... | WATCH LOST: recreate a.mmd; retrying | STALE revision 3; latest revision 4",
        "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit",
    ];

    const DIAGNOSTICS: [&str; 3] = [
        "error flowchart/unexpected-token 2:4 unexpected ]",
        "warning flowchart/duplicate-ids 3:3 id A declared twice",
        "info layout/budget-exhausted 0:0 layout stopped at its iteration cap",
    ];

    const DIAGRAM: [&str; 5] = ["  +-----+", "  |  A  |", "  +-----+", "      |", "      v"];

    const LONG_PATH: &str = "/home/user/projects/demo/diagrams/very-long-name.mmd";

    fn base(width: usize, height: usize) -> ViewState {
        ViewState {
            path: String::from("a.mmd"),
            width,
            height,
            ..ViewState::default()
        }
    }

    fn cells(width: usize, height: usize) -> ViewState {
        ViewState {
            mode: Mode::Cells,
            ..base(width, height)
        }
    }

    fn empty_state(width: usize, height: usize) -> ViewState {
        let mut state = cells(width, height);
        state.empty = true;
        state.displayed = 1;
        state.errors = 1;
        state.diagnostics = vec![String::from(
            "error common/empty-source 1:1 source is empty",
        )];
        state
    }

    fn diagram_state(width: usize, height: usize) -> ViewState {
        let mut state = cells(width, height);
        state.path = String::from("diagram.mmd");
        state.kind = Some(String::from("flowchart"));
        state.displayed = 2;
        state.frame_rev = 2;
        state.content_w = 8;
        state.content_h = 4;
        state.offset_x = 1;
        state.offset_y = 1;
        state.text = DIAGRAM.iter().map(|line| (*line).to_string()).collect();
        state
    }

    fn diagnostics_state(width: usize, height: usize) -> ViewState {
        let mut state = cells(width, height);
        state.path = String::from("bad.mmd");
        state.displayed = 1;
        state.errors = 3;
        state.panel = Panel::Diagnostics;
        state.auto_panel = true;
        state.diagnostics = DIAGNOSTICS.iter().map(|line| (*line).to_string()).collect();
        state
    }

    fn keys_state(width: usize, height: usize) -> ViewState {
        let mut state = base(width, height);
        state.path = String::from("keys.mmd");
        state.kind = Some(String::from("sequence"));
        state.displayed = 1;
        state.frame_rev = 1;
        state.panel = Panel::Keys;
        state.mode = Mode::Kitty;
        state.zoom = 95;
        state.content_w = 20;
        state.content_h = 4;
        state
    }

    fn long_path_state(width: usize, height: usize) -> ViewState {
        let mut state = cells(width, height);
        state.path = String::from(LONG_PATH);
        state.kind = Some(String::from("flowchart"));
        state.displayed = 3;
        state.frame_rev = 3;
        state.content_w = 8;
        state.content_h = 3;
        state.text = vec![String::from("A --> B"), String::from("B --> C")];
        state
    }

    fn watch_lost_state(width: usize, height: usize) -> ViewState {
        let mut state = cells(width, height);
        state.kind = Some(String::from("flowchart"));
        state.displayed = 4;
        state.frame_rev = 3;
        state.errors = 2;
        state.warnings = 1;
        state.watch_lost = true;
        state.content_w = 8;
        state.content_h = 3;
        state.text = vec![String::from("A --> B"), String::from("B --> C")];
        state
    }

    fn trimmed_rows(text: &str) -> Vec<String> {
        text.lines()
            .map(|line| line.trim_end_matches(' ').to_string())
            .collect()
    }

    fn assert_frame(state: &ViewState, expected: &[&str]) {
        let text = frame(state);
        let rows = trimmed_rows(&text);
        assert_eq!(rows.len(), expected.len());
        for (index, want) in expected.iter().enumerate() {
            assert_eq!(rows[index], *want, "row {index}");
        }
        let raw: Vec<&str> = text.split('\n').collect();
        assert_eq!(raw.len(), expected.len() + 1);
        assert_eq!(raw[expected.len()], "");
        for row in &raw[..expected.len()] {
            assert_eq!(scalar_len(row), state.width);
        }
    }

    #[test]
    fn empty_message_wraps_at_the_width() {
        assert_eq!(
            wrap_words(EMPTY_MESSAGE, 40),
            vec![
                String::from("Empty diagram: add a Mermaid header such"),
                String::from("as flowchart TD; waiting for changes"),
            ]
        );
        assert_eq!(
            wrap_words(EMPTY_MESSAGE, 80),
            vec![String::from(EMPTY_MESSAGE)]
        );
    }

    #[test]
    fn a_word_longer_than_the_width_splits() {
        assert_eq!(
            wrap_words("abcdefghij", 4),
            vec![
                String::from("abcd"),
                String::from("efgh"),
                String::from("ij")
            ]
        );
        assert_eq!(
            wrap_words("ab abcdefghij", 4),
            vec![
                String::from("ab"),
                String::from("abcd"),
                String::from("efgh"),
                String::from("ij"),
            ]
        );
    }

    #[test]
    fn empty_input_frame() {
        assert_frame(&empty_state(40, 6), &EMPTY_ROWS);
        assert_frame(&empty_state(80, 24), &EMPTY_ROWS_WIDE);
    }

    #[test]
    fn cells_content_frame_honours_the_offsets() {
        assert_frame(&diagram_state(40, 6), &CELLS_ROWS);
        assert_frame(&diagram_state(80, 24), &CELLS_ROWS_WIDE);
    }

    #[test]
    fn diagnostics_panel_elides_the_lines_that_do_not_fit() {
        assert_frame(&diagnostics_state(40, 6), &DIAG_ROWS);
        assert_frame(&diagnostics_state(80, 24), &DIAG_ROWS_WIDE);
    }

    #[test]
    fn keys_panel_lists_every_key() {
        assert_frame(&keys_state(40, 6), &KEYS_ROWS);
        assert_frame(&keys_state(80, 24), &KEYS_ROWS_WIDE);
    }

    #[test]
    fn a_long_path_is_shortened_from_the_front() {
        assert_frame(&long_path_state(40, 6), &LONG_PATH_ROWS);
        assert_frame(&long_path_state(80, 24), &LONG_PATH_ROWS_WIDE);
    }

    #[test]
    fn watch_lost_and_stale_share_the_message_field() {
        assert_frame(&watch_lost_state(40, 6), &WATCH_ROWS);
        assert_frame(&watch_lost_state(80, 24), &WATCH_ROWS_WIDE);
    }

    struct Xorshift(u32);

    impl Xorshift {
        fn draw(&mut self) -> u32 {
            let mut value = self.0;
            value ^= value << 13;
            value ^= value >> 17;
            value ^= value << 5;
            self.0 = value;
            value
        }

        fn index(&mut self, count: usize) -> usize {
            if count == 0 {
                return 0;
            }
            let bound = u32::try_from(count).unwrap_or(u32::MAX);
            usize::try_from(self.draw() % bound).unwrap_or(0)
        }

        fn range(&mut self, lo: usize, hi: usize) -> usize {
            lo + self.index(hi - lo + 1)
        }

        fn flag(&mut self) -> bool {
            self.index(2) == 1
        }

        fn count(&mut self, hi: u32) -> u32 {
            let bound = usize::try_from(hi).unwrap_or(usize::MAX);
            u32::try_from(self.range(0, bound)).unwrap_or(0)
        }
    }

    fn random_scalar(rng: &mut Xorshift) -> char {
        const ALPHABET: [char; 12] = ['a', 'b', 'A', ' ', '-', '>', '/', '|', '0', 'é', '界', '█'];
        let index = rng.index(ALPHABET.len());
        ALPHABET[index]
    }

    fn random_text(rng: &mut Xorshift, max: usize) -> String {
        let len = rng.range(0, max);
        (0..len).map(|_| random_scalar(rng)).collect::<String>()
    }

    impl Xorshift {
        fn state(&mut self) -> ViewState {
            let width = self.range(20, 120);
            let height = self.range(5, 40);
            let mode = match self.index(4) {
                0 => Mode::Cells,
                1 => Mode::Kitty,
                2 => Mode::Iterm,
                _ => Mode::Sixel,
            };
            let rows = height - 2;
            let lines = self.range(0, rows + 4);
            let text: Vec<String> = (0..lines).map(|_| random_text(self, width + 8)).collect();
            let diagnostics: Vec<String> = (0..self.range(0, 30))
                .map(|_| random_text(self, width + 10))
                .collect();
            let kind = if self.flag() {
                Some(random_text(self, 12))
            } else {
                None
            };
            let block = if self.flag() {
                Some((self.count(4), 4))
            } else {
                None
            };
            let panel = match self.index(3) {
                0 => Panel::None,
                1 => Panel::Diagnostics,
                _ => Panel::Keys,
            };
            ViewState {
                path: random_text(self, 60),
                width,
                height,
                mode,
                fit: self.flag(),
                zoom: self.range(10, 800),
                kind,
                block,
                errors: self.count(3),
                warnings: self.count(3),
                empty: self.flag(),
                displayed: u64::from(self.count(9)),
                frame_rev: u64::from(self.count(9)),
                panel,
                auto_panel: false,
                diagnostics,
                watch_lost: self.flag(),
                text,
                content_w: self.range(0, width + 20),
                content_h: self.range(0, rows + 5),
                offset_x: self.range(0, 30),
                offset_y: self.range(0, 30),
                src_w: self.range(0, 4000),
                src_h: self.range(0, 4000),
                cell_w: self.range(1, 20),
                cell_h: self.range(1, 30),
            }
        }
    }
    #[test]
    fn random_states_always_produce_a_full_frame() {
        for case in 0..2000 {
            let state = Xorshift(case + 1).state();
            let text = frame(&state);
            let rows: Vec<&str> = text.split('\n').collect();
            assert_eq!(rows.len(), state.height + 1);
            assert_eq!(rows[state.height], "");
            for row in &rows[..state.height] {
                assert_eq!(scalar_len(row), state.width);
            }
            assert_eq!(super::viewport_rows(&state).len(), state.viewport_rows());
            assert!(
                !text.contains('\r'),
                "random_states_always_produce_a_full_frame: expected {} to hold (observed false)",
                stringify!(!text.contains('\r'))
            );
            assert!(
                !text.contains('\u{1b}'),
                "random_states_always_produce_a_full_frame: expected {} to hold (observed false)",
                stringify!(!text.contains('\u{1b}'))
            );
        }
    }
}
