use crate::diag::{Diagnostic, Related, Severity, push_decimal};
use crate::source::{Position, Span, align, line_content, line_position, line_starts};

pub struct TextFrameOptions {
    pub colour: bool,
    pub width: fn(char) -> usize,
}

struct FrameStyle {
    word: fn(&mut String, Severity),
    mark: fn(&mut String, Severity, usize),
}

const PLAIN: FrameStyle = FrameStyle {
    word: push_word,
    mark: push_mark,
};

const COLOUR: FrameStyle = FrameStyle {
    word: push_word_colour,
    mark: push_mark_colour,
};

struct Frame<'a> {
    out: &'a mut String,
    text: &'a str,
    starts: Vec<usize>,
    path: &'a str,
    width: fn(char) -> usize,
    style: &'a FrameStyle,
}

pub fn render_text(
    out: &mut String,
    path: &str,
    text: &str,
    ds: &[Diagnostic],
    options: &TextFrameOptions,
) {
    let style = if options.colour { &COLOUR } else { &PLAIN };
    let mut frame = Frame {
        out,
        text,
        starts: line_starts(text),
        path,
        width: options.width,
        style,
    };
    for (position, diagnostic) in ds.iter().enumerate() {
        if position > 0 {
            frame.out.push('\n');
        }
        frame.render(diagnostic);
    }
}

impl Frame<'_> {
    fn render(&mut self, d: &Diagnostic) {
        let start = self.position(d.span.start);
        let content = line_content(self.text, &self.starts, start.line);
        let from = self.aligned_offset(d.span.start, content);
        let to = self.aligned_offset(d.span.end, content).max(from);
        let first = self.cell_column(content.start, from);
        let last = self.cell_column(content.start, to);
        let cells = last.saturating_sub(first).max(1);
        let gutter = decimal_digits(start.line);
        self.push_header(start, d);
        self.push_rule(gutter);
        self.push_source(start.line, content);
        self.push_underline(gutter, first, cells, d.severity);
        self.push_notes(d);
    }

    fn position(&self, offset: usize) -> Position {
        line_position(self.text, &self.starts, offset)
    }

    fn aligned_offset(&self, offset: usize, content: Span) -> usize {
        align(self.text, offset).clamp(content.start, content.end)
    }

    fn push_header(&mut self, start: Position, d: &Diagnostic) {
        push_field(self.out, self.path);
        self.out.push(':');
        push_decimal(self.out, start.line);
        self.out.push(':');
        push_decimal(self.out, start.column);
        self.out.push_str(": ");
        (self.style.word)(self.out, d.severity);
        self.out.push('[');
        push_field(self.out, d.code);
        self.out.push_str("]: ");
        push_field(self.out, &d.message);
        self.out.push('\n');
    }

    fn push_rule(&mut self, gutter: usize) {
        push_spaces(self.out, gutter);
        self.out.push_str(" |\n");
    }

    fn push_source(&mut self, line: usize, content: Span) {
        push_decimal(self.out, line);
        self.out.push_str(" | ");
        self.push_shown_text(content);
        self.out.push('\n');
    }

    fn push_underline(&mut self, gutter: usize, first: usize, cells: usize, severity: Severity) {
        push_spaces(self.out, gutter);
        self.out.push_str(" | ");
        push_spaces(self.out, first);
        (self.style.mark)(self.out, severity, cells);
        self.out.push('\n');
    }

    fn push_notes(&mut self, d: &Diagnostic) {
        push_note_line(self.out, "  = help: ", &d.help);
        for fix in &d.fixes {
            push_note_line(self.out, "  = fix: ", &fix.title);
        }
        for related in &d.related {
            self.push_place_note(related);
        }
    }

    fn push_place_note(&mut self, related: &Related) {
        let position = self.position(related.span.start);
        self.out.push_str("  = note: ");
        push_field(self.out, &related.message);
        self.out.push_str(" at ");
        push_field(self.out, self.path);
        self.out.push(':');
        push_decimal(self.out, position.line);
        self.out.push(':');
        push_decimal(self.out, position.column);
        self.out.push('\n');
    }

    fn push_shown_text(&mut self, content: Span) {
        let mut column = 0;
        for shown in self.text[content.start..content.end].chars() {
            if shown == '\t' {
                let gap = 8 - column % 8;
                push_spaces(self.out, gap);
                column += gap;
                continue;
            }
            let shown = printable(shown);
            self.out.push(shown);
            column += (self.width)(shown);
        }
    }

    fn cell_column(&self, start: usize, offset: usize) -> usize {
        let mut column = 0;
        for ch in self.text[start..offset].chars() {
            column += if ch == '\t' {
                8 - column % 8
            } else {
                (self.width)(printable(ch))
            };
        }
        column
    }
}

fn push_note_line(out: &mut String, prefix: &str, body: &str) {
    if body.is_empty() {
        return;
    }
    out.push_str(prefix);
    push_field(out, body);
    out.push('\n');
}

fn push_field(out: &mut String, text: &str) {
    out.extend(text.chars().map(printable));
}

fn printable(ch: char) -> char {
    let code = u32::from(ch);
    if code < 0x20 || (0x7F..=0x9F).contains(&code) {
        '\u{FFFD}'
    } else {
        ch
    }
}

fn push_word(out: &mut String, severity: Severity) {
    out.push_str(severity.as_str());
}

fn push_word_colour(out: &mut String, severity: Severity) {
    push_sgr(out, severity);
    out.push_str(severity.as_str());
    push_reset(out);
}

fn push_mark(out: &mut String, _: Severity, cells: usize) {
    push_marks(out, cells);
}

fn push_mark_colour(out: &mut String, severity: Severity, cells: usize) {
    push_sgr(out, severity);
    push_marks(out, cells);
    push_reset(out);
}

fn push_marks(out: &mut String, cells: usize) {
    out.push('^');
    for _ in 1..cells {
        out.push('~');
    }
}

fn push_sgr(out: &mut String, severity: Severity) {
    out.push_str("\u{1b}[");
    push_decimal(out, usize::from(severity.sgr()));
    out.push('m');
}

fn push_reset(out: &mut String) {
    out.push_str("\u{1b}[0m");
}

fn decimal_digits(value: usize) -> usize {
    let mut digits = 1;
    let mut rest = value;
    while rest >= 10 {
        rest /= 10;
        digits += 1;
    }
    digits
}

fn push_spaces(out: &mut String, count: usize) {
    for _ in 0..count {
        out.push(' ');
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::{Fix, FixSafety, Related};
    use crate::source::Span;

    fn diagnostic(span: Span) -> Diagnostic {
        Diagnostic {
            code: "flowchart/unclosed-node-bracket",
            severity: Severity::Error,
            message: String::from("unexpected end of input"),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        }
    }

    fn plain() -> TextFrameOptions {
        TextFrameOptions {
            colour: false,
            width: |_| 1,
        }
    }

    fn coloured() -> TextFrameOptions {
        TextFrameOptions {
            colour: true,
            width: |_| 1,
        }
    }

    #[test]
    fn frame_matches_spec_shape() {
        let text = "abc\ndef\n";
        let d = diagnostic(Span { start: 5, end: 6 });
        let mut out = String::new();
        render_text(&mut out, "x.mmd", text, &[d], &plain());
        assert_eq!(
            out,
            "x.mmd:2:2: error[flowchart/unclosed-node-bracket]: unexpected end of input\n  |\n2 | def\n  |  ^\n"
        );
    }

    #[test]
    fn frame_prints_help_fix_and_note_in_order() {
        let text = "flowchart LR\n  A[Start --> B\n";
        let mut d = diagnostic(Span { start: 3, end: 10 });
        d.help = String::from("close the bracket");
        d.fixes = vec![Fix {
            title: String::from("add ]"),
            safety: FixSafety::Safe,
            edits: Vec::new(),
        }];
        d.related = vec![Related {
            span: Span { start: 0, end: 9 },
            message: String::from("header starts here"),
        }];
        let mut out = String::new();
        render_text(&mut out, "<stdin>", text, &[d], &plain());
        assert_eq!(
            out,
            "<stdin>:1:4: error[flowchart/unclosed-node-bracket]: unexpected end of input\n  |\n1 | flowchart LR\n  |    ^~~~~~~\n  = help: close the bracket\n  = fix: add ]\n  = note: header starts here at <stdin>:1:1\n"
        );
    }

    #[test]
    fn spec_block_renders_verbatim() {
        let text = "source line\n";
        let d = Diagnostic {
            code: "code",
            severity: Severity::Error,
            message: String::from("message"),
            span: Span { start: 0, end: 4 },
            related: Vec::new(),
            help: String::from("HELP"),
            fixes: vec![Fix {
                title: String::from("TITLE"),
                safety: FixSafety::Safe,
                edits: Vec::new(),
            }],
        };
        let mut out = String::new();
        render_text(&mut out, "path", text, &[d], &plain());
        assert_eq!(
            out,
            "path:1:1: error[code]: message\n  |\n1 | source line\n  | ^~~~\n  = help: HELP\n  = fix: TITLE\n"
        );
    }

    #[test]
    fn blank_line_separates_diagnostics() {
        let text = "ab\n";
        let ds = [
            diagnostic(Span { start: 0, end: 1 }),
            diagnostic(Span { start: 1, end: 2 }),
        ];
        let mut out = String::new();
        render_text(&mut out, "p", text, &ds, &plain());
        assert!(
            out.contains("^\n\np:1:2: "),
            "blank line separates diagnostics: contract out.contains(\"^\\n\\np:1:2: \") failed; observed out={:?}",
            out
        );
        assert_eq!(out.matches("error[flowchart").count(), 2);
    }

    #[test]
    fn multi_line_span_underlines_to_the_first_line_end() {
        let text = "abc\ndefg\n";
        let d = diagnostic(Span { start: 1, end: 8 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("1 | abc\n  |  ^~\n"),
            "multi line span underlines to the first line end: contract out.contains(\"1 | abc\\n | ^~\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn zero_width_span_gets_one_cell() {
        let text = "abc\n";
        let d = diagnostic(Span { start: 2, end: 2 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("1 | abc\n  |   ^\n"),
            "zero width span gets one cell: contract out.contains(\"1 | abc\\n | ^\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn tabs_expand_to_eight_column_stops_and_the_caret_follows() {
        let text = "a\tbc\n";
        let d = diagnostic(Span { start: 2, end: 3 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("1 | a       bc\n"),
            "tabs expand to eight column stops and the caret follows: contract out.contains(\"1 | a bc\\n\") failed; observed out={:?}",
            out
        );
        assert!(
            out.contains("  |         ^\n"),
            "tabs expand to eight column stops and the caret follows: contract out.contains(\" | ^\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn control_characters_print_as_replacement() {
        let text = "a\u{1}b\n";
        let d = diagnostic(Span { start: 0, end: 1 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("1 | a\u{FFFD}b\n"),
            "control characters print as replacement: contract out.contains(\"1 | a\\u{{FFFD}}b\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn colour_wraps_only_the_word_and_the_underline() {
        let text = "ab\n";
        let d = Diagnostic {
            code: "c/x",
            severity: Severity::Warning,
            message: String::from("m"),
            span: Span { start: 0, end: 2 },
            related: Vec::new(),
            help: String::from("h"),
            fixes: Vec::new(),
        };
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &coloured());
        assert_eq!(
            out,
            "p:1:1: \u{1b}[33mwarning\u{1b}[0m[c/x]: m\n  |\n1 | ab\n  | \u{1b}[33m^~\u{1b}[0m\n  = help: h\n"
        );
    }

    #[test]
    fn severity_to_sgr_codes() {
        assert_eq!(Severity::Error.sgr(), 31);
        assert_eq!(Severity::Warning.sgr(), 33);
        assert_eq!(Severity::Info.sgr(), 36);
    }

    #[test]
    fn gutter_is_as_wide_as_the_line_number() {
        let text = "\n\n\n\n\n\n\n\n\n\nab\n";
        let d = diagnostic(Span { start: 10, end: 11 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("11 | ab\n"),
            "gutter is as wide as the line number: contract out.contains(\"11 | ab\\n\") failed; observed out={:?}",
            out
        );
        assert!(
            out.contains("   |\n"),
            "gutter is as wide as the line number: contract out.contains(\" |\\n\") failed; observed out={:?}",
            out
        );
        assert!(
            out.contains("   | ^\n"),
            "gutter is as wide as the line number: contract out.contains(\" | ^\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn carriage_return_is_not_part_of_the_printed_line() {
        let text = "one\r\ntwo\r\n";
        let d = diagnostic(Span { start: 5, end: 6 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("2 | two\n  | ^\n"),
            "carriage return is not part of the printed line: contract out.contains(\"2 | two\\n | ^\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn empty_related_message_still_prints_its_note_line() {
        let text = "ab\n";
        let mut d = diagnostic(Span { start: 0, end: 1 });
        d.related = vec![Related {
            span: Span { start: 1, end: 2 },
            message: String::new(),
        }];
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.ends_with("  = note:  at p:1:2\n"),
            "empty related message still prints its note line: contract out.ends_with(\" = note: at p:1:2\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn width_function_places_the_caret_in_cells() {
        fn wide(ch: char) -> usize {
            if ch == '世' { 2 } else { 1 }
        }
        let text = "世a\n";
        let d = diagnostic(Span { start: 3, end: 4 });
        let options = TextFrameOptions {
            colour: false,
            width: wide,
        };
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &options);
        assert!(
            out.contains("1 | 世a\n  |   ^\n"),
            "wide: contract out.contains(\"1 | 世a\\n | ^\\n\") failed; observed out={:?}",
            out
        );
    }

    #[test]
    fn offsets_inside_a_sequence_do_not_split_it() {
        let text = "世\nz";
        let d = diagnostic(Span { start: 1, end: 2 });
        let mut out = String::new();
        render_text(&mut out, "p", text, &[d], &plain());
        assert!(
            out.contains("1 | 世\n  | ^\n"),
            "offsets inside a sequence do not split it: contract out.contains(\"1 | 世\\n | ^\\n\") failed; observed out={:?}",
            out
        );
    }
    #[test]
    fn terminal_fields_replace_isolated_controls_without_changing_frame_structure() {
        for ch in (0..=0x1f).chain(0x7f..=0x9f).filter_map(char::from_u32) {
            for colour in [false, true] {
                let field = format!("世{ch}é");
                let mut d = diagnostic(Span { start: 1, end: 2 });
                d.code = "c/\u{1}x";
                d.message = field.clone();
                d.help = field.clone();
                d.fixes.push(Fix {
                    title: field.clone(),
                    safety: FixSafety::Safe,
                    edits: Vec::new(),
                });
                d.related.push(Related {
                    span: Span { start: 0, end: 1 },
                    message: field.clone(),
                });
                let mut out = String::new();
                render_text(
                    &mut out,
                    &field,
                    "\t界\n",
                    &[d],
                    &TextFrameOptions {
                        colour,
                        width: |_| 1,
                    },
                );
                let plain = out.replace("\u{1b}[31m", "").replace("\u{1b}[0m", "");
                assert_eq!(
                    plain,
                    "世�é:1:2: error[c/�x]: 世�é\n  |\n1 |         界\n  |         ^\n  = help: 世�é\n  = fix: 世�é\n  = note: 世�é at 世�é:1:1\n"
                );
                if colour {
                    assert_eq!(out.matches("\u{1b}[31m").count(), 2);
                    assert_eq!(out.matches("\u{1b}[0m").count(), 2);
                }
            }
        }
    }
}
