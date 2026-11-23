mod check;
mod diagnostics;
mod error;
mod explain;
mod input;
mod kernel_eval;
mod layout;
mod lint;
mod options;
mod output;
mod paths;
mod render;
mod report;
mod termgfx;
mod tui;
mod view;

use error::UsageError;
use std::ffi::OsString;
use std::io::{IsTerminal, Write};

const USAGE: &str = "Usage: emd COMMAND [OPTIONS]\n  render   Render Mermaid as SVG, PNG, or terminal text\n  check    Check syntax and semantics without changing files\n  lint     Check lint rules and optionally apply fixes\n  view     Watch and display a diagram in the terminal\n  layout   Print canonical layout data\n  explain  Explain a diagnostic code\n";
fn main() {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let (stdout, stderr, code) = dispatch(&args);
    let out = std::io::stdout().lock().write_all(&stdout);
    let err = std::io::stderr().lock().write_all(stderr.as_bytes());
    std::process::exit(if out.is_ok() && err.is_ok() { code } else { 2 });
}
fn wants_help(args: &[OsString]) -> bool {
    args.len() == 2 && (args[1] == "--help" || args[1] == "-h")
}
fn dispatch(args: &[OsString]) -> (Vec<u8>, String, i32) {
    if args.first().is_some_and(|command| command == "render") && !wants_help(args) {
        let strings: Vec<_> = args[1..]
            .iter()
            .map(|s| s.to_string_lossy().into_owned())
            .collect();
        return render::run(&strings, &environment());
    }
    let (stdout, stderr, code) = dispatch_text(args);
    (stdout.into_bytes(), stderr, code)
}
fn dispatch_text(args: &[OsString]) -> (String, String, i32) {
    let Some(command) = args.first() else {
        return (String::new(), USAGE.into(), 2);
    };
    let command = command.to_string_lossy();
    if command == "-h" || command == "--help" {
        return (USAGE.into(), String::new(), 0);
    }
    if command == "--version" {
        return ("emd 0.1.0\n".into(), String::new(), 0);
    }
    if wants_help(args) && command != "kernel-eval" {
        return help(&command);
    }
    let strings: Vec<_> = args[1..]
        .iter()
        .map(|s| s.to_string_lossy().into_owned())
        .collect();
    let environment = environment();
    match command.as_ref() {
        "layout" => layout::run(&args[1..]),
        "check" => check::run(&strings, &environment),
        "lint" => lint::run(&strings, &environment),
        "explain" => explain::run(&strings),
        "view" => view::run(&strings, &environment),
        "kernel-eval" => match kernel_eval::eval_file(&args[1..]) {
            Ok(stdout) => (stdout, String::new(), 0),
            Err(failure) => (failure.stdout, format!("{}\n", failure.error), 2),
        },
        _ => (
            String::new(),
            format!(
                "{}\n",
                UsageError::UnknownCommand {
                    command: command.to_string()
                }
            ),
            2,
        ),
    }
}
fn environment() -> view::Environment {
    let term = std::env::var("TERM").unwrap_or_default();
    let colorterm = std::env::var("COLORTERM").unwrap_or_default();
    view::Environment {
        colorfgbg: std::env::var("COLORFGBG").unwrap_or_default(),
        kitty_window_id: std::env::var("KITTY_WINDOW_ID").unwrap_or_default(),
        term_program: std::env::var("TERM_PROGRAM").unwrap_or_default(),
        auto_colour: options::colour_enabled("auto", std::io::stdout().is_terminal(), |name| {
            if name == "TERM" {
                term.clone()
            } else {
                std::env::var(name).unwrap_or_default()
            }
        }),
        depth: if ["truecolor", "24bit"].contains(&colorterm.as_str()) {
            elegant_mermaid::cells::ColorMode::Truecolor
        } else if term.ends_with("256color") {
            elegant_mermaid::cells::ColorMode::Ansi256
        } else {
            elegant_mermaid::cells::ColorMode::Ansi16
        },
        term,
    }
}
fn render_help() -> String {
    format!(
        "Render Mermaid as SVG, PNG, or terminal text\nUsage: emd render [INPUT] [-i INPUT] [-o OUTPUT] [-e svg|png|text] [-t THEME] [-b BACKGROUND] [-s SCALE] [--charset unicode|ascii] [--color auto|always|never] [--width COLS] [--svg-text font|paths] [--icon-pack FILE]... [-c CONFIG]\nDefaults: input stdin; output stdout; format inferred from -o (.svg, .png, .txt), else text on a terminal and svg otherwise; theme elegant-light (elegant-dark on a dark terminal for text); background theme bg; scale 2 (1 to 8, PNG pixels per px); charset unicode; color auto; width 0; svg-text font (paths draws glyph outlines, so the viewer needs no font); icon packs none; config none. Themes: {}. PNG needs -o FILE.png or a redirected stdout. -c reads upstream config text (a block mapping); --icon-pack reads an Iconify JSON file and may repeat.\nExample: emd render demo.mmd -e text\n",
        elegant_mermaid::theme::names().join(", ")
    )
}
fn help(command: &str) -> (String, String, i32) {
    if command == "render" {
        return (render_help(), String::new(), 0);
    }
    let text = match command {
        "check" => {
            "Check syntax and semantics without changing files\nUsage: emd check [PATH...] [--output-format text|json|sarif|github] [--color auto|always|never]\nDefaults: paths . (.mmd, .mermaid, .md, .markdown, and .mdx files, skipping hidden directories, node_modules, and target; - reads stdin); output-format text; color auto. Markdown hosts report diagnostics at host positions.\nExample: emd check docs/\n"
        }
        "view" => {
            "Watch and display a diagram in the terminal\nUsage: emd view INPUT [-t THEME] [--graphics auto|kitty|iterm|sixel|cells] [--color auto|always|never]\nDefaults: theme elegant-light (elegant-dark on a dark terminal); graphics auto; color auto.\nExample: emd view demo.mmd\n"
        }
        "layout" => {
            "Print canonical layout data\nUsage: emd layout [INPUT] [--profile vector|cell] [--metrics]\nDefaults: input stdin; profile vector; metrics off. --metrics prints vector layout quality metrics.\nExample: emd layout demo.mmd --profile cell\n"
        }
        "lint" => {
            "Check lint rules and optionally apply fixes\nUsage: emd lint [PATH...] [--fix] [--unsafe-fixes] [--select CODES] [--ignore CODES] [--deny-warnings] [--output-format text|json|sarif|github] [--lint-config FILE] [--no-config] [--color auto|always|never]\nDefaults: paths . (.mmd, .mermaid, .md, .markdown, and .mdx files, skipping hidden directories, node_modules, and target; - reads stdin); fixes off (--fix applies safe fixes and rewrites the files; --unsafe-fixes also applies unsafe fixes and needs --fix; lint --fix - writes the fixed source to stdout and text diagnostics to stderr); select the default rule set; ignore none; deny-warnings off (a warning exits 0); output-format text; lint-config found by walking up from each input's directory to the first emd.json; no-config off; color auto. CODES is a comma-separated list of codes printed by emd check or emd lint. Exit 1 on an error diagnostic, or on a warning under --deny-warnings.\nExample: emd lint --fix demo.mmd\n"
        }
        "explain" => {
            "Explain a diagnostic code\nUsage: emd explain CODE [--output-format text|json]\nDefaults: output-format text. Prints the code, kind, severity, fix_safety, summary, help, rationale, and suppression comment of the registry row; an alias prints the row of its current code.\nExample: emd explain flowchart/unexpected-token\n"
        }
        _ => {
            return (
                String::new(),
                format!(
                    "{}\n",
                    UsageError::UnknownCommand {
                        command: command.to_owned()
                    }
                ),
                2,
            );
        }
    };
    (text.into(), String::new(), 0)
}
