mod check;
mod diagnostics;
mod input;
mod kernel_eval;
mod layout;
mod options;
mod render;

use std::ffi::OsString;
use std::io::Write;

const USAGE: &str = "Usage: emd COMMAND [OPTIONS]\n  render   Render Mermaid as SVG, PNG, or terminal text\n  check    Check syntax and semantics without changing files\n  lint     Check lint rules and optionally apply fixes\n  view     Watch and display a diagram in the terminal\n  layout   Print canonical layout data\n  explain  Explain a diagnostic code\n";
fn main() {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let (stdout, stderr, code) = dispatch(&args);
    let out = std::io::stdout().lock().write_all(stdout.as_bytes());
    let err = std::io::stderr().lock().write_all(stderr.as_bytes());
    std::process::exit(if out.is_ok() && err.is_ok() { code } else { 2 });
}
fn dispatch(args: &[OsString]) -> (String, String, i32) {
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
    if args.len() == 2 && (args[1] == "--help" || args[1] == "-h") && command != "kernel-eval" {
        return help(&command);
    }
    let strings: Vec<_> = args[1..]
        .iter()
        .map(|s| s.to_string_lossy().into_owned())
        .collect();
    match command.as_ref() {
        "layout" => layout::run(&args[1..]),
        "render" => render::run(&strings),
        "check" => check::run(&strings),
        "kernel-eval" => match kernel_eval::eval_file(&args[1..]) {
            Ok(stdout) => (stdout, String::new(), 0),
            Err(failure) => (failure.stdout, format!("{}\n", failure.error.message()), 2),
        },
        _ => (
            String::new(),
            format!("unknown command {command}; run emd --help\n"),
            2,
        ),
    }
}
fn help(command: &str) -> (String, String, i32) {
    let text = match command {
        "render" => {
            "Render Mermaid as SVG or terminal text\nUsage: emd render [INPUT] [-i INPUT] [-o OUTPUT] [-e svg|text] [-t THEME] [-b BACKGROUND] [--charset unicode|ascii] [--color auto|always|never] [--width COLS] [--svg-text font]\nDefaults: input stdin; output stdout; format inferred; theme elegant-light (elegant-dark on a dark terminal for text); background theme bg; charset unicode; color auto; width 0; svg-text font. Themes: elegant-light, elegant-dark.\nExample: emd render demo.mmd -e text\n"
        }
        "check" => {
            "Check syntax and semantics without changing files\nUsage: emd check [PATH...] [--output-format text|json] [--color auto|always|never]\nDefaults: paths .; output-format text; color auto.\nExample: emd check docs/\n"
        }
        "layout" => {
            "Print canonical layout data\nUsage: emd layout [INPUT] [--profile vector|cell] [--metrics]\nDefaults: input stdin; profile vector; metrics off. --metrics prints vector layout quality metrics.\nExample: emd layout demo.mmd --profile cell\n"
        }
        _ => {
            return (
                String::new(),
                format!("unknown command {command}; run emd --help\n"),
                2,
            );
        }
    };
    (text.into(), String::new(), 0)
}
