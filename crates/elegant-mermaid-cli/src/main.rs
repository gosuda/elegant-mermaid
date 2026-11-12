mod kernel_eval;
mod layout;

use std::ffi::OsString;
use std::io::Write;

fn main() {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let (stdout, stderr, code) = dispatch(&args);
    let out = std::io::stdout().lock().write_all(stdout.as_bytes());
    let err = std::io::stderr().lock().write_all(stderr.as_bytes());
    std::process::exit(if out.is_ok() && err.is_ok() { code } else { 2 });
}

fn dispatch(args: &[OsString]) -> (String, String, i32) {
    if args.first().is_some_and(|arg| arg == "layout") {
        return layout::run(&args[1..]);
    }
    if args.first().is_none_or(|arg| arg != "kernel-eval") {
        return (
            String::new(),
            String::from("Usage: emd kernel-eval FILE\n"),
            2,
        );
    }
    match kernel_eval::eval_file(&args[1..]) {
        Ok(stdout) => (stdout, String::new(), 0),
        Err(failure) => (failure.stdout, format!("{}\n", failure.error.message()), 2),
    }
}
