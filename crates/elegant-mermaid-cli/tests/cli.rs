use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_emd");

struct Outcome {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

fn run<S: AsRef<OsStr>>(args: &[S]) -> io::Result<Outcome> {
    let output = Command::new(BIN).args(args).output()?;
    Ok(Outcome {
        code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

struct Scratch {
    dir: PathBuf,
}

impl Scratch {
    fn new(name: &str) -> io::Result<Scratch> {
        let dir = std::env::temp_dir().join(format!("emd-cli-{name}-{}", std::process::id()));
        if dir.exists() {
            fs::remove_dir_all(&dir)?;
        }
        fs::create_dir_all(&dir)?;
        Ok(Scratch { dir })
    }

    fn write(&self, name: &str, text: &str) -> io::Result<PathBuf> {
        let path = self.dir.join(name);
        fs::write(&path, text)?;
        Ok(path)
    }

    fn absent(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

#[test]
fn public_invocations_replace_kernel_only_usage() -> io::Result<()> {
    let outcome = run::<&str>(&[])?;
    assert_eq!(outcome.code, Some(2));
    assert_eq!(outcome.stdout, "");
    assert!(outcome.stderr.starts_with("Usage: emd COMMAND"));
    for flag in ["--help", "--version"] {
        let outcome = run(&[flag])?;
        assert_eq!(outcome.code, Some(0));
        assert_eq!(outcome.stderr, "");
    }
    Ok(())
}

#[test]
fn kernel_eval_help_prints_its_usage() -> io::Result<()> {
    for flag in ["-h", "--help"] {
        let outcome = run(&["kernel-eval", flag])?;
        assert_eq!(outcome.code, Some(0), "{flag}");
        assert_eq!(outcome.stdout, "Usage: emd kernel-eval FILE\n", "{flag}");
        assert_eq!(outcome.stderr, "", "{flag}");
    }
    Ok(())
}

#[test]
fn kernel_eval_prints_hand_computed_results() -> io::Result<()> {
    let scratch = Scratch::new("cases")?;
    let cases = scratch.write(
        "cases.txt",
        "isqrt 9 -> 0\n\
         intersects (0,0,2,2) (2,0,2,2) -> true\n\
         inflate (0,0,1,1) -1 -> (0,0,0,0)\n",
    )?;
    let outcome = run(&[OsStr::new("kernel-eval"), cases.as_os_str()])?;
    assert_eq!(outcome.code, Some(0));
    assert_eq!(outcome.stdout, "3\nfalse\ndomain\n");
    assert_eq!(outcome.stderr, "");
    Ok(())
}

#[test]
fn kernel_eval_stops_at_the_first_bad_line() -> io::Result<()> {
    let scratch = Scratch::new("bad-line")?;
    let cases = scratch.write(
        "cases.txt",
        "isqrt 9 -> 0\nisqrt 16 -> 0\nfrobnicate 1 -> 2\n",
    )?;
    let outcome = run(&[OsStr::new("kernel-eval"), cases.as_os_str()])?;
    assert_eq!(outcome.code, Some(2));
    assert_eq!(outcome.stdout, "3\n4\n");
    assert_eq!(outcome.stderr, "bad case line 3\n");
    Ok(())
}

#[test]
fn kernel_eval_reports_an_unreadable_file() -> io::Result<()> {
    let scratch = Scratch::new("missing")?;
    let missing = scratch.absent("absent.txt");
    let outcome = run(&[OsStr::new("kernel-eval"), missing.as_os_str()])?;
    assert_eq!(outcome.code, Some(2));
    assert_eq!(outcome.stdout, "");
    let prefix = format!("cannot read {}: ", missing.display());
    assert!(outcome.stderr.starts_with(&prefix), "{}", outcome.stderr);
    assert!(outcome.stderr.ends_with('\n'), "{}", outcome.stderr);
    Ok(())
}

#[test]
fn kernel_eval_accepts_empty_stdin() -> io::Result<()> {
    let outcome = run(&["kernel-eval"])?;
    assert_eq!(outcome.code, Some(0));
    assert_eq!(outcome.stdout, "");
    assert_eq!(outcome.stderr, "");
    Ok(())
}

#[test]
fn kernel_eval_rejects_extra_positionals() -> io::Result<()> {
    let scratch = Scratch::new("extra")?;
    let cases = scratch.write("cases.txt", "isqrt 9 -> 0\n")?;
    let outcome = run(&[
        OsStr::new("kernel-eval"),
        cases.as_os_str(),
        OsStr::new("more"),
    ])?;
    assert_eq!(outcome.code, Some(2));
    assert_eq!(outcome.stdout, "");
    assert_eq!(
        outcome.stderr,
        "unknown flag more; run emd kernel-eval --help\n"
    );
    Ok(())
}

#[test]
fn kernel_eval_accepts_a_path_after_the_terminator() -> io::Result<()> {
    let scratch = Scratch::new("terminator")?;
    let cases = scratch.write("cases.txt", "isqrt 16 -> 0\n")?;
    let outcome = run(&[
        OsStr::new("kernel-eval"),
        OsStr::new("--"),
        cases.as_os_str(),
    ])?;
    assert_eq!(outcome.code, Some(0));
    assert_eq!(outcome.stdout, "4\n");
    Ok(())
}
