use quanta::Instant;
use std::{
    ffi::OsString,
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc,
    },
    thread::{self, JoinHandle},
    time::Duration,
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> io::Result<Self> {
        let root = std::env::temp_dir().join(format!(
            "emd-view-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root)?;
        Ok(Self(root))
    }
    fn write(&self, name: &str, text: &str) -> io::Result<PathBuf> {
        let path = self.0.join(name);
        fs::write(&path, text)?;
        Ok(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Running {
    child: Child,
    output: Option<mpsc::Receiver<Vec<u8>>>,
    reader: Option<JoinHandle<io::Result<()>>>,
}
impl Running {
    fn spawn(command: &mut Command) -> io::Result<Self> {
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let mut stdout = child
            .stdout
            .take()
            .ok_or_else(|| io::Error::other("missing stdout"))?;
        let (tx, rx) = mpsc::sync_channel(64);
        let reader = thread::spawn(move || {
            let mut bytes = [0; 4096];
            loop {
                let length = stdout.read(&mut bytes)?;
                if length == 0 || tx.send(bytes[..length].to_vec()).is_err() {
                    return Ok(());
                }
            }
        });
        Ok(Self {
            child,
            output: Some(rx),
            reader: Some(reader),
        })
    }
    fn receiver(&self) -> io::Result<&mpsc::Receiver<Vec<u8>>> {
        self.output
            .as_ref()
            .ok_or_else(|| io::Error::other("output closed"))
    }
    fn await_text(&self, needle: &str) -> io::Result<()> {
        let deadline = Instant::now() + Duration::from_secs(10);
        let mut bytes = Vec::new();
        while Instant::now() < deadline {
            let chunk = self
                .receiver()?
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .map_err(|error| {
                    io::Error::other(format!(
                        "waiting for {needle}: {error}; output {}",
                        String::from_utf8_lossy(&bytes)
                    ))
                })?;
            bytes.extend(chunk);
            if bytes
                .windows(needle.len())
                .any(|window| window == needle.as_bytes())
            {
                return Ok(());
            }
            if bytes.len() > 65536 {
                bytes.drain(..bytes.len() - 4096);
            }
        }
        Err(io::Error::other(format!("timed out waiting for {needle}")))
    }
    fn exit(&mut self) -> io::Result<ExitStatus> {
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            if let Some(status) = self.child.try_wait()? {
                return Ok(status);
            }
            if Instant::now() >= deadline {
                return Err(io::Error::other("viewer did not exit within 10 seconds"));
            }
            if let Some(output) = &self.output {
                while output.try_recv().is_ok() {}
            }
            thread::sleep(Duration::from_millis(5));
        }
    }
    fn collect(&mut self) -> io::Result<Vec<u8>> {
        let deadline = Instant::now() + Duration::from_secs(10);
        let mut bytes = Vec::new();
        loop {
            match self.receiver()?.recv_timeout(Duration::from_millis(5)) {
                Ok(chunk) => bytes.extend(chunk),
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
                Err(mpsc::RecvTimeoutError::Timeout) => {}
            }
            if Instant::now() >= deadline {
                return Err(io::Error::other("script replay exceeded 10 seconds"));
            }
        }
        let status = self.exit()?;
        if !status.success() {
            return Err(io::Error::other(format!("viewer exited with {status}")));
        }
        Ok(bytes)
    }
}

fn terminate_descendants(pid: u32) {
    let children =
        fs::read_to_string(format!("/proc/{pid}/task/{pid}/children")).unwrap_or_default();
    for child in children
        .split_whitespace()
        .filter_map(|value| value.parse::<u32>().ok())
    {
        terminate_descendants(child);
        let _ = Command::new("kill")
            .args(["-KILL", &child.to_string()])
            .status();
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        self.output.take();
        self.child.stdin.take();
        if matches!(self.child.try_wait(), Ok(None)) {
            terminate_descendants(self.child.id());
            let _ = self.child.kill();
        }
        let _ = self.child.wait();
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

fn binary() -> OsString {
    std::env::var_os("EMD_BIN").unwrap_or_else(|| OsString::from(env!("CARGO_BIN_EXE_emd")))
}

#[test]
fn view_pty() -> io::Result<()> {
    let scratch = Scratch::new()?;
    let source = scratch.write("a.mmd", "flowchart LR\n  A[alpha] --> B\n")?;
    let executable = fs::canonicalize(binary())?;
    let mut process = Running::spawn(Command::new("script")
        .args(["-q", "-e", "-f", "-c", "stty cols 80 rows 24; exec \"$EMD_BIN\" view --graphics cells --color never \"$FILE\"", "/dev/null"])
        .env("EMD_BIN", executable).env("FILE", &source))?;
    process.await_text("alpha")?;
    while process.receiver()?.try_recv().is_ok() {}
    let changed = Instant::now();
    fs::write(&source, "flowchart LR\n  A[beta] --> B\n")?;
    fs::write(&source, "flowchart LR\n  A[gamma] --> B\n")?;
    assert!(
        changed.elapsed() < Duration::from_millis(50),
        "file writes did not exercise the 50 ms coalescing window"
    );
    process.await_text("gamma")?;
    let quitting = Instant::now();
    process
        .child
        .stdin
        .as_mut()
        .ok_or_else(|| io::Error::other("missing pty input"))?
        .write_all(b"q")?;
    let final_output = process.collect()?;
    assert!(
        quitting.elapsed() < Duration::from_secs(10),
        "view_pty: expected {} to hold (observed false)",
        stringify!(quitting.elapsed() < Duration::from_secs(10))
    );
    assert!(
        final_output.windows(6).any(|bytes| bytes == b"\x1b[?25h"),
        "view_pty: expected {} to hold (observed false)",
        stringify!(final_output.windows(6).any(|bytes| bytes == b"\x1b[?25h"))
    );
    assert!(
        final_output.windows(8).any(|bytes| bytes == b"\x1b[?1049l"),
        "view_pty: expected {} to hold (observed false)",
        stringify!(final_output.windows(8).any(|bytes| bytes == b"\x1b[?1049l"))
    );
    Ok(())
}

fn replay(executable: &Path, source: &Path, script: &Path) -> io::Result<String> {
    let mut process = Running::spawn(
        Command::new(executable)
            .arg("view")
            .arg(source)
            .arg("--script")
            .arg(script)
            .args(["--color", "never", "-t", "elegant-light"]),
    )?;
    String::from_utf8(process.collect()?).map_err(io::Error::other)
}

#[test]
fn view_scripts() -> io::Result<()> {
    let scratch = Scratch::new()?;
    let valid = "flowchart LR\n  A[alpha] --> B\n";
    scratch.write("bad.mmd", "flowchart LR\n A[broken\n")?;
    scratch.write("returned.mmd", "flowchart LR\n A[returned] --> B\n")?;
    let chain = (0..35)
        .map(|index| format!("n{index}[node{index}]"))
        .collect::<Vec<_>>()
        .join(" --> ");
    let large = format!("flowchart LR\n {chain}\n");
    let cases = [
        ("empty", "", "settle\n", 80, 24),
        ("unknown", "not-a-kind\n", "settle\n", 80, 24),
        (
            "first-error",
            "flowchart LR\n A[broken\n",
            "settle\n",
            80,
            24,
        ),
        (
            "stale",
            valid,
            "settle\nfile-change bad.mmd\nsettle\nkey esc\n",
            80,
            24,
        ),
        ("oversize", large.as_str(), "settle\n", 80, 24),
        ("resize", valid, "settle\nresize 40 12\n", 40, 12),
        (
            "recreate",
            valid,
            "settle\nfile-delete\nfile-create returned.mmd\nsettle\n",
            80,
            24,
        ),
        ("keys", valid, "settle\nkey ?\n", 80, 24),
    ];
    let executable = fs::canonicalize(binary())?;
    for (name, source_text, actions, width, height) in cases {
        let source = scratch.write(&format!("{name}.mmd"), source_text)?;
        let script = scratch.write(&format!("{name}.script"), actions)?;
        let output = replay(&executable, &source, &script)?;
        assert_eq!(output.lines().count(), height, "{name}");
        assert!(
            output.lines().all(|line| line.chars().count() == width),
            "{name}"
        );
        assert!(
            !output.bytes().any(|byte| byte == b'\r' || byte == 0x1b),
            "{name}"
        );
        ReplayObservation {
            name,
            frame: &output,
            source: &source,
        }
        .assert_behavior(&scratch, &executable)?;
        if let Some(go) = std::env::var_os("EMD_GO_BIN") {
            let go = fs::canonicalize(go)?;
            assert_eq!(
                output,
                replay(&go, &source, &script)?,
                "cross-language replay: {name}"
            );
        }
    }
    Ok(())
}

struct ReplayObservation<'a> {
    name: &'a str,
    frame: &'a str,
    source: &'a Path,
}

impl ReplayObservation<'_> {
    fn assert_behavior(&self, scratch: &Scratch, executable: &Path) -> io::Result<()> {
        let name = self.name;
        let output = self.frame;
        let source = self.source;
        match name {
            "empty" => {
                assert!(
                    output.contains("Empty diagram:") && !output.contains("+- Diagnostics"),
                    "empty source must show the empty viewport instead of a diagnostic panel: {output}"
                );
                let wide_script = scratch.write("empty-wide.script", "settle\nresize 160 24\n")?;
                let wide = replay(executable, source, &wide_script)?;
                assert_eq!(
                    wide.lines().count(),
                    24,
                    "empty wide frame must retain 24 rows"
                );
                assert!(
                    wide.lines().all(|line| line.chars().count() == 160),
                    "empty wide frame rows must have 160 scalar values: {wide}"
                );
                assert!(
                    wide.contains("E 1 errors W 0 warnings"),
                    "empty revision must retain its single common/empty-source error when counters fit: {wide}"
                );
            }
            "unknown" => {
                assert!(
                    output.contains("Diagnostics") && output.contains("unknown-diagram-kind"),
                    "view_scripts: expected {} to hold (observed false)",
                    stringify!(
                        output.contains("Diagnostics") && output.contains("unknown-diagram-kind")
                    )
                )
            }
            "first-error" => assert!(
                output.contains("Diagnostics")
                    && output.contains("error ")
                    && output.contains("No valid revision yet; fix the source or press r"),
                "first parse error must open diagnostics and identify the absence of a good revision: {output}"
            ),
            "stale" => assert!(
                output.contains("alpha")
                    && !output.contains("broken")
                    && output.contains("STALE revision 1; latest revision 2 has errors"),
                "view_scripts: expected {} to hold (observed false)",
                stringify!(
                    output.contains("alpha")
                        && !output.contains("broken")
                        && output.contains("STALE revision 1; latest revision 2 has errors")
                )
            ),
            "oversize" => assert!(
                output.contains("pan available"),
                "view_scripts: expected {} to hold (observed false)",
                stringify!(output.contains("pan available"))
            ),
            "resize" => assert!(
                output.contains("alpha"),
                "view_scripts: expected {} to hold (observed false)",
                stringify!(output.contains("alpha"))
            ),
            "recreate" => assert!(
                output.contains("returned") && !output.contains("WATCH LOST"),
                "view_scripts: expected {} to hold (observed false)",
                stringify!(output.contains("returned") && !output.contains("WATCH LOST"))
            ),
            "keys" => assert!(
                output.contains("Keys") && output.contains("next, previous block"),
                "view_scripts: expected {} to hold (observed false)",
                stringify!(output.contains("Keys") && output.contains("next, previous block"))
            ),
            _ => return Err(io::Error::other(format!("unrecognised replay case {name}"))),
        }
        Ok(())
    }
}
