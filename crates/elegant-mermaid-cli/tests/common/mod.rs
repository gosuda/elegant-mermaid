//! One stdin drain for every CLI integration test.
//!
//! A child that rejects its flags exits without reading stdin, so the write
//! can fail with `BrokenPipe` while the child already holds the verdict.
//! That verdict is the test subject, not the write, so a broken pipe is
//! tolerated exactly when the child then exits unsuccessfully. Any other
//! write error, or a broken pipe from a child that reports success (its
//! input was silently truncated), is returned to the caller.

use std::io::Write;
use std::process::{Command, Output};

/// Spawn `cmd`, which must leave stdin, stdout and stderr piped, feed it
/// `stdin_bytes`, close the pipe, and collect its output.
pub fn run_with_stdin(mut cmd: Command, stdin_bytes: &[u8]) -> std::io::Result<Output> {
    let mut child = cmd.spawn()?;
    let mut stdin = child
        .stdin
        .take()
        .ok_or_else(|| std::io::Error::other("missing stdin"))?;
    let write = stdin.write_all(stdin_bytes);
    drop(stdin);
    match write {
        Ok(()) => child.wait_with_output(),
        Err(err) => {
            let output = child.wait_with_output()?;
            if err.kind() == std::io::ErrorKind::BrokenPipe && !output.status.success() {
                Ok(output)
            } else {
                Err(err)
            }
        }
    }
}
