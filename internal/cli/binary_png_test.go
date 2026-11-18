package cli_test

import (
	"bytes"
	"context"
	"image/png"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

const pngTerminalMessage = "cannot write PNG to a terminal; use -o FILE.png or redirect stdout to a file"

func TestBinaryPNGPipe(t *testing.T) {
	cmd := binaryCommand(t, "render", "-e", "png", "-s", "1")
	cmd.Stdin = bytes.NewReader([]byte("flowchart LR\n A --> B\n"))
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil || stderr.Len() != 0 {
		t.Fatalf("err=%v stderr=%q", err, stderr.String())
	}
	img, err := png.Decode(bytes.NewReader(out))
	if err != nil || img.Bounds().Empty() {
		t.Fatalf("stdout is not a PNG: %v", err)
	}
}

func TestBinaryPNGFile(t *testing.T) {
	path := filepath.Join(t.TempDir(), "out.png")
	binaryOutput(t, binaryCommand(t, "render", "-o", path, "-s", "3"), "flowchart LR\n A --> B\n", "", "", 0)
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := png.Decode(bytes.NewReader(data)); err != nil {
		t.Fatalf("%s is not a PNG: %v", path, err)
	}
}

func TestBinaryPNGDevNull(t *testing.T) {
	null, err := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = null.Close() })
	cmd := binaryCommand(t, "render", "-e", "png")
	cmd.Stdin = bytes.NewReader([]byte("flowchart LR\n A --> B\n"))
	var stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = null, &stderr
	if err := cmd.Run(); err != nil || stderr.Len() != 0 {
		t.Fatalf("a redirect to %s is not a terminal: err=%v stderr=%q", os.DevNull, err, stderr.String())
	}
}

func TestBinaryPNGTerminal(t *testing.T) {
	source := filepath.Join(t.TempDir(), "a.mmd")
	if err := os.WriteFile(source, []byte("flowchart LR\n A --> B\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, "script", "-qec", "\"$EMD_BIN\" render -e png \"$SOURCE\"", "/dev/null")
	cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "TERM=xterm", "EMD_BIN=" + binaryPath(t), "SOURCE=" + source}
	binaryOutput(t, cmd, "", pngTerminalMessage+"\r\n", "", 2)
}

func TestBinaryPNGFileOnTerminal(t *testing.T) {
	dir := t.TempDir()
	source, output := filepath.Join(dir, "a.mmd"), filepath.Join(dir, "a.png")
	if err := os.WriteFile(source, []byte("flowchart LR\n A --> B\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, "script", "-qec", "\"$EMD_BIN\" render \"$SOURCE\" -o \"$OUTPUT\"", "/dev/null")
	cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "TERM=xterm", "EMD_BIN=" + binaryPath(t), "SOURCE=" + source, "OUTPUT=" + output}
	binaryOutput(t, cmd, "", "", "", 0)
	data, err := os.ReadFile(output)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := png.Decode(bytes.NewReader(data)); err != nil {
		t.Fatalf("%s is not a PNG: %v", output, err)
	}
}
