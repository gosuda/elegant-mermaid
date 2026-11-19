package cli

import (
	"bytes"
	"errors"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

type viewPTYOutput struct {
	mutex   sync.Mutex
	bytes   []byte
	total   int64
	changed chan struct{}
}

func (output *viewPTYOutput) Write(p []byte) (int, error) {
	output.mutex.Lock()
	defer output.mutex.Unlock()
	output.bytes = append(output.bytes, p...)
	output.total += int64(len(p))
	const retained = 1024 * 1024
	if len(output.bytes) > retained {
		output.bytes = output.bytes[len(output.bytes)-retained:]
	}
	select {
	case output.changed <- struct{}{}:
	default:
	}
	return len(p), nil
}

func (output *viewPTYOutput) position() int64 {
	output.mutex.Lock()
	defer output.mutex.Unlock()
	return output.total
}

func (output *viewPTYOutput) containsSince(token string, position int64) bool {
	output.mutex.Lock()
	defer output.mutex.Unlock()
	start := max(0, position-(output.total-int64(len(output.bytes))))
	return bytes.Contains(output.bytes[min(start, int64(len(output.bytes))):], []byte(token))
}

type viewPTYProcess struct {
	cmd     *exec.Cmd
	input   io.WriteCloser
	output  *viewPTYOutput
	done    chan struct{}
	waitErr error
}

func startViewPTY(t *testing.T, path string) *viewPTYProcess {
	t.Helper()
	script, err := exec.LookPath("script")
	if err != nil {
		t.Fatalf("required util-linux script is unavailable: %v", err)
	}
	cmd := exec.CommandContext(t.Context(), script, "-q", "-e", "-f", "-c", `stty cols 80 rows 24; exec "$EMD_BIN" view --graphics cells --color never "$FILE"`, "/dev/null")
	cmd.Env = append(os.Environ(), "EMD_BIN="+viewExecutable(t), "FILE="+path)
	cmd.WaitDelay = time.Second
	input, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	process := &viewPTYProcess{cmd: cmd, input: input, output: &viewPTYOutput{changed: make(chan struct{}, 1)}, done: make(chan struct{})}
	cmd.Stdout = process.output
	cmd.Stderr = process.output
	if err = cmd.Start(); err != nil {
		if closeErr := input.Close(); closeErr != nil {
			t.Log(closeErr)
		}
		t.Fatal(err)
	}
	go func() { process.waitErr = cmd.Wait(); close(process.done) }()
	t.Cleanup(func() { process.cleanup(t) })
	return process
}

func (process *viewPTYProcess) cleanup(t *testing.T) {
	t.Helper()
	if err := process.input.Close(); err != nil {
		t.Logf("close PTY input: %v", err)
	}
	select {
	case <-process.done:
		return
	default:
	}
	if err := process.cmd.Process.Kill(); err != nil && !errors.Is(err, os.ErrProcessDone) {
		t.Errorf("kill PTY process: %v", err)
	}
	timer := time.NewTimer(3 * time.Second)
	defer timer.Stop()
	select {
	case <-process.done:
	case <-timer.C:
		t.Error("PTY process and its output readers did not terminate")
	}
}

func (process *viewPTYProcess) await(t *testing.T, token string, position int64) {
	t.Helper()
	timer := time.NewTimer(10 * time.Second)
	defer timer.Stop()
	for !process.output.containsSince(token, position) {
		select {
		case <-process.output.changed:
		case <-process.done:
			t.Fatalf("viewer exited before fresh %q: %v", token, process.waitErr)
		case <-timer.C:
			t.Fatalf("no fresh %q within 10 seconds", token)
		}
	}
}

func TestViewPTY(t *testing.T) {
	path := filepath.Join(t.TempDir(), "a.mmd")
	writeViewInput(t, path, "flowchart LR\n  A[alpha] --> B\n")
	process := startViewPTY(t, path)
	process.await(t, "alpha", 0)
	mark := process.output.position()
	start := time.Now()
	writeViewInput(t, path, "flowchart LR\n  A[beta] --> B\n")
	writeViewInput(t, path, "flowchart LR\n  A[gamma] --> B\n")
	if elapsed := time.Since(start); elapsed > 50*time.Millisecond {
		t.Fatalf("beta/gamma writes took %v; test requires the 50ms coalescing scenario", elapsed)
	}
	process.await(t, "gamma", mark)
	if _, err := io.WriteString(process.input, "q"); err != nil {
		t.Fatal(err)
	}
	timer := time.NewTimer(10 * time.Second)
	defer timer.Stop()
	select {
	case <-process.done:
		if process.waitErr != nil {
			t.Fatalf("viewer did not exit 0: %v", process.waitErr)
		}
	case <-timer.C:
		t.Fatal("viewer did not exit within 10 seconds after q")
	}
	assertNoViewQueries(t, process.output)
}

func assertNoViewQueries(t *testing.T, output *viewPTYOutput) {
	t.Helper()
	for _, query := range []string{"\x1b[16t", "\x1b[c", "\x1b_Gi=31"} {
		if output.containsSince(query, 0) {
			t.Fatalf("cells viewer sent terminal query %q", query)
		}
	}
}

func viewExecutable(t *testing.T) string {
	t.Helper()
	path := os.Getenv("EMD_BIN")
	if path == "" {
		t.Fatal("EMD_BIN is not set; run just go-check")
	}
	absolute, err := filepath.Abs(path)
	if err != nil {
		t.Fatal(err)
	}
	return absolute
}
