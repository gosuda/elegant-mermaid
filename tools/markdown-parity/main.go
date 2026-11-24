// Compare actual CLI artifacts, including raw host bytes and filesystem paths.
package main

import (
	"bytes"
	"errors"
	"fmt"
	"io/fs"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

type result struct {
	code           int
	stdout, stderr string
	entries        map[string]string
}

func main() {
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, "markdown-parity:", err)
		os.Exit(1)
	}
}

func run(args []string) error {
	if len(args) == 0 {
		args = []string{"bin/emd-go", "bin/emd-rs"}
	}
	if len(args) != 2 {
		return errors.New("usage: markdown-parity [GO_BINARY RUST_BINARY]")
	}
	binaries := make([]string, len(args))
	for i, path := range args {
		absolute, err := filepath.Abs(path)
		if err != nil {
			return err
		}
		binaries[i] = absolute
	}
	fixtures := cases()
	for _, fixture := range fixtures {
		if err := compare(fixture, binaries); err != nil {
			return fmt.Errorf("%s: %w", fixture.name, err)
		}
	}
	fmt.Printf("markdown-parity: %d cases, identical status, diagnostics, files, and links\n", len(fixtures))
	return nil
}

func compare(fixture testCase, binaries []string) error {
	left, err := execute(fixture, binaries[0])
	if err != nil {
		return fmt.Errorf("Go: %w", err)
	}
	right, err := execute(fixture, binaries[1])
	if err != nil {
		return fmt.Errorf("Rust: %w", err)
	}
	if left.code != right.code || left.stdout != right.stdout || left.stderr != right.stderr {
		return fmt.Errorf("process differs: Go=(%d, %q, %q) Rust=(%d, %q, %q)", left.code, left.stdout, left.stderr, right.code, right.stdout, right.stderr)
	}
	if !maps.Equal(left.entries, right.entries) {
		return errors.New("output directory entries or file bytes differ")
	}
	return nil
}

func execute(fixture testCase, binary string) (_ result, err error) {
	directory, err := os.MkdirTemp("", "emd-markdown-parity-*")
	if err != nil {
		return result{}, err
	}
	defer func() { err = errors.Join(err, os.RemoveAll(directory)) }()
	if err := fixture.setup(directory); err != nil {
		return result{}, err
	}
	command := exec.Command(binary, append([]string{"render", "input.md", "--color", "never"}, fixture.args...)...)
	command.Dir = directory
	var stdout, stderr bytes.Buffer
	command.Stdout, command.Stderr = &stdout, &stderr
	err = command.Run()
	code := 0
	if exit, ok := errors.AsType[*exec.ExitError](err); ok {
		code = exit.ExitCode()
	} else if err != nil {
		return result{}, err
	}
	if code != fixture.code || stdout.Len() != 0 {
		return result{}, fmt.Errorf("exit=%d, stdout=%q, stderr=%q; expected exit=%d and empty stdout", code, stdout.String(), stderr.String(), fixture.code)
	}
	entries, err := snapshot(directory)
	if err != nil {
		return result{}, err
	}
	if err := fixture.check(entries); err != nil {
		return result{}, err
	}
	return result{code: code, stdout: stdout.String(), stderr: stderr.String(), entries: entries}, nil
}

func snapshot(root string) (map[string]string, error) {
	entries := make(map[string]string)
	err := filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		relative, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		value, err := entryValue(path, entry)
		if err != nil {
			return err
		}
		entries[filepath.ToSlash(relative)] = value
		return nil
	})
	return entries, err
}

func entryValue(path string, entry fs.DirEntry) (string, error) {
	if entry.IsDir() {
		return "directory", nil
	}
	if entry.Type()&os.ModeSymlink != 0 {
		target, err := os.Readlink(path)
		return "link:" + target, err
	}
	data, err := os.ReadFile(path)
	return "file:" + string(data), err
}

func writeFixtureFile(root, path, contents string) error {
	path = filepath.Join(root, path)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, []byte(contents), 0o644)
}

func (fixture testCase) setup(root string) error {
	for path, text := range fixture.files {
		if err := writeFixtureFile(root, path, text); err != nil {
			return err
		}
	}
	for path, target := range fixture.links {
		if err := os.Symlink(target, filepath.Join(root, path)); err != nil {
			return err
		}
	}
	return nil
}

func (fixture testCase) check(entries map[string]string) error {
	for path, text := range fixture.files {
		if _, replaced := fixture.hosts[path]; !replaced && entries[path] != "file:"+text {
			return fmt.Errorf("modified existing file %s", path)
		}
	}
	for _, path := range fixture.absent {
		if _, exists := entries[path]; exists {
			return fmt.Errorf("unexpected output %s", path)
		}
	}
	return fixture.checkArtifacts(entries)
}

func (fixture testCase) checkArtifacts(entries map[string]string) error {
	for path, prefix := range fixture.images {
		value := entries[path]
		if value == "file:" || !strings.HasPrefix(value, "file:"+prefix) {
			return fmt.Errorf("missing or invalid artifact %s", path)
		}
	}
	for path, text := range fixture.hosts {
		if entries[path] != "file:"+text {
			return fmt.Errorf("host %s: got %q, want %q", path, entries[path], "file:"+text)
		}
	}
	return nil
}
