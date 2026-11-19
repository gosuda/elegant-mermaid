package cli

import (
	"bytes"
	"os"
	"strings"
	"testing"
)

func TestLayoutSourceGolden(t *testing.T) {
	want, err := os.ReadFile("../../spec/golden/two-node.layout.json")
	if err != nil {
		t.Fatal(err)
	}
	var out, stderr bytes.Buffer
	err = Run(t.Context(), Config{Args: []string{"layout", "-"}, Stdin: strings.NewReader("flowchart\nA -->|yes| B\n"), Stdout: &out, Stderr: &stderr})
	if err != nil {
		t.Fatalf("layout failed: %v; stderr: %s", err, stderr.String())
	}
	if !bytes.Equal(out.Bytes(), want) {
		t.Fatalf("layout differs from golden\ngot:\n%s\nwant:\n%s", out.Bytes(), want)
	}
	if stderr.Len() != 0 {
		t.Fatalf("unexpected diagnostics: %s", stderr.String())
	}
}
