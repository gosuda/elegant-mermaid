package diag

import (
	"bytes"
	"fmt"
	"io"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func TestTerminalDiagnosticFields(t *testing.T) {
	for r := rune(0); r <= 0x9F; r++ {
		if r >= 0x20 && r < 0x7F {
			continue
		}
		t.Run(fmt.Sprintf("U+%04X", r), func(t *testing.T) {
			checkTerminalDiagnosticScalar(t, "é"+string(r)+"界")
		})
	}
}

func checkTerminalDiagnosticScalar(t *testing.T, field string) {
	t.Helper()
	ds := []Diagnostic{{
		Code: field, Severity: SeverityError, Message: field,
		Span: source.Span{Start: 2, End: 3}, Help: field,
		Fixes:   []Fix{{Title: field}},
		Related: []Related{{Span: source.Span{Start: 0, End: 1}, Message: field}},
	}}
	modes := []terminalDiagnosticMode{
		{"plain", RenderText, "error", "^"},
		{"colour", RenderTextColour, "\x1b[31merror\x1b[0m", "\x1b[31m^\x1b[0m"},
	}
	for _, mode := range modes {
		t.Run(mode.name, func(t *testing.T) {
			checkTerminalDiagnosticFrame(t, field, ds, mode)
		})
	}
}

type terminalDiagnosticMode struct {
	name     string
	render   func(io.Writer, string, []byte, []Diagnostic, FrameOptions) error
	severity string
	mark     string
}

func checkTerminalDiagnosticFrame(t *testing.T, field string, ds []Diagnostic, mode terminalDiagnosticMode) {
	t.Helper()
	var out bytes.Buffer
	if err := mode.render(&out, field, []byte("a\tb"), ds, FrameOptions{}); err != nil {
		t.Fatal(err)
	}
	want := "é�界:1:3: " + mode.severity + "[é�界]: é�界\n" +
		"  |\n1 | a       b\n  |         " + mode.mark + "\n" +
		"  = help: é�界\n  = fix: é�界\n" +
		"  = note: é�界 at é�界:1:1\n"
	if out.String() != want {
		t.Fatalf("got %q want %q", out.String(), want)
	}
	for _, got := range []string{ds[0].Code, ds[0].Message, ds[0].Help, ds[0].Fixes[0].Title, ds[0].Related[0].Message} {
		if got != field {
			t.Fatal("formatter changed diagnostic data")
		}
	}
}
