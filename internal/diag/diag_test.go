package diag

import (
	"bytes"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func render(t *testing.T, src string, ds []Diagnostic, o FrameOptions) string {
	t.Helper()
	var buf bytes.Buffer
	if err := RenderText(&buf, "a.mmd", []byte(src), ds, o); err != nil {
		t.Fatalf("RenderText: %v", err)
	}
	return buf.String()
}

func renderColour(t *testing.T, src string, ds []Diagnostic, o FrameOptions) string {
	t.Helper()
	var buf bytes.Buffer
	if err := RenderTextColour(&buf, "a.mmd", []byte(src), ds, o); err != nil {
		t.Fatalf("RenderTextColour: %v", err)
	}
	return buf.String()
}

func frameSample() []Diagnostic {
	return []Diagnostic{{
		Code:     "flowchart/x",
		Severity: SeverityError,
		Message:  "bad token",
		Span:     source.Span{Start: 5, End: 7},
		Related:  []Related{{Span: source.Span{Start: 0, End: 1}, Message: "first declared here"}},
		Help:     "Use -->.",
		Fixes:    []Fix{{Title: "Insert -->", Safety: FixSafe}},
	}}
}

func TestRenderTextFrame(t *testing.T) {
	want := "a.mmd:2:2: error[flowchart/x]: bad token\n" +
		"  |\n" +
		"2 | def\n" +
		"  |  ^~\n" +
		"  = help: Use -->.\n" +
		"  = fix: Insert -->\n" +
		"  = note: first declared here at a.mmd:1:1\n"
	if got := render(t, "abc\ndef\n", frameSample(), FrameOptions{}); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestRenderTextOmitsEmptyNotes(t *testing.T) {
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityInfo, Message: "m", Span: source.Span{Start: 1, End: 2}}}
	want := "a.mmd:1:2: info[c/x]: m\n  |\n1 | abc\n  |  ^\n"
	if got := render(t, "abc", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestRenderTextSeparatesDiagnostics(t *testing.T) {
	ds := []Diagnostic{
		{Code: "c/a", Severity: SeverityError, Message: "first", Span: source.Span{Start: 0, End: 0}},
		{Code: "c/b", Severity: SeverityWarning, Message: "second", Span: source.Span{Start: 0, End: 0}},
	}
	want := "a.mmd:1:1: error[c/a]: first\n  |\n1 | x\n  | ^\n" +
		"\n" +
		"a.mmd:1:1: warning[c/b]: second\n  |\n1 | x\n  | ^\n"
	if got := render(t, "x", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestRenderTextColourWrapsSeverityAndMark(t *testing.T) {
	want := "a.mmd:2:2: \x1b[31merror\x1b[0m[flowchart/x]: bad token\n" +
		"  |\n" +
		"2 | def\n" +
		"  |  \x1b[31m^~\x1b[0m\n" +
		"  = help: Use -->.\n" +
		"  = fix: Insert -->\n" +
		"  = note: first declared here at a.mmd:1:1\n"
	if got := renderColour(t, "abc\ndef\n", frameSample(), FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestRenderTextSeverityColours(t *testing.T) {
	cases := []struct {
		severity Severity
		sgr      string
	}{
		{SeverityError, "\x1b[31m"},
		{SeverityWarning, "\x1b[33m"},
		{SeverityInfo, "\x1b[36m"},
	}
	for _, c := range cases {
		ds := []Diagnostic{{Code: "c/x", Severity: c.severity, Message: "m", Span: source.Span{Start: 0, End: 1}}}
		got := renderColour(t, "x", ds, FrameOptions{})
		if !strings.Contains(got, c.sgr+c.severity.String()+"\x1b[0m") {
			t.Errorf("%s: got %q", c.severity, got)
		}
	}
}

func TestRenderTextExpandsTabs(t *testing.T) {
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityError, Message: "m", Span: source.Span{Start: 2, End: 3}}}
	want := "a.mmd:1:3: error[c/x]: m\n  |\n1 | a       b\n  |         ^\n"
	if got := render(t, "a\tb", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestRenderTextReplacesControlCharacters(t *testing.T) {
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityError, Message: "m", Span: source.Span{Start: 1, End: 2}}}
	want := "a.mmd:1:2: error[c/x]: m\n  |\n1 | a\uFFFDb\n  |  ^\n"
	if got := render(t, "a\x01b", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestRenderTextHonoursCustomWidth(t *testing.T) {
	wide := func(r rune) int {
		if r == '世' {
			return 2
		}
		return 1
	}
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityError, Message: "m", Span: source.Span{Start: 3, End: 4}}}
	want := "a.mmd:1:2: error[c/x]: m\n  |\n1 | 世b\n  |   ^\n"
	if got := render(t, "世b", ds, FrameOptions{Width: wide}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestRenderTextMultiLineSpanStopsAtFirstLineEnd(t *testing.T) {
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityError, Message: "m", Span: source.Span{Start: 1, End: 6}}}
	want := "a.mmd:1:2: error[c/x]: m\n  |\n1 | abc\n  |  ^~\n"
	if got := render(t, "abc\ndef", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestRenderTextWidensGutter(t *testing.T) {
	src := strings.Repeat("\n", 9) + "x\n"
	ds := []Diagnostic{{Code: "c/x", Severity: SeverityError, Message: "m", Span: source.Span{Start: 9, End: 10}}}
	want := "a.mmd:10:1: error[c/x]: m\n   |\n10 | x\n   | ^\n"
	if got := render(t, src, ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestAppendStringEscapes(t *testing.T) {
	cases := []struct {
		in   string
		want string
	}{
		{"plain", `"plain"`},
		{`a"b\c`, `"a\"b\\c"`},
		{"\b\t\n\f\r", `"\b\t\n\f\r"`},
		{"\x00\x1f", `"\u0000\u001f"`},
		{"é世😀\u007f/", "\"é世😀\u007f/\""},
	}
	for _, c := range cases {
		if got := string(AppendString(nil, c.in)); got != c.want {
			t.Errorf("%q: got %s want %s", c.in, got, c.want)
		}
	}
}

func TestAppendDiagnosticJSONKeyOrderAndEscaping(t *testing.T) {
	src := []byte("xyz")
	ix := source.NewIndex(src)
	d := Diagnostic{
		Code:     "a/b",
		Severity: SeverityWarning,
		Message:  "he said \"hi\"\tand \\ there\x01",
		Span:     source.Span{Start: 0, End: 2},
		Related:  []Related{{Span: source.Span{Start: 2, End: 2}, Message: "r"}},
		Fixes: []Fix{{
			Title:  "f",
			Safety: FixUnsafe,
			Edits:  []Edit{{Span: source.Span{Start: 0, End: 1}, NewText: "q\n"}},
		}},
	}
	want := `{"code":"a/b","severity":"warning","message":"he said \"hi\"\tand \\ there\u0001",` +
		`"span":{"start":0,"end":2},"line":1,"column":1,"end_line":1,"end_column":3,` +
		`"related":[{"span":{"start":2,"end":2},"line":1,"column":3,"message":"r"}],` +
		`"help":"","fixes":[{"title":"f","safety":"unsafe",` +
		`"edits":[{"span":{"start":0,"end":1},"new_text":"q\n"}]}]}`
	if got := string(AppendDiagnosticJSON(nil, ix, d)); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestAppendDiagnosticJSONEmptyCollections(t *testing.T) {
	ix := source.NewIndex(nil)
	d := Diagnostic{Code: "c/x", Severity: SeverityInfo, Message: "m", Span: source.Span{}}
	want := `{"code":"c/x","severity":"info","message":"m","span":{"start":0,"end":0},` +
		`"line":1,"column":1,"end_line":1,"end_column":1,"related":[],"help":"","fixes":[]}`
	if got := string(AppendDiagnosticJSON(nil, ix, d)); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestRenderTextKeepsEmptyNoteLine(t *testing.T) {
	ds := []Diagnostic{{
		Code:     "c/x",
		Severity: SeverityError,
		Message:  "m",
		Span:     source.Span{Start: 0, End: 0},
		Related:  []Related{{Span: source.Span{Start: 0, End: 0}, Message: ""}},
	}}
	want := "a.mmd:1:1: error[c/x]: m\n  |\n1 | x\n  | ^\n" +
		"  = note:  at a.mmd:1:1\n"
	if got := render(t, "x", ds, FrameOptions{}); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestSortOrdersByStartThenCode(t *testing.T) {
	ds := []Diagnostic{
		{Code: "b/one", Span: source.Span{Start: 4, End: 5}},
		{Code: "a/two", Span: source.Span{Start: 0, End: 2}},
		{Code: "a/one", Span: source.Span{Start: 0, End: 2}},
		{Code: "c/zero", Span: source.Span{Start: 0, End: 0}},
	}
	Sort(ds)
	codes := make([]string, len(ds))
	for i := range ds {
		codes[i] = ds[i].Code
	}
	want := []string{"a/one", "a/two", "c/zero", "b/one"}
	for i := range want {
		if codes[i] != want[i] {
			t.Fatalf("got %v want %v", codes, want)
		}
	}
}

func TestSortKeepsEmissionOrderOnTies(t *testing.T) {
	ds := []Diagnostic{
		{Code: "a/x", Message: "first", Span: source.Span{Start: 1, End: 1}},
		{Code: "a/x", Message: "second", Span: source.Span{Start: 1, End: 1}},
	}
	Sort(ds)
	if ds[0].Message != "first" || ds[1].Message != "second" {
		t.Fatalf("got %q then %q", ds[0].Message, ds[1].Message)
	}
}
