package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
)

func TestEventmodelingUndefinedFrame(t *testing.T) {
	for i, text := range []string{"eventmodeling\ntf 1 cmd A ->> 9\n", "eventmodeling\ntf 9 ui A\ntf 1 cmd B ->> 9\n"} {
		checkEventmodelingUndefinedFrameCase(t, i, text)
	}
}

func TestEventmodelingInvalidFlow(t *testing.T) {
	for i, text := range []string{"eventmodeling\ntf 1 evt A\ntf 2 cmd B ->> 1\n", "eventmodeling\ntf 1 ui A\ntf 2 cmd B ->> 1\n"} {
		checkEventmodelingInvalidFlowCase(t, i, text)
	}
}

func checkEventmodelingUndefinedFrameCase(t *testing.T, i int, text string) {
	t.Helper()
	document, parsed := parser.Parse([]byte(text), nil)
	if len(parsed) != 0 {
		t.Fatalf("fixture did not parse: %+v", parsed)
	}
	row := Row{Code: "eventmodeling/undefined-frame", Summary: "expected", Help: "help"}
	resolved, _ := model.Resolve(document)
	ds := eventmodelingUndefinedFrame(resolved, row)
	want := 0
	if i == 0 {
		want = 1
	}
	if len(ds) != want {
		t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
	}
	for _, d := range ds {
		checkEventmodelingFinding1(t, d, row, text)
	}
}

func checkEventmodelingInvalidFlowCase(t *testing.T, i int, text string) {
	t.Helper()
	document, parsed := parser.Parse([]byte(text), nil)
	if len(parsed) != 0 {
		t.Fatalf("fixture did not parse: %+v", parsed)
	}
	row := Row{Code: "eventmodeling/invalid-flow", Summary: "expected", Help: "help"}
	resolved, _ := model.Resolve(document)
	ds := eventmodelingInvalidFlow(resolved, row)
	want := 0
	if i == 0 {
		want = 1
	}
	if len(ds) != want {
		t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
	}
	for _, d := range ds {
		checkEventmodelingFinding2(t, d, row, text)
	}
}

func checkEventmodelingFinding1(t *testing.T, d diag.Diagnostic, row Row, text string) {
	t.Helper()
	if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("unexpected diagnostic: %+v", d)
	}
}

func checkEventmodelingFinding2(t *testing.T, d diag.Diagnostic, row Row, text string) {
	t.Helper()
	if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("unexpected diagnostic: %+v", d)
	}
}

func TestEventmodelingResolvedEvidence(t *testing.T) {
	text := "eventmodeling\ntf 1 cmd A ->> 9 ->> 8\ntf 9 ui B\nrf 9 evt C\n"
	document, parsed := parser.Parse([]byte(text), nil)
	if len(parsed) != 0 {
		t.Fatalf("fixture did not parse: %+v", parsed)
	}
	m, ds := model.Resolve(document)
	checkDuplicateFrameFinding(t, ds, m)
	if got := eventmodelingUndefinedFrame(m, Row{}); len(got) != 1 {
		t.Fatalf("unresolved reference lost: %+v", got)
	}
	if got := eventmodelingInvalidFlow(m, Row{}); len(got) != 1 {
		t.Fatalf("forward or duplicate source type evidence lost: %+v", got)
	}
}

func checkDuplicateFrameFinding(t *testing.T, ds []diag.Diagnostic, m *model.Model) {
	t.Helper()
	if len(ds) != 1 {
		t.Fatalf("duplicate resolver diagnostic lost: %+v", ds)
	}
	d := ds[0]
	if d.Code != "eventmodeling/duplicate-frame-id" || d.Severity != diag.SeverityError || d.Span != m.Frames[2].Span {
		t.Fatalf("duplicate resolver diagnostic lost: %+v", ds)
	}
	if len(d.Related) != 1 || d.Related[0].Span != m.Frames[1].Span || d.Related[0].Message != "first declared here" {
		t.Fatalf("duplicate resolver diagnostic lost: %+v", ds)
	}
}
