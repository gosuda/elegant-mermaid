package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/radar"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
)

func TestRadarNoCurves(t *testing.T) {
	for i, text := range []string{"radar-beta\naxis A\n", "radar-beta\naxis A\ncurve c {1}\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "radar/no-curves", Summary: "expected", Help: "help"}
		ds := radarNoCurves(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestRadarCurveLengthMismatch(t *testing.T) {
	for i, text := range []string{
		"radar-beta\naxis A, B\ncurve c {1}\n",
		"radar-beta\naxis A, B\ncurve c {1, 2}\n",
		"radar-beta\naxis A, B\ncurve c {A: 1}\n",
	} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "radar/curve-length-mismatch", Summary: "expected", Help: "help"}
		ds := radarCurveLengthMismatch(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestRadarEmptyCurveRejected(t *testing.T) {
	for _, text := range []string{
		"radar-beta\naxis A, B\ncurve c {}\n",
		"radar-beta\naxis A\ncurve c {\n}\n",
	} {
		_, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) == 0 || diagnostics[0].Code != "radar/unexpected-token" {
			t.Fatalf("%q: expected empty-curve syntax diagnostic, got %+v", text, diagnostics)
		}
		span := diagnostics[0].Span
		if text[span.Start:span.End] != "}" {
			t.Fatalf("%q: empty-curve diagnostic must identify closing brace: %+v", text, diagnostics[0])
		}
	}
}

func TestRadarDuplicateAxis(t *testing.T) {
	for i, text := range []string{"radar-beta\naxis A[\"same\"], B[\"same\"]\n", "radar-beta\naxis A, B\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "radar/duplicate-axis", Summary: "expected", Help: "help"}
		ds := radarDuplicateAxis(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func checkResolvedRuleDiagnostics(t *testing.T, text string, row Row, ds []diag.Diagnostic, want int) {
	t.Helper()
	if len(ds) != want {
		t.Fatalf("%q: got %d diagnostics, want %d", text, len(ds), want)
	}
	for _, d := range ds {
		if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
			t.Fatalf("unexpected diagnostic: %+v", d)
		}
	}
}
