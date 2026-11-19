package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

func TestXychartMissingXAxis(t *testing.T) {
	for i, text := range []string{"xychart\nbar [1]\n", "xychart\nx-axis [a]\nbar [1]\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "xychart/missing-x-axis", Summary: "expected", Help: "help"}
		ds := xychartMissingXAxis(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestXychartMissingYAxis(t *testing.T) {
	for i, text := range []string{"xychart\nbar [1]\n", "xychart\ny-axis 0 --> 2\nbar [1]\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "xychart/missing-y-axis", Summary: "expected", Help: "help"}
		ds := xychartMissingYAxis(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestXychartNoSeries(t *testing.T) {
	for i, text := range []string{"xychart\n", "xychart\nbar [1]\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		m, _ := model.Resolve([]byte(text), document)
		row := Row{Code: "xychart/no-series", Summary: "expected", Help: "help"}
		ds := xychartNoSeries(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestXychartSeriesLengthMismatch(t *testing.T) {
	for i, text := range []string{"xychart\nx-axis [a, b]\nbar [1]\n", "xychart\nx-axis [a, b]\nbar [1, 2]\n"} {
		document, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("case %d: parse diagnostics: %+v", i, diagnostics)
		}
		row := Row{Code: "xychart/series-length-mismatch", Summary: "expected", Help: "help"}
		m, _ := model.Resolve([]byte(text), document)
		ds := xychartSeriesLengthMismatch(m, row)
		want := 0
		if i == 0 {
			want = 1
		}
		checkResolvedRuleDiagnostics(t, text, row, ds, want)
	}
}

func TestXychartEffectiveDomain(t *testing.T) {
	for _, tc := range []struct {
		text string
		want int
	}{
		{"xychart\nx-axis [a, b]\nx-axis 0 --> 10\nbar [1]\nline [2]\n", 0},
		{"xychart\nx-axis [a, b]\nx-axis 0 --> 10\nbar [1]\nline [2, 3]\n", 1},
		{"xychart\nx-axis [a, b]\nx-axis \"title\"\nbar [1]\n", 1},
		{"xychart\nx-axis [a, b]\nbar [1, 2, 3]\n", 1},
	} {
		document, diagnostics := parser.Parse([]byte(tc.text), nil)
		if len(diagnostics) != 0 {
			t.Fatalf("%q: parse diagnostics: %+v", tc.text, diagnostics)
		}
		m, _ := model.Resolve([]byte(tc.text), document)
		ds := xychartSeriesLengthMismatch(m, Row{Code: "xychart/series-length-mismatch"})
		if len(ds) != tc.want {
			t.Fatalf("%q: got %d diagnostics, want %d", tc.text, len(ds), tc.want)
		}
	}
}

func TestXychartEmptyListsRejected(t *testing.T) {
	for _, text := range []string{
		"xychart\nx-axis []\nbar [1]\n",
		"xychart\nbar []\nline [1]\n",
		"xychart\nbar []\n",
	} {
		_, diagnostics := parser.Parse([]byte(text), nil)
		if len(diagnostics) == 0 || diagnostics[0].Code != "xychart/unexpected-token" {
			t.Fatalf("%q: expected empty-list syntax diagnostic, got %+v", text, diagnostics)
		}
		span := diagnostics[0].Span
		if text[span.Start:span.End] != "]" {
			t.Fatalf("%q: empty-list diagnostic must identify closing bracket: %+v", text, diagnostics[0])
		}
	}
}
