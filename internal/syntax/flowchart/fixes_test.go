package flowchart

import (
	"reflect"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func TestDiagnosticFixContracts(t *testing.T) {
	cases := []struct {
		code, src, title, text         string
		start, end, editStart, editEnd int
		safety                         diag.FixSafety
	}{
		{codeArrowInvalid, "A -> B", "Replace -> with -->", "-->", 2, 4, 2, 4, diag.FixSafe},
		{codeLinkMissing, "A B", "Insert --> between the two nodes", "--> ", 2, 3, 2, 2, diag.FixUnsafe},
		{codeEndWithoutSubgraph, " end\n", "Remove the stray end line", "", 1, 4, 0, 5, diag.FixUnsafe},
		{codeMetaUnsupported, " title foo\n", "Remove the unsupported meta line", "", 1, 10, 0, 11, diag.FixUnsafe},
		{codeUnclosedNodeBracket, "A[foo", "Add the closing bracket", "]", 1, 5, 5, 5, diag.FixUnsafe},
		{codeNodeMixedBrackets, "A(foo]", "Close with the matching bracket", ")", 5, 6, 5, 6, diag.FixSafe},
		{codeNodeEmpty, "A[]", "Remove the empty bracket pair", "", 1, 2, 1, 3, diag.FixSafe},
		{codeLabelEscapedQuote, "A[\"x\\\"y\"]", "Replace the quote with &quot;", "&quot;", 4, 6, 4, 6, diag.FixSafe},
		{codeLabelDoubleInSingle, "A[x\"y]", "Replace the quote with &quot;", "&quot;", 3, 4, 3, 4, diag.FixSafe},
		{"flowchart/label-backtick", "A[x`y]", "Remove the backtick", "", 3, 4, 3, 4, diag.FixSafe},
		{codeDirKeywordInvalid, "graph directionx LR", "Replace the keyword with direction", "direction", 6, 16, 6, 16, diag.FixSafe},
		{"flowchart/dir-missing", "graph", "Insert the default direction TD", " TD", 0, 5, 5, 5, diag.FixSafe},
		{codeLinkUnsupportedMark, "A --x--> B", "Remove the unsupported one-sided marker", "---->", 2, 8, 2, 8, diag.FixUnsafe},
		{codeQuoteUnclosed, "A[\"foo]", "Insert the closing quote", "\"", 2, 7, 6, 6, diag.FixUnsafe},
		{codeLabelQuoteInUnquoted, "A[foo\"bar\"]", "Wrap the label in quotes", "\"foo&quot;bar&quot;\"", 5, 6, 2, 10, diag.FixSafe},
	}
	covered := make(map[string]bool)
	for _, tc := range cases {
		ds := []diag.Diagnostic{{Code: tc.code, Span: source.Span{Start: tc.start, End: tc.end}}}
		attachFixes([]byte(tc.src), ds)
		want := []diag.Fix{{Title: tc.title, Safety: tc.safety, Edits: []diag.Edit{{Span: source.Span{Start: tc.editStart, End: tc.editEnd}, NewText: tc.text}}}}
		if !reflect.DeepEqual(ds[0].Fixes, want) {
			t.Errorf("%s: got %+v want %+v", tc.code, ds[0].Fixes, want)
		}
		covered[tc.code] = true
	}
	checkFixCoverage(t, covered)
}

func checkFixCoverage(t *testing.T, covered map[string]bool) {
	t.Helper()
	for _, row := range gen.Diagnostics {
		assertFixCovered(t, covered, row.Code, row.FixSafety)
	}
	for _, row := range gen.LintRules {
		if row.Status == "adopted" {
			assertFixCovered(t, covered, row.Code, row.FixSafety)
		}
	}
}

func assertFixCovered(t *testing.T, covered map[string]bool, code, safety string) {
	t.Helper()
	if safety != "none" && strings.HasPrefix(code, "flowchart/") && !covered[code] {
		t.Errorf("uncovered diagnostic fix %s", code)
	}
}

func TestParseAttachesFixes(t *testing.T) {
	for _, tc := range []struct{ src, code string }{{"flowchart LR\nA -> B\n", codeArrowInvalid}, {"flowchart LR\nA[Start --> B\n", codeUnclosedNodeBracket}} {
		_, ds := Parse([]byte(tc.src), nil)
		found := false
		for _, d := range ds {
			if d.Code == tc.code {
				found = true
				if len(d.Fixes) != 1 {
					t.Errorf("missing fix: %+v", d)
				}
			}
		}
		if !found {
			t.Fatalf("missing %s: %+v", tc.code, ds)
		}
	}
}
