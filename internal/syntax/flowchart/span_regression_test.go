package flowchart

import "testing"

func TestQuotedTokenSpans(t *testing.T) {
	for _, tc := range []struct {
		source, code string
		start, end   int
	}{
		{"0\"0\"`0\"\"0", codeLinkMissing, 1, 4},
		{"\"\"", codeUnknownStatement, 0, 2},
		{"\"00000\"0", codeUnknownStatement, 0, 8},
	} {
		_, diagnostics := Parse([]byte(tc.source), nil)
		if len(diagnostics) != 1 || diagnostics[0].Code != tc.code || diagnostics[0].Span.Start != tc.start || diagnostics[0].Span.End != tc.end {
			t.Fatalf("%q: %+v", tc.source, diagnostics)
		}
		lexer := newLexer([]byte(tc.source), nil)
		for _, token := range lexer.lexAll() {
			if token.Span.Start < 0 || token.Span.End < token.Span.Start || token.Span.End > len(tc.source) {
				t.Fatalf("invalid token: %+v", token)
			}
		}
	}
}

func TestInvalidDirectionSpan(t *testing.T) {
	_, diagnostics := Parse([]byte("flowchart XY\n A --> B\n"), nil)
	if len(diagnostics) != 1 || diagnostics[0].Code != codeDirInvalid || diagnostics[0].Span.Start != 10 || diagnostics[0].Span.End != 12 || len(diagnostics[0].Fixes) != 0 {
		t.Fatalf("invalid direction diagnostic: %+v", diagnostics)
	}
}
