package quadrant_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

func FuzzQuadrant(f *testing.F) {
	seedFuzzCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
	})
}

func seedFuzzCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "quadrant", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for i := 0; i < len(paths); i += 2 {
		src, err := os.ReadFile(paths[i])
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"quadrantChart",
		"quadrantChart\n  x-axis Low --> \n  y-axis --> High\n  quadrant-5 x",
		"quadrantChart\n  A:::cls: [0.5, 0.5] radius: 99999999999999999999\n  classDef cls color: #fff, radius: 3px;",
		"quadrantChart\n  \"unterminated: [0.1, 0.2]",
		"quadrantChart\n  accDescr {\nnever closed",
		"quadrantChart\n  A: [0.1,\n  B: [0.2, 0.3] color: #12",
		"quadrantChart;title #35; x;A: [1, 0.x]",
	} {
		f.Add([]byte(s))
	}
}

func checkSpans(t *testing.T, stage string, document []byte, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(document) {
			t.Fatalf("%s diagnostic %s has span %v for %d bytes", stage, d.Code, d.Span, len(document))
		}
		if !onBoundary(document, d.Span.Start) || !onBoundary(document, d.Span.End) {
			t.Fatalf("%s diagnostic %s span %v splits a UTF-8 sequence", stage, d.Code, d.Span)
		}
	}
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
