package pie_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/pie"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
)

func FuzzPie(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "pie", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for i := 0; i < len(paths); i += 3 {
		src, err := os.ReadFile(paths[i])
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"pie",
		"pie showData",
		"pie\n\"never closed",
		"pie\naccDescr {\nnever closed",
		"pie title x\n\"a\" : 1\n\"b\" : -2\n\"a\" : 3",
		"pie\n\"a\" : 1.5\n'b' : 007\n\"c\" : 1.",
		"pie showData\ntitle  x   y\naccTitle: t\naccDescr: d %% c\n%% comment\n\"a\\\"b\" : 0.0004",
		"---\nconfig:\n  pie:\n    donutHole: 0.4\n    textPosition: 2\n---\npie\n\"a\" : 99999999999",
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
