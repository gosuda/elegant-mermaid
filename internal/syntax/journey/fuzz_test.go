package journey_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/journey"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

func FuzzJourney(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
		checkTree(t, document, start)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "journey", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for _, path := range paths {
		src, err := os.ReadFile(path)
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"journey",
		"journey\naccDescr {\nnever closed",
		"journey\ntitle t\nsection s\n  a: 5: x, y\n  b: 0\n  c: 99999999999999999999\n  d: +3:\n  e\n  ; f: 3\n  : g",
		"journey\r\nA: 3: Me\r\n%% c\r\nB:\r\n",
		"journey\naccTitle:\naccDescr:\n\u00a0title\u00a0x\nsection\u2028y: 1: \u00e9",
		"journey\nA: 3: M%%{init: {}}%%e\nx%%y\n",
	} {
		f.Add([]byte(s))
	}
}

func checkSpans(t *testing.T, stage string, document []byte, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		checkSpan(t, stage+" diagnostic "+d.Code, document, d.Span)
	}
}

func checkSpan(t *testing.T, what string, document []byte, span source.Span) {
	t.Helper()
	if span.Start < 0 || span.End < span.Start || span.End > len(document) {
		t.Fatalf("%s has span %v for %d bytes", what, span, len(document))
	}
	if !onBoundary(document, span.Start) || !onBoundary(document, span.End) {
		t.Fatalf("%s span %v splits a UTF-8 sequence", what, span)
	}
}

func checkTree(t *testing.T, document []byte, start *parser.Start) {
	t.Helper()
	checkSpan(t, "start", document, start.Span)
	checkSpan(t, "document", document, start.Document.Span)
	for _, line := range start.Document.Lines {
		checkSpan(t, "line", document, line.Span)
		if line.Statement != nil {
			checkSpan(t, "statement", document, line.Statement.Span)
		}
	}
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
