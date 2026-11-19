package eventmodeling_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
)

func FuzzEventmodeling(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		ast, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(ast)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "eventmodeling", "*", "*.mmd"))
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
	data, err := os.ReadFile(filepath.Join("..", "..", "..", "spec", "golden", "eventmodeling", "syntax-cases.json"))
	if err != nil {
		f.Fatal(err)
	}
	var cases []verdictCase
	if err := json.Unmarshal(data, &cases); err != nil {
		f.Fatal(err)
	}
	for _, c := range cases {
		f.Add([]byte(c.Source))
	}
}

func checkSpans(t *testing.T, stage string, document []byte, ds []diag.Diagnostic) {
	t.Helper()
	for _, d := range ds {
		if !spanWithin(d.Span, len(document)) {
			t.Fatalf("%s diagnostic %s has span %v for %d bytes", stage, d.Code, d.Span, len(document))
		}
		if !onBoundary(document, d.Span.Start) || !onBoundary(document, d.Span.End) {
			t.Fatalf("%s diagnostic %s span %v splits a UTF-8 sequence", stage, d.Code, d.Span)
		}
		for _, related := range d.Related {
			if !spanWithin(related.Span, len(document)) {
				t.Fatalf("%s diagnostic %s has related span %v for %d bytes", stage, d.Code, related.Span, len(document))
			}
		}
	}
}

func spanWithin(span source.Span, size int) bool {
	return span.Start >= 0 && span.End >= span.Start && span.End <= size
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
