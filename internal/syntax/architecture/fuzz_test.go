package architecture_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
)

func FuzzArchitecture(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "architecture", "*", "*.mmd"))
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
		"architecture-beta",
		"architecture-beta\ngroup g(cloud)[G]\nservice a(server)[A] in g\nservice b(logos:aws-s3)\njunction j in g\na:R -[x]- L:b\nalign row a b",
		"architecture-beta\nservice a[never closed",
		"architecture-beta\nservice a(server)\na:R{group} --> L:a\nalign column a",
		"architecture-beta\ngroup g in g\nservice a in missing\nA:R -- L:B",
		"architecture-beta\ntitle t\naccTitle: x\naccDescr {\nmulti\n}\nservice \"quoted\\\"id\"(x)",
		"architecture-beta\nservice a(server)\nservice a(disk)\nalign row a a",
		"---\nconfig:\n  architecture:\n    padding: 99999999999\n    iconSize: 0\n---\narchitecture-beta\nservice a",
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
