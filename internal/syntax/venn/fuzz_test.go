package venn_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/venn"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

func FuzzVenn(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "venn", "*", "*.mmd"))
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
		"venn-beta",
		"venn-beta\n  set A[\"x\n",
		"venn-beta\n  set A\n  set B\n  union A,B[ x ]:2\n  text A,B \"y\"[z]\n  style A,B fill:rgb(1,2,3), c:\"d\"",
		"venn-beta\n\n  title a\n\tset \"b\"%% c\n union \"b\",x\n  text 5\n",
		"venn-beta set A set B set C set D union A,B,C style A color:#abcdefabc",
		"---\ntitle: t\n---\nvenn-beta\r  set A\r  text x\r%%{init: {}}%%",
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
		checkRelatedSpans(t, stage, document, d)
	}
}

func checkRelatedSpans(t *testing.T, stage string, document []byte, d diag.Diagnostic) {
	t.Helper()
	for _, r := range d.Related {
		if r.Span.Start < 0 || r.Span.End < r.Span.Start || r.Span.End > len(document) {
			t.Fatalf("%s diagnostic %s has related span %v for %d bytes", stage, d.Code, r.Span, len(document))
		}
	}
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
