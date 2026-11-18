package kanban_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/kanban"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
)

func FuzzKanban(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "kanban", "*", "*.mmd"))
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
		"kanban",
		"kanban\n  root[a",
		"kanban\n  root[\"`never closed",
		"kanban\n  root\n    ::icon(never closed",
		"kanban\n  root@{ ticket: \"open",
		"kanban\n  root@{ ticket: ^ }\n",
		"kanban\n    s[S]\n  a[A]\n    b[B]\n",
		"kanban\n  a[A]@{ shape: Bad_Shape, label: \"\u00e9\n  \u00e9\" }\n",
		"---\ntitle: t\n---\n%%{init: {\"kanban\": {\"sectionWidth\": 120}}}%%\nkanban\r\n  s[S]\r\n    a[A]@{ ticket: 1 }\r    b\r\n",
		"kanban\n\u00a0\u00a0root\u2028\n\t\tchild{{x}}\n:::\n::icon()\n@{}\n",
		"kanban\n  a@{\n    ticket:\n      toString: 1\n}\n",
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
