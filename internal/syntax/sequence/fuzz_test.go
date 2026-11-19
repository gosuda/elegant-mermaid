package sequence_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
)

func FuzzSequence(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "sequence", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for i := 0; i < len(paths); i += 25 {
		src, err := os.ReadFile(paths[i])
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"sequenceDiagram",
		"sequenceDiagram\nparticipant A@{ \"type\": \"actor\"",
		"sequenceDiagram\naccDescr {\nnever closed",
		"sequenceDiagram\nbox Aqua Team\nparticipant A as \"Alice é\"\nend\nloop x\nA->>+B: y\nelse z\nend",
		"sequenceDiagram\ncreate participant C\nA-->>C: hi\ndestroy C\nC--xA: bye\nautonumber 3 2",
		"sequenceDiagram\nlink A: Dash @ https://x.dev\nlinks A: {\"k\": \"v\"}\nNote over A,B: n #amp; m",
		"sequenceDiagram\npar a\nA->>B: x\nand b\nA-)B: y\nend\ncritical c\noption d\nend\nbreak e\nend\nrect rgb(1,2,3)\nend",
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
