package sankey_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

func FuzzSankey(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
		checkRecordSpans(t, document, start)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "sankey", "*", "*.mmd"))
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
		"sankey",
		"sankey-beta\n",
		"sankey\n\"a,b,1",
		"sankey\na,b,1,2\n\"x\"\"\",y,1e999\n,,\n",
		"sankey\r\n\r\na\r\n,b,c\r\n\"\n\n\"\"\",d,Infinity",
		"sankey\n%% c\n\ta,b,1\né,ü,3",
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

func checkRecordSpans(t *testing.T, document []byte, start *parser.Start) {
	t.Helper()
	for _, r := range start.Csv.Records {
		if r.Span.Start < 0 || r.Span.End < r.Span.Start || r.Span.End > len(document) {
			t.Fatalf("record %d has span %v for %d bytes", r.Index, r.Span, len(document))
		}
	}
}

func onBoundary(text []byte, at int) bool {
	return at == len(text) || utf8.RuneStart(text[at])
}
