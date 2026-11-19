package gitgraph_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
)

func FuzzGitgraph(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "gitgraph", "*", "*.mmd"))
	if err != nil {
		f.Fatal(err)
	}
	for i := 0; i < len(paths); i += 9 {
		src, err := os.ReadFile(paths[i])
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"gitGraph",
		"gitGraph:",
		"gitGraph LR:\ncommit id: \"never closed",
		"gitGraph TB:\naccDescr {\nnever closed",
		"gitGraph\ncommit id: \"a\" tag: \"t\" type: HIGHLIGHT\nbranch dev order: 2\ncheckout dev\ncommit\nmerge main",
		"gitGraph\ncommit id: \"a\"\ncommit id: \"a\"\nbranch x\ncherry-pick id: \"a\"",
		"gitGraph BT:\ncommit\nbranch \"q r\"\nswitch \"q r\"\ncommit msg: \"m\"\ncheckout main\nmerge \"q r\" id: \"m\" type: REVERSE",
		"gitGraph\ntitle  x   y\naccTitle: t\naccDescr: d %% c\n%% comment\ncommit %% c",
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
