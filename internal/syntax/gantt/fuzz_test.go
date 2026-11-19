package gantt_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/gantt"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

func FuzzGantt(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(document, start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
		checkTokenSpans(t, document, start)
	})
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "gantt", "*", "*.mmd"))
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
		"gantt",
		"gantt\ndateFormat YYYY-MM-DD\nexcludes weekends\nA :a, 2014-01-03, 3d\nB :after a, 2d\n",
		"gantt\ndateFormat X\nA :a, 1700000000, 1700003600\n",
		"gantt\ndateFormat\naxisFormat %L %Y\ntickInterval 5millisecond\n",
		"gantt\nA :a, after b c, until d\nclick a href \"x\" call f(\"1,2\", 3)\n",
		"gantt\r\ntitle t\rsection \u00a0s\r\n%% c\r\nx : crit, done, 2014-01-01, 99999999999y\r\n",
		"gantt\nA :milestone, m, 2014-01-01, 0d\nB :vert, v, 2014-01-01, 0d\nC :10000y\n",
		"gantt\nexcludes monday tuesday wednesday thursday friday saturday sunday\nA :a, 2014-01-03, 3d\n",
		"gantt\naccTitle:\naccDescr {\nnever closed",
	} {
		f.Add([]byte(s))
	}
}

func checkTokenSpans(t *testing.T, document []byte, start *parser.Start) {
	t.Helper()
	for _, line := range start.Document.Lines {
		inside := line.Span.Start >= 0 && line.Span.Start <= line.Span.End && line.Span.End <= len(document)
		if !inside || !onBoundary(document, line.Span.Start) || !onBoundary(document, line.Span.End) {
			t.Fatalf("line span %v is not a UTF-8 slice of %d bytes", line.Span, len(document))
		}
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
