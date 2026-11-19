package packet_test

import (
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/packet"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
)

func FuzzPacket(f *testing.F) {
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
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "packet", "*", "*.mmd"))
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
		"packet",
		"packet-beta",
		"packet\n0-3: \"never closed",
		"packet\naccDescr {\nnever closed",
		"packet\n0-3: \"a\\",
		"packet\n0-63: \"wide\"\n64: 'x'\n+8: \"y\"",
		"packet\n8-4: \"x\"",
		"packet\n0-3: \"a\"\n5: \"b\"",
		"packet\n0-3: \"a\"\n+0: \"b\"",
		"---\nconfig:\n  packet:\n    bitsPerRow: 1\n    bitOrder: descending\n---\npacket\n0-99999: \"x\"",
		"packet\ntitle  x   y\naccTitle: t\naccDescr: d %% c\n%% comment\n0: \"x\" %% c",
		"packet\n0.5: \"x\"\n01-3: \"y\"\n-3: \"z\"\n+: \"w\"",
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
