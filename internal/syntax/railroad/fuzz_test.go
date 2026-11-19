package railroad_test

import (
	"errors"
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	model "github.com/gosuda/elegant-mermaid/internal/model/railroad"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/railroad"
)

func FuzzRailroad(f *testing.F) {
	seedCorpus(f)
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		prep := syntax.Preprocess(document)
		start, parsed := parser.Parse(document, prep.Removed)
		_, resolved := model.Resolve(start)
		checkSpans(t, "parser", document, parsed)
		checkSpans(t, "resolver", document, resolved)
		checkLayout(t, document)
	})
}

func checkLayout(t *testing.T, document []byte) {
	t.Helper()
	d := layout.ParseDiagram(document)
	if d.Kind != "railroad" {
		return
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in, err := d.Input(profile, scene.Options{})
		if err != nil {
			t.Fatalf("%v input: %v", profile, err)
		}
		s, _, err := layout.Layout(in)
		if errors.Is(err, geom.ErrOverflow) || errors.Is(err, layered.ErrTooLarge) {
			continue
		}
		if err != nil {
			t.Fatalf("%v layout: %v", profile, err)
		}
		if clause, failed, err := s.Validate(); err != nil || failed {
			t.Fatalf("%v layout violates %v: %v", profile, clause, err)
		}
	}
}

func seedCorpus(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "railroad", "*", "*.mmd"))
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
		"railroad-beta",
		"railroad-beta\ntitle \"t\"\naccDescr {\nnever closed",
		"railroad-beta\nr = choice(terminal(\"a\\n\"), sequence(special('x'), zeroOrMore(nonterminal(\"r\")))) ;\nbad = sequence( ;",
		"railroad-ebnf-beta\nr ::= a, (b | c)* - d | [e] , { f } , ? g ? , \"h\" + ; (* c *) /* d */\ns = r ;",
		"railroad-abnf-beta\nr = 1*3a / 2[b c] / *(d / e) / %x41-5A / \"q\" ; ; comment\ns = 0*1r ;",
		"railroad-peg-beta\nr <- &a !(b / c)+ d? e* . \"x\" # note\n / f ;",
		"railroad-beta\n---\nx\n---\nr = optional(terminal(\"a\")) ; %% c\n",
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
