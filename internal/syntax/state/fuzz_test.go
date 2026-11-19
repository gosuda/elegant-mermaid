package state_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

func FuzzState(f *testing.F) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "fuzz", "corpus", "state", "*.mmd"))
	if err != nil || len(paths) != 4 {
		f.Fatal(paths, err)
	}
	for _, path := range paths {
		src, err := os.ReadFile(path)
		if err != nil {
			f.Fatal(err)
		}
		f.Add(src)
	}
	for _, s := range []string{
		"stateDiagram-v2",
		"stateDiagram\nstate \"unfinished é",
		"stateDiagram\nnote left of A\nfirst\nend note\nnote \"memo\" as F",
		"stateDiagram\naccDescr {first\nsecond}\naccTitle: t\nscale 2 width",
		"stateDiagram\nstate A {\nstate B {\n--\n[*] --> C:::x : go\n}",
		"stateDiagram\nclassDef default fill:red\nclass A,B c\nstyle A fill:blue\nclick A href \"x\"",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		document, _ := source.RepairUTF8(src)
		_, ds := parser.Parse(document, nil)
		for _, d := range ds {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(document) {
				t.Fatal(d)
			}
		}
	})
}
