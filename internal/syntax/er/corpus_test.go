package er_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

type verdict struct {
	Accept bool `json:"accept"`
}

func TestCorpus(t *testing.T) {
	var verdicts map[string]verdict
	readJSON(t, "corpus/verdicts.json", &verdicts)
	var divergences []struct {
		Path string `json:"path"`
	}
	readJSON(t, "corpus/divergences.json", &divergences)
	skip := make(map[string]bool)
	for _, row := range divergences {
		skip[row.Path] = true
	}
	var paths []string
	for path := range verdicts {
		if strings.HasPrefix(path, "corpus/er/") && !skip[path] {
			paths = append(paths, path)
		}
	}
	slices.Sort(paths)
	for _, path := range paths {
		checkCorpusFile(t, path, verdicts[path])
	}
	t.Logf("compared %d er fixtures", len(paths))
}

func readJSON(t *testing.T, path string, target any) {
	t.Helper()
	raw, err := os.ReadFile(filepath.Join("../../..", path))
	if err != nil {
		t.Fatal(err)
	}
	if err = json.Unmarshal(raw, target); err != nil {
		t.Fatal(err)
	}
}

func checkCorpusFile(t *testing.T, path string, expected verdict) {
	t.Helper()
	src, err := os.ReadFile(filepath.Join("../../..", path))
	if err != nil {
		t.Fatal(err)
	}
	p := syntax.Preprocess(src)
	start, ds := parser.Parse(src, p.Removed)
	_, semantic := ermodel.Resolve(src, start)
	ds = append(ds, semantic...)
	ds = append(ds, p.Diags...)
	accept := !slices.ContainsFunc(ds, func(d diag.Diagnostic) bool { return d.Severity == diag.SeverityError })
	if accept != expected.Accept {
		t.Errorf("%s: accept=%v want=%v diagnostics=%v", path, accept, expected.Accept, ds)
	}
}
