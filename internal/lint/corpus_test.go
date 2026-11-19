package lint

import (
	"encoding/json"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
)

const corpusDir = "../../corpus"

var maidGaps = map[string]string{}

type upstreamVerdict struct {
	Accept bool `json:"accept"`
}

func loadVerdicts(t *testing.T) map[string]upstreamVerdict {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(corpusDir, "verdicts.json"))
	require.NoError(t, err)
	var verdicts map[string]upstreamVerdict
	require.NoError(t, json.Unmarshal(data, &verdicts))
	return verdicts
}

func gapReason(rel string, d *layout.Diagram) string {
	if reason, ok := maidGaps[rel]; ok {
		return reason
	}
	if d.Found && !d.Supported() {
		return "the Go engine has no parser for kind " + d.Kind + " yet"
	}
	return ""
}

func countAtLeast(ds []diag.Diagnostic, threshold diag.Severity) int {
	n := 0
	for _, d := range ds {
		if d.Severity <= threshold {
			n++
		}
	}
	return n
}

func TestMaidInvalidDiagnosed(t *testing.T) {
	verdicts := loadVerdicts(t)
	paths, err := filepath.Glob(filepath.Join(corpusDir, "*", "maid", "invalid", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		rel := "corpus/" + strings.TrimPrefix(filepath.ToSlash(path), corpusDir+"/")
		verdict, ok := verdicts[rel]
		require.True(t, ok, "%s has no upstream verdict", rel)
		t.Run(rel, func(t *testing.T) {
			src, err := os.ReadFile(path)
			require.NoError(t, err)
			d := layout.ParseDiagram(src)
			threshold := diag.SeverityError
			if verdict.Accept {
				threshold = diag.SeverityWarning
			}
			found := countAtLeast(Run(AnalyzeDiagram(d), Config{}).All(), threshold)
			if reason := gapReason(rel, d); reason != "" {
				require.Zero(t, found, "the gap is closed; remove it from the gap list: %s", reason)
				t.Skip(reason)
			}
			require.Positive(t, found, "want a %s diagnostic or worse (upstream accept=%v)", threshold, verdict.Accept)
		})
	}
}

func corpusSources(t *testing.T) []string {
	t.Helper()
	var paths []string
	err := filepath.WalkDir(corpusDir, func(path string, e fs.DirEntry, err error) error {
		switch {
		case err != nil:
			return err
		case e.IsDir() && path != corpusDir && strings.HasPrefix(e.Name(), "."):
			return filepath.SkipDir
		case !e.IsDir() && filepath.Ext(path) == ".mmd":
			paths = append(paths, path)
		}
		return nil
	})
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	return paths
}

func spanProblems(d diag.Diagnostic, size int) []string {
	var problems []string
	check := func(what string, start, end int) {
		if start < 0 || start > end || end > size {
			problems = append(problems, d.Code+" "+what)
		}
	}
	check("span", d.Span.Start, d.Span.End)
	for _, r := range d.Related {
		check("related span", r.Span.Start, r.Span.End)
	}
	for _, f := range d.Fixes {
		for _, e := range f.Edits {
			check("edit span", e.Span.Start, e.Span.End)
		}
	}
	return problems
}

func TestDiagnosticSpansAndFixes(t *testing.T) {
	t.Run("corpus spans stay inside the source", func(t *testing.T) {
		var problems []string
		for _, path := range corpusSources(t) {
			src, err := os.ReadFile(path)
			require.NoError(t, err)
			report := LintSource(src, Config{})
			for _, d := range report.Diagnostics {
				for _, p := range spanProblems(d, len(report.Source)) {
					problems = append(problems, path+": "+p)
				}
			}
		}
		require.Empty(t, problems)
	})
	for _, c := range []struct{ name, code, safety string }{
		{"error-duplicate-ids", "flowchart/duplicate-ids", "none"},
		{"warning-quote-unclosed", "sequence/quote-unclosed", "unsafe"},
		{"safe-fix-arrow-invalid", "flowchart/arrow-invalid", "safe"},
		{"unsafe-fix-end-without-subgraph", "flowchart/end-without-subgraph", "unsafe"},
		{"suppressed-duplicate-ids", "", ""},
	} {
		t.Run("golden "+c.name, func(t *testing.T) {
			src, err := os.ReadFile(filepath.Join(goldenDir, c.name+".mmd"))
			require.NoError(t, err)
			checkGoldenFix(t, src, c.code, c.safety)
		})
	}
}

func withCode(ds []diag.Diagnostic, code string) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Code == code {
			out = append(out, d)
		}
	}
	return out
}

func checkGoldenFix(t *testing.T, src []byte, code, safety string) {
	t.Helper()
	report := LintSource(src, Config{})
	for _, d := range report.Diagnostics {
		require.Empty(t, spanProblems(d, len(report.Source)))
	}
	if code == "" {
		require.Empty(t, report.Diagnostics)
		return
	}
	found := withCode(report.Diagnostics, code)
	require.NotEmpty(t, found, "golden case lost its diagnostic")
	row, ok := Describe(code)
	require.True(t, ok)
	require.Equal(t, safety, row.FixSafety)
	for _, d := range found {
		require.Equal(t, safety != "none", len(d.Fixes) > 0)
		for _, f := range d.Fixes {
			require.Equal(t, safety, f.Safety.String())
		}
	}
	if safety == "none" {
		return
	}
	if safety == "unsafe" {
		skipped, applied := ApplyFixes(src, Config{}, diag.FixSafe)
		require.Zero(t, applied)
		require.Equal(t, string(src), string(skipped))
	}
	fixed, applied := ApplyFixes(src, Config{}, diag.FixUnsafe)
	require.Positive(t, applied)
	require.Empty(t, withCode(LintSource(fixed, Config{}).Diagnostics, code), "the fix leaves %s in place:\n%s", code, fixed)
}
