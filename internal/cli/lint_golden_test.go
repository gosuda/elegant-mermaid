package cli_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

const lintGoldenDir = "../../spec/golden/lint"

var lintGoldenCases = []struct {
	name string
	exit int
}{
	{name: "error-duplicate-ids", exit: 1},
	{name: "warning-quote-unclosed"},
	{name: "safe-fix-arrow-invalid", exit: 1},
	{name: "unsafe-fix-end-without-subgraph", exit: 1},
	{name: "suppressed-duplicate-ids"},
}

func lintGoldenPath(t *testing.T) string {
	t.Helper()
	dir, err := filepath.Abs(lintGoldenDir)
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

func TestLintGolden(t *testing.T) {
	dir := lintGoldenPath(t)
	for _, c := range lintGoldenCases {
		for _, format := range []string{"text", "json", "sarif", "github"} {
			t.Run(c.name+"."+format, func(t *testing.T) {
				want, err := os.ReadFile(filepath.Join(dir, c.name+"."+format))
				if err != nil {
					t.Fatal(err)
				}
				cmd := binaryCommand(t, "lint", "--no-config", "--color", "never", "--output-format", format, c.name+".mmd")
				cmd.Dir = dir
				binaryOutput(t, cmd, "", string(want), "", c.exit)
			})
		}
	}
}

func TestLintGoldenCasesAreTheSpecCases(t *testing.T) {
	entries, err := os.ReadDir(lintGoldenPath(t))
	if err != nil {
		t.Fatal(err)
	}
	var cases, want []string
	for _, e := range entries {
		if name, ok := strings.CutSuffix(e.Name(), ".mmd"); ok {
			cases = append(cases, name)
		}
	}
	for _, c := range lintGoldenCases {
		want = append(want, c.name)
	}
	slices.Sort(want)
	if !slices.Equal(cases, want) {
		t.Fatalf("golden cases %v; want %v", cases, want)
	}
}

func TestSeverityOverride(t *testing.T) {
	dir := t.TempDir()
	golden := lintGoldenPath(t)
	src, err := os.ReadFile(filepath.Join(golden, "error-duplicate-ids.mmd"))
	if err != nil {
		t.Fatal(err)
	}
	want, err := os.ReadFile(filepath.Join(golden, "error-duplicate-ids.info.txt"))
	if err != nil {
		t.Fatal(err)
	}
	config := `{"lint":{"severity":{"flowchart/duplicate-ids":"info"}}}`
	for name, data := range map[string][]byte{"error-duplicate-ids.mmd": src, "emd.json": []byte(config)} {
		if err = os.WriteFile(filepath.Join(dir, name), data, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	cmd := binaryCommand(t, "lint", "--color", "never", "--output-format", "text", "error-duplicate-ids.mmd")
	cmd.Dir = dir
	binaryOutput(t, cmd, "", string(want), "", 0)
}
