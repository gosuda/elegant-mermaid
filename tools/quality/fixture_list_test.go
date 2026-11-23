package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

func TestListFixtures(t *testing.T) {
	all := listFixtureCorpus(t)
	for _, tc := range []struct {
		name string
		args []string
		want []string
	}{
		{"all layered kinds", nil, all},
		{"selected kinds", []string{"-kinds", "state,flowchart"}, []string{"corpus/accepted-flowchart.mmd", "corpus/accepted-state.mmd"}},
		{"read only with write flag", []string{"-write"}, all},
	} {
		t.Run(tc.name, func(t *testing.T) {
			args := append([]string{"-list", "-emd", filepath.Join(t.TempDir(), "missing-emd")}, tc.args...)
			var out, errOut bytes.Buffer
			if code := execute(args, &out, &errOut); code != 0 {
				t.Fatalf("exit %d: %s", code, errOut.String())
			}
			if errOut.Len() != 0 {
				t.Fatalf("unexpected diagnostics: %s", errOut.String())
			}
			want := strings.Join(tc.want, "\n") + "\n"
			if out.String() != want {
				t.Errorf("fixture list = %q, want %q", out.String(), want)
			}
		})
	}
	for _, path := range []string{"corpus/quality-corpus.txt", "corpus/quality-exceptions.json"} {
		if _, err := os.Stat(path); !os.IsNotExist(err) {
			t.Errorf("list mode created %s or could not check it: %v", path, err)
		}
	}
}

func TestListValidatesFlags(t *testing.T) {
	for _, tc := range []struct {
		name string
		args []string
	}{
		{"zero jobs", []string{"-jobs", "0"}},
		{"nonlayered kind", []string{"-kinds", "pie"}},
		{"empty executable", []string{"-emd", ""}},
		{"positional operand", []string{"fixture.mmd"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			args := append([]string{"-list"}, tc.args...)
			var out, errOut bytes.Buffer
			if code := execute(args, &out, &errOut); code != 2 {
				t.Errorf("exit = %d, want 2: %s", code, errOut.String())
			}
			if out.Len() != 0 || errOut.Len() == 0 {
				t.Errorf("stdout = %q, stderr = %q", out.String(), errOut.String())
			}
		})
	}
}

type fixtureKind struct {
	ID     string `json:"id"`
	Family string `json:"family"`
}

type fixtureVerdict struct {
	Accept bool   `json:"accept"`
	Kind   string `json:"kind"`
}

func listFixtureCorpus(t *testing.T) []string {
	t.Helper()
	kinds := fixtureKindRegistry(t)
	verdicts := make(map[string]fixtureVerdict, 2*len(kinds))
	var expected []string
	for _, kind := range kinds {
		path := "corpus/accepted-" + kind.ID + ".mmd"
		verdicts[path] = fixtureVerdict{Accept: true, Kind: kind.ID}
		verdicts["corpus/rejected-"+kind.ID+".mmd"] = fixtureVerdict{Kind: kind.ID}
		if kind.Family == "layered" {
			expected = append(expected, path)
		}
	}
	writeFixtureVerdicts(t, verdicts)
	slices.Sort(expected)
	return expected
}

func fixtureKindRegistry(t *testing.T) []fixtureKind {
	t.Helper()
	data, err := os.ReadFile("../../spec/data/kinds.json")
	if err != nil {
		t.Fatal(err)
	}
	var kinds []fixtureKind
	if err := json.Unmarshal(data, &kinds); err != nil {
		t.Fatal(err)
	}
	return kinds
}

func writeFixtureVerdicts(t *testing.T, verdicts map[string]fixtureVerdict) {
	t.Helper()
	data, err := json.Marshal(verdicts)
	if err != nil {
		t.Fatal(err)
	}
	t.Chdir(t.TempDir())
	if err := os.Mkdir("corpus", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile("corpus/verdicts.json", data, 0o644); err != nil {
		t.Fatal(err)
	}
}
