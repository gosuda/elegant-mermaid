package main

import (
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

func TestFlatClassification(t *testing.T) {
	for _, tc := range []struct{ name, boxes, routes, labels, want string }{
		{"dag", `[{"id":"A","role":"node"},{"id":"B","role":"node"},{"id":"C","role":"node"}]`, `[{"id":"e","from":"A","to":"B"},{"from":"B","to":"C"}]`, `[]`, ""},
		{"self", `[{"id":"A","role":"node"}]`, `[{"from":"A","to":"A"}]`, `[]`, "self-loop"},
		{"two", `[{"id":"A","role":"node"},{"id":"B","role":"node"}]`, `[{"from":"A","to":"B"},{"from":"B","to":"A"}]`, `[]`, "cycle"},
		{"long", `[{"id":"A","role":"node"},{"id":"B","role":"node"},{"id":"C","role":"node"}]`, `[{"from":"A","to":"B"},{"from":"B","to":"C"},{"from":"C","to":"A"}]`, `[]`, "cycle"},
		{"group", `[{"id":"G","role":"group"}]`, `[]`, `[]`, "group"},
		{"nested", `[{"id":"A","role":"node","parent":"G"}]`, `[]`, `[]`, "nested"},
		{"edge label", `[{"id":"A","role":"node"},{"id":"B","role":"node"}]`, `[{"id":"e","from":"A","to":"B"}]`, `[{"owner":"e"}]`, "label"},
		{"box label", `[{"id":"A","role":"node"}]`, `[]`, `[{"owner":"A"}]`, "label"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var model flatModel
			if err := json.Unmarshal([]byte(`{"boxes":`+tc.boxes+`,"routes":`+tc.routes+`,"labels":`+tc.labels+`}`), &model); err != nil {
				t.Fatal(err)
			}
			if got := flatReason(model); got != tc.want {
				t.Fatalf("got %q want %q", got, tc.want)
			}
		})
	}
}

func TestFlatListEndToEnd(t *testing.T) {
	binary := filepath.Join(t.TempDir(), "emd")
	build := exec.Command("go", "build", "-o", binary, "./cmd/emd")
	build.Dir = filepath.Join("..", "..")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build: %v\n%s", err, out)
	}
	t.Setenv("EMD_BIN", binary)
	root := t.TempDir()
	dir := filepath.Join(root, "corpus", "flowchart", "test")
	if err := os.MkdirAll(dir, 0755); err != nil {
		t.Fatal(err)
	}
	sources := []string{"flowchart TD\nA --> B\n", "flowchart TD\nA[alpha] --> B\n", "flowchart TD\nA --> A\n", "flowchart TD\nA --> B\nB --> A\n", "flowchart TD\nA -->|yes| B\n"}
	for i, source := range sources {
		if err := os.WriteFile(filepath.Join(dir, string(rune('a'+i))+".mmd"), []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
	}
	got, err := execute([]string{"-root", root, "-flat-list", "flowchart"})
	if err != nil {
		t.Fatal(err)
	}
	want := "corpus/flowchart/test/a.mmd\n"
	if got != want {
		t.Fatalf("got %q want %q", got, want)
	}
}
