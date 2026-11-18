package layout

import (
	"encoding/json"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func diagramModelDump(t *testing.T, src string) string {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		t.Fatalf("diagnostic: %+v", diagnostic)
	}
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	return string(dumpInput(t, in))
}

func dumpRecord(t *testing.T, dump, id string) string {
	t.Helper()
	var parsed struct {
		Boxes  []json.RawMessage `json:"boxes"`
		Routes []json.RawMessage `json:"routes"`
	}
	if err := json.Unmarshal([]byte(dump), &parsed); err != nil {
		t.Fatal(err)
	}
	for _, record := range append(parsed.Boxes, parsed.Routes...) {
		var head struct {
			ID string `json:"id"`
		}
		if err := json.Unmarshal(record, &head); err != nil {
			t.Fatal(err)
		}
		if head.ID == id {
			return string(record)
		}
	}
	t.Fatalf("no box or route %q in %s", id, dump)
	return ""
}

func TestModelDumpERBoxesCarryTheMeasuredTable(t *testing.T) {
	dump := diagramModelDump(t, "erDiagram\nCUSTOMER ||--o{ ORDER : places\nCUSTOMER {\n  string name PK \"the <br> name\"\n  int age\n}\nORDER { int id }\n")
	for id, want := range map[string]string{
		"CUSTOMER": `{"id":"CUSTOMER","role":"node","parent":"","exclusive":true,"shape":"erBox","text":"CUSTOMER<br/><br/>string|name|PK|the \\n name<br/>int|age||"}`,
		"ORDER":    `{"id":"ORDER","role":"node","parent":"","exclusive":true,"shape":"erBox","text":"ORDER<br/><br/>int|id||"}`,
	} {
		if got := dumpRecord(t, dump, id); got != want {
			t.Fatalf("got %s, want %s", got, want)
		}
	}
}

func TestModelDumpERGroupTitleAndEmptyTable(t *testing.T) {
	dump := diagramModelDump(t, "erDiagram\nsubgraph G [Group]\nA\nend\n")
	for id, want := range map[string]string{
		"A": `{"id":"A","role":"node","parent":"G","exclusive":true,"shape":"erBox","text":"A<br/><br/>"}`,
		"G": `{"id":"G","role":"group","parent":"","exclusive":false,"direction":"","text":"Group"}`,
	} {
		if got := dumpRecord(t, dump, id); got != want {
			t.Fatalf("got %s, want %s", got, want)
		}
	}
}

func TestModelDumpBoxesWithLabelRecordsCarryNoText(t *testing.T) {
	for _, src := range []string{
		"flowchart\nA[Start] --> B\n",
		"classDiagram\nclass Animal {\n  +name\n}\n",
		"requirementDiagram\nrequirement r {\n  id: 1\n  text: x\n  risk: low\n  verifymethod: test\n}\n",
	} {
		dump := diagramModelDump(t, src)
		var parsed struct {
			Boxes []map[string]any `json:"boxes"`
		}
		if err := json.Unmarshal([]byte(dump), &parsed); err != nil {
			t.Fatal(err)
		}
		if len(parsed.Boxes) == 0 {
			t.Fatalf("no boxes in %s", dump)
		}
		for _, b := range parsed.Boxes {
			if _, ok := b["text"]; ok {
				t.Fatalf("labelled box carries text: %v in %s", b, dump)
			}
		}
	}
}

func TestModelDumpMinLengthKey(t *testing.T) {
	usecase := diagramModelDump(t, "usecase-beta\nactor A\nA ----> B\nA --> C\n")
	agentflow := diagramModelDump(t, "agentflow-beta TB\n  a[\"a\"]\n  b[\"b\"]\n  c[\"c\"]\n  d[\"d\"]\n  a ---> b\n  a --->|x| c\n  c ---->|y| d\n  c --> d\n")
	for _, want := range []struct {
		dump, id, record string
	}{
		{usecase, "e0", `{"id":"e0","from":"A","to":"B","orthogonal":true,"min_length":3}`},
		{usecase, "e1", `{"id":"e1","from":"A","to":"C","orthogonal":true}`},
		{agentflow, "e0", `{"id":"e0","from":"a","to":"b","orthogonal":true,"min_length":2}`},
		{agentflow, "e1", `{"id":"e1","from":"a","to":"c","orthogonal":true}`},
		{agentflow, "e2", `{"id":"e2","from":"c","to":"d","orthogonal":true,"min_length":3}`},
		{agentflow, "e3", `{"id":"e3","from":"c","to":"d","orthogonal":true}`},
	} {
		if got := dumpRecord(t, want.dump, want.id); got != want.record {
			t.Fatalf("got %s, want %s", got, want.record)
		}
	}
}

func TestModelMinLengthDefaultDependsOnLabels(t *testing.T) {
	labelled := map[string]struct{}{"e1": {}}
	for _, c := range []struct {
		kind string
		r    Route
		want int32
	}{
		{"usecase", Route{ID: "e0", MinLength: 1}, 0},
		{"usecase", Route{ID: "e0", MinLength: 2}, 2},
		{"usecase", Route{ID: "e1", MinLength: 2}, 0},
		{"usecase", Route{ID: "e1", MinLength: 3}, 3},
		{"flowchart", Route{ID: "e0", MinLength: 5}, 0},
		{"state", Route{ID: "e1", MinLength: 2}, 0},
	} {
		if got := modelMinLength(c.kind, c.r, labelled); got != c.want {
			t.Fatalf("%s %+v: got %d, want %d", c.kind, c.r, got, c.want)
		}
	}
}

func layoutStageScene(t *testing.T, src string) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(src))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func requireNoKey(t *testing.T, records []map[string]any, key string) {
	t.Helper()
	for _, record := range records {
		if _, ok := record[key]; ok {
			t.Fatalf("layout-stage record carries %s: %v", key, record)
		}
	}
}

func TestLayoutStageDumpCarriesNoModelOnlyKeys(t *testing.T) {
	for _, src := range []string{
		"erDiagram\nCUSTOMER ||--o{ ORDER : places\nCUSTOMER { string name }\n",
		"usecase-beta\nactor A\nA ----> B\n",
	} {
		s := layoutStageScene(t, src)
		var parsed struct {
			Boxes  []map[string]any `json:"boxes"`
			Routes []map[string]any `json:"routes"`
		}
		if err := json.Unmarshal(s.AppendJSON(nil), &parsed); err != nil {
			t.Fatal(err)
		}
		requireNoKey(t, parsed.Boxes, "text")
		requireNoKey(t, parsed.Routes, "min_length")
	}
}

func TestModelDumpWritesAnAbsentTargetMarkerAsNone(t *testing.T) {
	er := diagramModelDump(t, "erDiagram\nA u--o{ B : x\nA ||--|| B : y\n")
	flowchart := diagramModelDump(t, "flowchart\nA --- B\nA --> C\nA --x D\n")
	for _, want := range []struct {
		dump, id, record string
	}{
		{er, "e0", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_start":"zero_or_more","marker_end":"none"}`},
		{er, "e1", `{"id":"e1","from":"A","to":"B","orthogonal":true,"marker_start":"only_one","marker_end":"only_one"}`},
		{flowchart, "e0", `{"id":"e0","from":"A","to":"B","orthogonal":true,"marker_end":"none"}`},
		{flowchart, "e1", `{"id":"e1","from":"A","to":"C","orthogonal":true}`},
		{flowchart, "e2", `{"id":"e2","from":"A","to":"D","orthogonal":true,"marker_end":"cross"}`},
	} {
		if got := dumpRecord(t, want.dump, want.id); got != want.record {
			t.Fatalf("got %s, want %s", got, want.record)
		}
	}
}
