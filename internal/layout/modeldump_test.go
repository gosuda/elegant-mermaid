package layout

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

const golden = `{"version":1,"stage":"model","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
"boxes":[{"id":"A","role":"node","parent":"","exclusive":true},
{"id":"B","role":"node","parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true}],
"labels":[{"id":"e0.label","owner":"e0","text":"yes","lines":[]}]}
`

func inputSource(t *testing.T, src []byte) (Input, bool) {
	t.Helper()
	p := syntax.Preprocess(src)
	f, ds := parser.Parse(src, p.Removed)
	m, more := model.Resolve(src, f)
	ds = append(ds, more...)
	for _, d := range ds {
		if d.Severity == 0 {
			return Input{}, false
		}
	}
	in, _ := FromFlowchart(m, scene.ProfileVector, scene.Options{})
	return in, true
}

func dumpInput(t *testing.T, in Input) []byte {
	t.Helper()
	var b bytes.Buffer
	if err := WriteModelDump(&b, in); err != nil {
		t.Fatal(err)
	}
	return b.Bytes()
}

func TestModelGolden(t *testing.T) {
	in, ok := inputSource(t, []byte("flowchart\nA -->|yes| B\n"))
	if !ok {
		t.Fatal("golden rejected")
	}
	if got := string(dumpInput(t, in)); got != golden {
		t.Fatalf("got %s", got)
	}
}

func TestFallbackGroupTitleTransport(t *testing.T) {
	for _, direction := range []string{"LR", "TD"} {
		in, ok := inputSource(t, []byte("graph "+direction+"\nsubgraph one\nA --> B\nend\n"))
		if !ok {
			t.Fatal("group fixture rejected")
		}
		in.Profile = scene.ProfileCell
		if len(in.Labels) != 0 {
			t.Fatalf("fallback title invented model labels: %v", in.Labels)
		}
		s := step14Scene(t, in)
		if len(s.Labels) != 0 {
			t.Fatalf("fallback title invented layout labels: %v", s.Labels)
		}
		title := sceneGroupTitle(t, s, "one", "one")
		if title.Rect.W != 3 || title.Rect.H != 1 {
			t.Fatalf("group title has incorrect measured rectangle: %+v", title.Rect)
		}
	}
}

func sceneGroupTitle(t *testing.T, s scene.Scene, owner, title string) *scene.Text {
	t.Helper()
	for _, group := range s.Groups {
		if group.Owner != owner || group.Role != scene.GroupRoleGroup {
			continue
		}
		for _, item := range group.Items {
			text, ok := item.(*scene.Text)
			if ok && len(text.Lines) == 1 && len(text.Lines[0]) == 1 && text.Lines[0][0].Text == title {
				return text
			}
		}
	}
	t.Fatalf("group %q title %q missing from scene", owner, title)
	return nil
}

func TestCorpusModelRelations(t *testing.T) {
	err := filepath.WalkDir("../../corpus/flowchart", func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() || filepath.Ext(path) != ".mmd" {
			return nil
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		in, ok := inputSource(t, src)
		if !ok {
			return nil
		}
		checkInput(t, in)
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
}

func checkInput(t *testing.T, in Input) {
	t.Helper()
	data := dumpInput(t, in)
	if !json.Valid(data) || !bytes.Equal(data, dumpInput(t, in)) {
		t.Fatal("invalid or unstable dump")
	}
	checkRelations(t, in)
	var value any
	if err := json.Unmarshal(data, &value); err != nil {
		t.Fatal(err)
	}
	forbiddenKeys(t, value)
}

func checkRelations(t *testing.T, in Input) {
	t.Helper()
	ids := map[string]bool{}
	for _, b := range in.Boxes {
		if ids[b.ID] {
			t.Fatalf("duplicate box %s", b.ID)
		}
		ids[b.ID] = true
	}
	for _, r := range in.Routes {
		if !ids[r.From] || !ids[r.To] {
			t.Fatalf("bad endpoint %s", r.ID)
		}
	}
	checkOwners(t, in, ids)
}

func checkOwners(t *testing.T, in Input, ids map[string]bool) {
	t.Helper()
	for _, r := range in.Routes {
		ids[r.ID] = true
	}
	for _, l := range in.Labels {
		if !ids[l.Owner] {
			t.Fatalf("bad owner %s", l.ID)
		}
	}
}

func forbiddenKeys(t *testing.T, v any) {
	t.Helper()
	switch v := v.(type) {
	case map[string]any:
		for k, x := range v {
			switch k {
			case "x", "y", "w", "h", "points", "canvas":
				t.Fatalf("coordinate key %s", k)
			}
			forbiddenKeys(t, x)
		}
	case []any:
		for _, x := range v {
			forbiddenKeys(t, x)
		}
	}
}
