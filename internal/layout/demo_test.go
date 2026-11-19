package layout

import (
	"encoding/json"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const demoSource = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n"

func TestModelShapesKeepDeclaredOwners(t *testing.T) {
	in, ok := inputSource(t, []byte(demoSource))
	if !ok {
		t.Fatal("demo rejected")
	}
	var dump struct {
		Boxes []struct {
			ID    string          `json:"id"`
			Shape json.RawMessage `json:"shape"`
		} `json:"boxes"`
	}
	if err := json.Unmarshal(dumpInput(t, in), &dump); err != nil {
		t.Fatal(err)
	}
	want := map[string]any{"A": nil, "B": "diamond", "C": nil}
	for _, b := range dump.Boxes {
		declared, known := want[b.ID]
		if !known {
			t.Fatalf("unexpected box %s in model dump", b.ID)
		}
		delete(want, b.ID)
		var shape any
		if err := json.Unmarshal(b.Shape, &shape); err != nil && len(b.Shape) != 0 {
			t.Fatalf("box %s shape: %v", b.ID, err)
		}
		if shape != declared || (len(b.Shape) != 0) != (declared != nil) {
			t.Fatalf("box %s got shape %s, source declares %v", b.ID, b.Shape, declared)
		}
	}
	if len(want) != 0 {
		t.Fatalf("boxes missing from model dump: %v", want)
	}
}

func TestStyledFlowchartLabels(t *testing.T) {
	s := styledFlowchartScene(t)
	for _, test := range []struct {
		owner    string
		runs     []scene.Run
		rendered string
		padding  int32
	}{
		{"A", []scene.Run{{Text: "This "}, {Text: "is", Bold: true}, {Text: " "}, {Text: "Markdown", Italic: true}}, "This is Markdown", 2 * goldenConstant(t, "node_pad_x")},
		{"e0", []scene.Run{{Text: "Go "}, {Text: "bold", Bold: true}, {Text: " "}, {Text: "italic", Italic: true}}, "Go bold italic", 0},
	} {
		t.Run(test.owner, func(t *testing.T) {
			text := flowchartOwnerText(s, test.owner)
			if text == nil || len(text.Lines) != 1 || !slices.Equal(text.Lines[0], test.runs) {
				t.Fatalf("styled text for %s = %#v; want %#v", test.owner, text, test.runs)
			}
			wantWidth := styledAdvanceWidth(t, test.runs, 1)
			if text.Rect.W != wantWidth+test.padding {
				t.Fatalf("text box width = %d; want advances %d + padding %d", text.Rect.W, wantWidth, test.padding)
			}
			checkFlowchartDumpLines(t, s, test.owner, test.rendered)
		})
	}
}

func TestCellFlowchartEmphasisStopsAtSourceNewline(t *testing.T) {
	const label = "**a\nb**"
	d := ParseDiagram([]byte("flowchart TD\nA[\"" + label + "\"]\n"))
	in, err := d.Input(scene.ProfileCell, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	checkFlowchartModelSourceLabel(t, in, label)
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	assertCellText(t, s, "**a\ufffdb**")
	checkFlowchartPlainTextLine(t, s, "A", "**a\ufffdb**")
}

func checkFlowchartModelSourceLabel(t *testing.T, in Input, label string) {
	t.Helper()
	var model struct {
		Labels []struct{ Text string }
	}
	if err := json.Unmarshal(dumpInput(t, in), &model); err != nil {
		t.Fatal(err)
	}
	if len(model.Labels) != 1 || model.Labels[0].Text != label {
		t.Fatalf("model source labels = %#v; want %q", model.Labels, label)
	}
}

func checkFlowchartPlainTextLine(t *testing.T, s scene.Scene, owner, want string) {
	t.Helper()
	text := flowchartOwnerText(s, owner)
	if text == nil || len(text.Lines) != 1 {
		t.Fatalf("node rendered text = %#v; want one line", text)
	}
	var rendered string
	for _, run := range text.Lines[0] {
		rendered += run.Text
		if run.Bold || run.Italic {
			t.Fatalf("literal node text has emphasis: %#v", run)
		}
	}
	if rendered != want {
		t.Fatalf("node rendered text = %q; want %q with literal emphasis markers", rendered, want)
	}
}

func checkFlowchartDumpLines(t *testing.T, s scene.Scene, owner, rendered string) {
	t.Helper()
	for _, label := range s.Labels {
		if label.Owner == owner && !slices.Equal(label.Lines, []string{rendered}) {
			t.Fatalf("rendered dump lines = %#v; want %q", label.Lines, rendered)
		}
	}
}

func styledFlowchartScene(t *testing.T) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte("flowchart TD\nA[\"This **is** _Markdown_\"] -->|Go **bold** _italic_| B\n"))
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

func flowchartOwnerText(s scene.Scene, owner string) *scene.Text {
	var text *scene.Text
	for _, group := range s.Groups {
		if group.Owner != owner {
			continue
		}
		for _, item := range group.Items {
			if candidate, ok := item.(*scene.Text); ok {
				text = candidate
			}
		}
	}
	return text
}
