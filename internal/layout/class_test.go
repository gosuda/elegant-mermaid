package layout

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestClassSize(t *testing.T) {
	size, err := ClassSize([][]string{{"Animal"}, {"+name", "+age"}, {}}, scene.ProfileCell)
	if err != nil || size != (geom.Size{W: 10, H: 8}) {
		t.Fatal(size, err)
	}
	size, err = ClassSize([][]string{{}, {}, {}}, scene.ProfileVector)
	if err != nil || size != (geom.Size{W: 2048, H: 3968}) {
		t.Fatal(size, err)
	}
}
func TestClassCompartments(t *testing.T) {
	src := []byte("classDiagram\nclass Animal {\n+name\n+run()\n}\nAnimal <|-- Dog\n")
	f, ds := parser.Parse(src, nil)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(src, f)
	if len(ds) > 0 {
		t.Fatal(ds)
	}
	in, _ := FromClass(m, scene.ProfileCell, scene.Options{})
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	result, err := cells.Render(s, cells.Options{})
	if err != nil {
		t.Fatal(err)
	}
	for _, text := range []string{"Animal", "+name", "+run()", "Dog"} {
		if !strings.Contains(string(result.Text), text) {
			t.Fatalf("missing %s:\n%s", text, result.Text)
		}
	}
	if result.RefusedClusters != 0 {
		t.Fatal(result.RefusedClusters)
	}
}

func TestClassMultilineHeadingRows(t *testing.T) {
	rows := classRows(model.Class{Label: "First\nSecond"})
	size, err := ClassSize(rows, scene.ProfileCell)
	if err != nil || size.H != 8 || len(rows[0]) != 2 {
		t.Fatal(rows, size, err)
	}
}

func TestClassAbsentTargetMarkerDump(t *testing.T) {
	src := []byte("classDiagram\nA -- B\nnote for A \"note\"\n")
	f, ds := parser.Parse(src, nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	m, ds := model.Resolve(src, f)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	in, _ := FromClass(m, scene.ProfileVector, scene.Options{})
	var dump strings.Builder
	if err := WriteModelDump(&dump, in); err != nil {
		t.Fatal(err)
	}
	if strings.Count(dump.String(), "\"marker_end\":\"none\"") != 2 {
		t.Fatal(dump.String())
	}
}
