package layout

import (
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestClassDefaultStroke(t *testing.T) {
	f, diagnostics := parser.Parse([]byte("classDiagram\nA --> B\nA ..> B\n"), nil)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	m, diagnostics := model.Resolve(nil, f)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	in, err := FromClass(m, scene.ProfileVector, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	if in.Routes[0].Line != "normal" || in.Routes[1].Line != "dashed" {
		t.Fatal(in.Routes)
	}
}

func TestClassSize(t *testing.T) {
	size, err := ClassSize([][]string{{"Animal"}, {"+name", "+age"}, {}}, scene.ProfileCell)
	if err != nil || size != (geom.Size{W: 10, H: 8}) {
		t.Fatal(size, err)
	}
	size, err = ClassSize([][]string{{}, {}, {}}, scene.ProfileVector)
	if err != nil || size != (geom.Size{W: 2048, H: 3968}) {
		t.Fatal(size, err)
	}
	for _, test := range []struct {
		name   string
		rows   [][]string
		width  int32
		height int32
	}{
		{"italic member", [][]string{{"C"}, {"_AAAAAAAA_"}, {}}, styledAdvanceWidth(t, []scene.Run{{Text: "AAAAAAAA", Italic: true}}, 0) + 2*goldenConstant(t, "class.padding"), 3*goldenConstant(t, "line_h") + 2*goldenConstant(t, "class.separator")},
		{"body member", [][]string{{"C"}, {"AAAAAAAA"}, {}}, styledAdvanceWidth(t, []scene.Run{{Text: "AAAAAAAA"}}, 0) + 2*goldenConstant(t, "class.padding"), 3*goldenConstant(t, "line_h") + 2*goldenConstant(t, "class.separator")},
		{"forced member break", [][]string{{"C"}, {"_AAAAAAAA_<BR />B"}, {}}, styledAdvanceWidth(t, []scene.Run{{Text: "AAAAAAAA", Italic: true}}, 0) + 2*goldenConstant(t, "class.padding"), 4*goldenConstant(t, "line_h") + 2*goldenConstant(t, "class.separator")},
	} {
		t.Run(test.name, func(t *testing.T) {
			got, err := ClassSize(test.rows, scene.ProfileVector)
			if err != nil || got != (geom.Size{W: test.width, H: test.height}) {
				t.Fatalf("styled class size = %v, %v; want %d x %d", got, err, test.width, test.height)
			}
		})
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
	t.Run("styled body", testStyledClassBody)
}

func testStyledClassBody(t *testing.T) {
	d := ParseDiagram([]byte("classDiagram\nclass C {\n+_AAAAAAAA_\n}\n"))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	want := []scene.Run{{Text: "+"}, {Text: "AAAAAAAA", Italic: true}}
	text := classBodyText(s, "C")
	if text == nil {
		t.Fatal("missing styled class body")
	}
	if !slices.Equal(text.Lines[0], want) {
		t.Fatalf("member runs = %#v; want %#v", text.Lines[0], want)
	}
	width := styledAdvanceWidth(t, want, 0)
	if text.Rect.W != width {
		t.Fatalf("member content width = %d; want %d", text.Rect.W, width)
	}
}

func classBodyText(s scene.Scene, owner string) *scene.Text {
	for _, group := range s.Groups {
		if group.Owner != owner {
			continue
		}
		for _, item := range group.Items {
			text, ok := item.(*scene.Text)
			if ok && text.Role == scene.TextRoleBody && len(text.Lines) != 0 {
				return text
			}
		}
	}
	return nil
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

func styledAdvanceWidth(t *testing.T, runs []scene.Run, ordinary uint8) int32 {
	t.Helper()
	var sum int64
	for _, run := range runs {
		weight := ordinary
		if run.Bold {
			weight = 1
		} else if run.Italic {
			weight = 0
		}
		for _, cp := range run.Text {
			sum += authoritativeAdvance(t, cp, weight)
		}
	}
	upem := int64(gen.AdvancesUpem[ordinary])
	return int32((sum*14*64 + upem - 1) / upem)
}

func authoritativeAdvance(t *testing.T, cp rune, weight uint8) int64 {
	t.Helper()
	for _, advance := range gen.Advances {
		if advance.CP == uint32(cp) && advance.Weight == weight {
			return int64(advance.Units)
		}
	}
	t.Fatalf("missing authoritative advance for %q at weight %d", cp, weight)
	return 0
}
