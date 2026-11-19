package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	erparser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

func erTestInput(t *testing.T, text string, profile scene.Profile) Input {
	t.Helper()
	start, ds := erparser.Parse([]byte(text), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	m, rds := ermodel.Resolve(nil, start)
	if len(rds) != 0 {
		t.Fatal(rds)
	}
	in, _ := FromER(m, profile, scene.Options{})
	return in
}

func erTextItems(items []scene.Primitive) []*scene.Text {
	var out []*scene.Text
	for _, item := range items {
		if text, ok := item.(*scene.Text); ok {
			out = append(out, text)
		}
	}
	return out
}

func TestERShapesAndMinimumSizes(t *testing.T) {
	for _, want := range []struct {
		profile scene.Profile
		size    geom.Size
	}{
		{scene.ProfileCell, geom.Size{W: 13, H: 5}},
		{scene.ProfileVector, geom.Size{W: 6400, H: 4800}},
	} {
		in := erTestInput(t, "erDiagram\nA\n", want.profile)
		box := in.Boxes[0]
		if box.ID != "A" || box.Shape != "erBox" {
			t.Fatal(box)
		}
		input, err := erFamilyInput(in)
		if err != nil {
			t.Fatal(err)
		}
		if input.Sizes[0] != want.size {
			t.Fatal(input.Sizes[0])
		}
	}
}

func TestERCardinalityAndLineKinds(t *testing.T) {
	in := erTestInput(t, "erDiagram\nA ||--o{ B : owns\nA |o..|{ B : uses\n", scene.ProfileCell)
	var got []string
	for _, route := range in.Routes {
		got = append(got, route.MarkerStart+" "+route.MarkerEnd+" "+route.Line)
	}
	want := []string{"zero_or_more only_one normal", "one_or_more zero_or_one dashed"}
	if len(got) != len(want) {
		t.Fatal(got)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatal(i, got)
		}
	}
	var labels []string
	for _, label := range in.Labels {
		labels = append(labels, label.Text)
	}
	if len(labels) != 2 || labels[0] != "owns" || labels[1] != "uses" {
		t.Fatal(labels)
	}
}

func TestERTableKeepsColumns(t *testing.T) {
	in := erTestInput(t, "erDiagram\nA { int id PK \"identifier\" }\n", scene.ProfileCell)
	box := in.Boxes[0]
	if box.Text != "A<br/><br/>int|id|PK|identifier" {
		t.Fatal(box.Text)
	}
	items, err := erTableItems(box.Text, geom.Rect{W: 27, H: 5}, scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	if len(erTextItems(items)) != 5 {
		t.Fatal(items)
	}
}

func TestERGroupsAndRouteIDs(t *testing.T) {
	in := erTestInput(t, "erDiagram\ne0\nsubgraph G [Group]\nA\nend\nG ||--|| A : owns\n", scene.ProfileCell)
	if len(in.Groups) != 1 {
		t.Fatal(in.Groups)
	}
	if in.Routes[0].ID != "e1" {
		t.Fatal(in.Routes)
	}
	var parent string
	for _, box := range in.Boxes {
		if box.ID == "A" {
			parent = box.Parent
		}
	}
	if parent != "G" {
		t.Fatal(parent)
	}
}

func TestERMDParentHasNoMarker(t *testing.T) {
	in := erTestInput(t, "erDiagram\nA u--|| B : parent\nA ||--u-B : child\n", scene.ProfileCell)
	if len(in.Routes) != 2 {
		t.Fatal(in.Routes)
	}
	if in.Routes[0].MarkerStart != "only_one" || in.Routes[0].MarkerEnd != "" {
		t.Fatal(in.Routes[0])
	}
	if in.Routes[1].MarkerStart != "" || in.Routes[1].MarkerEnd != "only_one" {
		t.Fatal(in.Routes[1])
	}
}

func TestERHeightReservesOnlyTheHeaderDividerInCells(t *testing.T) {
	text := "A<br/><br/>int|a||<br/>int|b||"
	cell, err := erTableSize(text, scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	if cell != (geom.Size{W: 13, H: 6}) {
		t.Fatal(cell)
	}
	vector, err := erTableSize(text, scene.ProfileVector)
	if err != nil {
		t.Fatal(err)
	}
	if vector != (geom.Size{W: 6400, H: 5760}) {
		t.Fatal(vector)
	}
}

func TestEREscapedFieldsKeepMultilineTextAndColumnDelimiters(t *testing.T) {
	encoded := erEncodeField("line1<br/>line2|literal\\n")
	if encoded != "line1\\nline2\\pliteral\\\\n" {
		t.Fatal(encoded)
	}
	if erDecodeField(encoded) != "line1\nline2|literal\\n" {
		t.Fatal(encoded)
	}
	table, err := erNewTable("A<br/><br/>"+encoded+"|name||", scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	if len(table.rowHeights) != 1 || table.rowHeights[0] != 2 {
		t.Fatal(table.rowHeights)
	}
}

func TestERHiddenEntityEndpointsBindToFinalGroupBox(t *testing.T) {
	in := erTestInput(t, "erDiagram\nG ||--|| A : before\nsubgraph G\nB\nend\nG ||--|| A : after\n", scene.ProfileCell)
	count := 0
	var role scene.BoxRole
	var from []string
	for _, box := range in.Boxes {
		if box.ID == "G" {
			count++
			role = box.Role
		}
	}
	for _, route := range in.Routes {
		from = append(from, route.From)
	}
	if count != 1 || role != scene.RoleGroup {
		t.Fatal(in.Boxes)
	}
	if len(from) != 2 || from[0] != "G" || from[1] != "G" {
		t.Fatal(from)
	}
}

func TestERFieldTableSize(t *testing.T) {
	text := "A<br/><br/>x\\ny|**id**||"
	px := erConstant(scene.ProfileCell, "padding_x")
	py := erConstant(scene.ProfileCell, "padding_y")
	minWidth := erConstant(scene.ProfileCell, "min_width")
	contentWidth := int32(1) + int32(2) + px
	size, err := erTableSize(text, scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	want := geom.Size{W: max(minWidth, contentWidth+2*px), H: 1 + 2 + 1 + 2*py}
	if size != want {
		t.Fatal(size, want)
	}
}

func TestERFieldsEmitFlaggedRunsAndKeepFieldLines(t *testing.T) {
	text := "A<br/><br/>x\\ny|**id**||"
	size, err := erTableSize(text, scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	items, err := erTableItems(text, geom.Rect{W: size.W, H: size.H}, scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	wantRuns(t, erTextItems(items))
}

func firstTextWhere(texts []*scene.Text, match func(*scene.Text) bool) *scene.Text {
	for _, text := range texts {
		if match(text) {
			return text
		}
	}
	return nil
}

func isBoldIDCell(text *scene.Text) bool {
	return len(text.Lines) == 1 && len(text.Lines[0]) == 1 && text.Lines[0][0] == (scene.Run{Text: "id", Bold: true})
}

func isSplitFieldCell(text *scene.Text) bool {
	return len(text.Lines) == 2 && len(text.Lines[0]) == 1 && text.Lines[0][0] == (scene.Run{Text: "x"}) && text.Lines[1][0] == (scene.Run{Text: "y"})
}

func wantRuns(t *testing.T, texts []*scene.Text) {
	t.Helper()
	bold := firstTextWhere(texts, func(text *scene.Text) bool { return hasBoldRun(text.Lines) })
	if bold == nil {
		t.Fatal("missing bold cell")
	}
	if !isBoldIDCell(bold) {
		t.Fatal(bold.Lines)
	}
	split := firstTextWhere(texts, func(text *scene.Text) bool { return len(text.Lines) == 2 })
	if split == nil {
		t.Fatal("missing two-line field")
	}
	if !isSplitFieldCell(split) {
		t.Fatal(split.Lines)
	}
}

func hasBoldRun(lines [][]scene.Run) bool {
	for _, line := range lines {
		for _, run := range line {
			if run.Bold {
				return true
			}
		}
	}
	return false
}

func TestERLayoutDrawsTableCompartmentsUnderBothProfiles(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		wantCompartmentTexts(t, profile)
	}
}

func wantCompartmentTexts(t *testing.T, profile scene.Profile) {
	t.Helper()
	in := erTestInput(t, "erDiagram\nA { int id PK \"key\" }\n", profile)
	s, ds, err := layoutER(in)
	if err != nil {
		t.Fatal(err)
	}
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	group := ownerGroup(s, "A")
	if group == nil {
		t.Fatal("missing node group")
	}
	if len(erTextItems(group.Items)) != 5 {
		t.Fatal(group.Items)
	}
	if len(s.Boxes) == 0 || s.Boxes[0].ID != "A" {
		t.Fatal(s.Boxes)
	}
}

func ownerGroup(s scene.Scene, id string) *scene.Group {
	var group *scene.Group
	for _, g := range s.Groups {
		if g.Owner == id {
			group = g
		}
	}
	return group
}
