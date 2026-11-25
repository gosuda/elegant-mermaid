package layout

import (
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	reqmodel "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	reqparser "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
)

func requirementInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	document, ds := reqparser.Parse([]byte(src), nil)
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	model, resolved := reqmodel.Resolve([]byte(src), document)
	if len(resolved) != 0 {
		t.Fatal(resolved)
	}
	in, diagnostics := FromRequirement(model, profile, scene.Options{})
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	return in
}

func TestUnresolvedRelationsAreRetainedOnlyByModel(t *testing.T) {
	in := requirementInput(t, "requirementDiagram\nrequirement R {\n}\nR - verifies -> Missing\n", scene.ProfileCell)
	if len(in.Routes) != 0 {
		t.Fatal(in.Routes)
	}
	owners := make([]string, len(in.Labels))
	for i, l := range in.Labels {
		owners[i] = l.Owner
	}
	if !slices.Equal(owners, []string{"R"}) {
		t.Fatal(owners)
	}
}

func TestRequirementsPrecedeElementsWithDistinctIDs(t *testing.T) {
	in := requirementInput(t, "requirementDiagram\nelement X {\n}\nelement Y {\n}\nrequirement X {\n}\nrequirement Y {\n}\nX - copies -> Y\n", scene.ProfileCell)
	ids := make([]string, len(in.Boxes))
	for i, b := range in.Boxes {
		ids[i] = b.ID
	}
	if !slices.Equal(ids, []string{"X", "Y", "element:0", "element:1"}) {
		t.Fatal(ids)
	}
	if in.Routes[0].From != "X" || in.Routes[0].To != "Y" {
		t.Fatal(in.Routes[0])
	}
}

func TestNonContainsRelationshipsUseDashedTargetArrows(t *testing.T) {
	src := "requirementDiagram\nrequirement R {\n}\nelement E {\n}\n"
	for _, relation := range []string{"copies", "derives", "satisfies", "verifies", "refines", "traces"} {
		in := requirementInput(t, src+"R - "+relation+" -> E\n", scene.ProfileVector)
		if len(in.Routes) != 1 {
			t.Fatal(in.Routes)
		}
		r := in.Routes[0]
		if r.Line != "dashed" || r.MarkerStart != "none" || r.MarkerEnd != "requirement_arrow" {
			t.Fatal(relation, r)
		}
	}
}

func TestVectorDividerUsesPaddingWithoutAddingHeight(t *testing.T) {
	items, err := requirementTableItems("<<Element>>\nE\nType: service", geom.Rect{X: 0, Y: 0, W: 20000, H: 5120}, scene.ProfileVector, "")
	if err != nil {
		t.Fatal(err)
	}
	var divider *scene.Polyline
	var rows []int32
	for _, item := range items {
		switch v := item.(type) {
		case *scene.Polyline:
			if divider != nil {
				t.Fatal("duplicate divider")
			}
			divider = v
		case *scene.Text:
			rows = append(rows, v.Rect.Y)
		}
	}
	if divider == nil || !slices.Equal(divider.Points, []geom.Point{{X: 0, Y: 3200}, {X: 20000, Y: 3200}}) {
		t.Fatal(divider)
	}
	if !slices.Equal(rows, []int32{320, 1600, 3520}) {
		t.Fatal(rows)
	}
}

func TestLayeredPipelineReturnsRequirementTableGroups(t *testing.T) {
	in := requirementInput(t, "requirementDiagram\nrequirement R {\n}\nelement E {\n}\nR - contains -> E\n", scene.ProfileCell)
	s, _, err := layoutRequirement(in)
	if err != nil {
		t.Fatal(err)
	}
	ids := make([]string, len(s.Boxes))
	for i, b := range s.Boxes {
		ids[i] = b.ID
	}
	if !slices.Equal(ids, []string{"R", "E"}) {
		t.Fatal(ids)
	}
	for _, group := range s.Groups {
		if group.Owner != "R" {
			continue
		}
		count := 0
		for _, item := range group.Items {
			if _, ok := item.(*scene.Text); ok {
				count++
			}
		}
		if count != 2 {
			t.Fatal(count)
		}
		return
	}
	t.Fatal("missing table group")
}

func requirementFirstTextLines(t *testing.T, source string) [][]scene.Run {
	t.Helper()
	items, err := requirementTableItems(source, geom.Rect{X: 0, Y: 0, W: 4000, H: 4000}, scene.ProfileVector, "")
	if err != nil {
		t.Fatal(err)
	}
	for _, item := range items {
		if text, ok := item.(*scene.Text); ok {
			return text.Lines
		}
	}
	t.Fatal("missing heading")
	return nil
}

func isFlaggedHeading(lines [][]scene.Run) bool {
	return len(lines) == 1 && len(lines[0]) == 3 && lines[0][0].Text == "H" && lines[0][0].Bold && lines[0][1].Text == " " && lines[0][2].Text == "i" && lines[0][2].Italic
}

func isOpaqueMath(lines [][]scene.Run) bool {
	return len(lines) == 1 && len(lines[0]) == 1 && lines[0][0].Text == "$$x$$" && !lines[0][0].Bold && !lines[0][0].Italic
}

func TestRequirementRowsCarryFlagsAndMathStaysOpaque(t *testing.T) {
	if heading := requirementFirstTextLines(t, "**H** *i*\nR\nf"); !isFlaggedHeading(heading) {
		t.Fatal(heading)
	}
	if math := requirementFirstTextLines(t, "$$x$$\nR\nf"); !isOpaqueMath(math) {
		t.Fatal(math)
	}
}

func semiBoldWidth(t *testing.T, text string) int32 {
	t.Helper()
	width, err := measure.VectorWidth(text, 14, measure.WeightSemiBold)
	if err != nil {
		t.Fatal(err)
	}
	return width
}

func assertRequirementSize(t *testing.T, text string, profile scene.Profile, want geom.Size) {
	t.Helper()
	size, err := requirementTableSize(text, profile, "")
	if err != nil {
		t.Fatal(err)
	}
	if size != want {
		t.Fatal(size)
	}
}

func dividersAndRows(items []scene.Primitive) (int, int32, [][3]int32) {
	var dividerY int32
	dividers := 0
	var rows [][3]int32
	for _, item := range items {
		switch v := item.(type) {
		case *scene.Polyline:
			dividers++
			dividerY = v.Points[0].Y
		case *scene.Text:
			rows = append(rows, [3]int32{v.Rect.Y, v.Rect.H, int32(len(v.Lines))})
		}
	}
	return dividers, dividerY, rows
}

func TestRequirementEscapesAndForcedBreaksAffectSize(t *testing.T) {
	profile := scene.ProfileVector
	paddingX, paddingY := requirementPadding(profile, "padding_x"), requirementPadding(profile, "padding_y")
	height := int64(requirementLineHeight(profile))
	assertRequirementSize(t, `\*x`, profile, geom.Size{W: semiBoldWidth(t, "*x") + paddingX, H: int32(height) + paddingY})
	a, b := semiBoldWidth(t, "a"), semiBoldWidth(t, "b")
	assertRequirementSize(t, "a<br>b", profile, geom.Size{W: max(a, b) + paddingX, H: int32(2*height) + paddingY})
	items, err := requirementTableItems("a<br>b\nhead\nfield", geom.Rect{X: 0, Y: 0, W: 20000, H: 20000}, profile, "")
	if err != nil {
		t.Fatal(err)
	}
	startY := (paddingY - paddingY/2) / 2
	dividers, dividerY, rows := dividersAndRows(items)
	if dividers != 1 || dividerY != startY+3*int32(height)+paddingY/4 {
		t.Fatal(dividers, dividerY, startY+3*int32(height)+paddingY/4)
	}
	want := [][3]int32{{startY, 2 * int32(height), 2}, {startY + 2*int32(height), int32(height), 1}, {startY + 3*int32(height) + paddingY/2, int32(height), 1}}
	if !slices.Equal(rows, want) {
		t.Fatal(rows, want)
	}
}

func TestRequirementTableRowsAndCellDimensions(t *testing.T) {
	in := requirementInput(t, "requirementDiagram\nrequirement R {\nid: 1\ntext: hello\nrisk: low\nverifyMethod: test\n}\n", scene.ProfileCell)
	node := &in.Boxes[0]
	if node.ID != "R" || node.Shape != "requirementBox" {
		t.Fatal(node)
	}
	if node.Text != "<<Requirement>>\nR\nID: 1\nText: hello\nRisk: Low\nVerification: Test" {
		t.Fatal(node.Text)
	}
	sizes, err := requirementFamilyInput(in)
	if err != nil {
		t.Fatal(err)
	}
	if sizes.Sizes[0] != (geom.Size{W: 21, H: 8}) {
		t.Fatal(sizes.Sizes[0])
	}
}

func TestVectorTableUsesMeasuredWidthAndSinglePadding(t *testing.T) {
	size, err := requirementTableSize("A\nB", scene.ProfileVector, "")
	if err != nil {
		t.Fatal(err)
	}
	a, err := measure.VectorWidth("A", 14, measure.WeightSemiBold)
	if err != nil {
		t.Fatal(err)
	}
	b, err := measure.VectorWidth("B", 14, measure.WeightSemiBold)
	if err != nil {
		t.Fatal(err)
	}
	if size != (geom.Size{W: max(a, b) + 1280, H: 3840}) {
		t.Fatal(size)
	}
}

func TestRelationshipLabelsStrokesMarkersAndCollisionIDs(t *testing.T) {
	in := requirementInput(t, "requirementDiagram\nrequirement e0 {\n}\nelement E {\n}\ne0 - contains -> E\nE - satisfies -> e0\n", scene.ProfileCell)
	type route struct{ id, line, markerStart, markerEnd string }
	var got []route
	for _, r := range in.Routes {
		got = append(got, route{r.ID, r.Line, r.MarkerStart, r.MarkerEnd})
	}
	want := []route{{"e1", "normal", "requirement_contains", "none"}, {"e2", "dashed", "none", "requirement_arrow"}}
	if !slices.Equal(got, want) {
		t.Fatal(got)
	}
	var labels []string
	for _, l := range in.Labels {
		if len(l.Owner) > 0 && l.Owner[0] == 'e' && len(l.Text) > 1 && l.Text[:2] == "<<" {
			labels = append(labels, l.Text)
		}
	}
	if !slices.Equal(labels, []string{"<<Requirement>>\ne0", "<<contains>>", "<<satisfies>>"}) {
		t.Fatal(labels)
	}
}

func TestTableScenePreservesRowsInsideCellBorders(t *testing.T) {
	items, err := requirementTableItems("<<Element>>\nE\nType: service", geom.Rect{X: 0, Y: 0, W: 16, H: 5}, scene.ProfileCell, "")
	if err != nil {
		t.Fatal(err)
	}
	var texts []*scene.Text
	for _, item := range items {
		if text, ok := item.(*scene.Text); ok {
			texts = append(texts, text)
		}
	}
	rows := make([]int32, len(texts))
	for i, text := range texts {
		rows[i] = text.Rect.Y
	}
	if !slices.Equal(rows, []int32{1, 2, 3}) {
		t.Fatal(rows)
	}
	if texts[0].Align != scene.AlignMiddle || texts[len(texts)-1].Align != scene.AlignStart {
		t.Fatal(texts[0].Align, texts[len(texts)-1].Align)
	}
}
