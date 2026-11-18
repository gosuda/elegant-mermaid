package layout

import (
	"fmt"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const iconSource = "flowchart LR\n  A@{ icon: 'x:none', label: 'Gone' } --> B[Plain]\n"

const (
	boxPack      = `{"prefix":"t","width":24,"height":24,"icons":{"box":{"body":"<path d=\"M0 0h24v24H0z\"/>"},"bad":{"body":"<circle cx=\"1\" cy=\"1\" r=\"1\"/>"}}}`
	otherPack    = `{"prefix":"t","width":16,"height":16,"icons":{"box":{"body":"<path d=\"M0 0h16v16z\"/>"},"bad":{"body":"<path d=\"M0 0h16v16z\"/>"}}}`
	trianglePack = `{"prefix":"t","width":24,"height":24,"icons":{"box":{"body":"<path d=\"M0 0h24v24z\"/>"}}}`
	flowSource   = "flowchart LR\n  A@{ icon: '%s', label: 'L' }\n"
)

type placed struct {
	scene       scene.Scene
	diagram     *Diagram
	diagnostics []string
	spans       []int
}

func place(t *testing.T, src string, profile scene.Profile, packs ...string) placed {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		t.Fatalf("diagnostic: %+v", diagnostic)
	}
	in, err := d.Input(profile, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	var parsed []*icon.Pack
	for _, text := range packs {
		pack, err := icon.Parse([]byte(text))
		if err != nil {
			t.Fatal(err)
		}
		parsed = append(parsed, pack)
	}
	out := placed{scene: s, diagram: d}
	for _, diagnostic := range PlaceIcons(&out.scene, d.IconRefs(), parsed) {
		if diagnostic.Code != "icon/pack-missing" || diagnostic.Severity.String() != "info" {
			t.Fatalf("unexpected diagnostic %+v", diagnostic)
		}
		out.diagnostics = append(out.diagnostics, diagnostic.Message)
		out.spans = append(out.spans, diagnostic.Span.End-diagnostic.Span.Start)
	}
	return out
}

func (p placed) rect(t *testing.T, id string) geom.Rect {
	t.Helper()
	rect, ok := boxRect(&p.scene, id)
	if !ok {
		t.Fatalf("no box %s", id)
	}
	return rect
}

func (p placed) items(t *testing.T, id string) []scene.Primitive {
	t.Helper()
	group := nodeGroup(&p.scene, id)
	if group == nil {
		t.Fatalf("no node group %s", id)
	}
	return group.Items
}

func pathPoints(path *scene.Path) []geom.Point {
	var out []geom.Point
	for _, c := range path.Commands {
		switch v := c.(type) {
		case *scene.MoveTo:
			out = append(out, v.P)
		case *scene.LineTo:
			out = append(out, v.P)
		case *scene.CubicTo:
			out = append(out, v.C1, v.C2, v.P)
		}
	}
	return out
}

func inkPaths(items []scene.Primitive) []*scene.Path {
	var out []*scene.Path
	for _, item := range items {
		if path, ok := item.(*scene.Path); ok && path.Style == "ink" {
			out = append(out, path)
		}
	}
	return out
}

func bounds(points []geom.Point) geom.Rect {
	minX, minY, maxX, maxY := points[0].X, points[0].Y, points[0].X, points[0].Y
	for _, p := range points {
		minX, maxX = min(minX, p.X), max(maxX, p.X)
		minY, maxY = min(minY, p.Y), max(maxY, p.Y)
	}
	return geom.Rect{X: minX, Y: minY, W: maxX - minX, H: maxY - minY}
}

func TestPlaceIconsCentreTheBoxOnTheNodeTopEdge(t *testing.T) {
	p := place(t, fmt.Sprintf(flowSource, "t:box"), scene.ProfileVector, boxPack)
	if len(p.diagnostics) != 0 {
		t.Fatalf("diagnostics: %v", p.diagnostics)
	}
	rect := p.rect(t, "A")
	paths := inkPaths(p.items(t, "A"))
	if len(paths) != 1 {
		t.Fatalf("paths: %d", len(paths))
	}
	centre := rect.X + rect.W/2
	want := []geom.Point{{X: centre - 768, Y: rect.Y - 768}, {X: centre + 768, Y: rect.Y - 768}, {X: centre + 768, Y: rect.Y + 768}, {X: centre - 768, Y: rect.Y + 768}}
	if got := pathPoints(paths[0]); !slices.Equal(got, want) {
		t.Fatalf("box corners %v, rule says %v", got, want)
	}
}

func TestPlaceIconsCellSymbolSitsOnTheTopEdgeCentre(t *testing.T) {
	p := place(t, fmt.Sprintf(flowSource, "t:box"), scene.ProfileCell, boxPack)
	if len(p.diagnostics) != 0 {
		t.Fatalf("diagnostics: %v", p.diagnostics)
	}
	rect := p.rect(t, "A")
	var symbols []*scene.SymbolRef
	for _, item := range p.items(t, "A") {
		if symbol, ok := item.(*scene.SymbolRef); ok {
			symbols = append(symbols, symbol)
		}
	}
	want := geom.Point{X: rect.X + rect.W/2, Y: rect.Y}
	if len(symbols) != 1 || symbols[0].Symbol != "unknown" || symbols[0].Style != "ink" || symbols[0].At != want {
		t.Fatalf("symbols %+v, rule says one unknown ink symbol at %v", symbols, want)
	}
}

func TestPlaceIconsMissingCellSymbolIsInk(t *testing.T) {
	p := place(t, iconSource, scene.ProfileCell)
	rect := p.rect(t, "A")
	var symbols []*scene.SymbolRef
	for _, item := range p.items(t, "A") {
		if symbol, ok := item.(*scene.SymbolRef); ok {
			symbols = append(symbols, symbol)
		}
	}
	want := geom.Point{X: rect.X + rect.W/2, Y: rect.Y}
	if len(symbols) != 1 || symbols[0].Symbol != "unknown" || symbols[0].Style != "ink" || symbols[0].At != want {
		t.Fatalf("symbols %+v, rule says one unknown ink symbol at %v", symbols, want)
	}
}

func TestPlaceIcons(t *testing.T) {
	for _, c := range []struct {
		name  string
		packs []string
		note  bool
	}{
		{"t:box", []string{boxPack}, false},
		{"t:nothing", []string{boxPack}, true},
		{"other:box", []string{boxPack}, true},
		{"box", []string{boxPack}, true},
		{"cloud", []string{boxPack}, true},
		{"unknown", []string{boxPack}, true},
		{"t:bad", []string{boxPack}, true},
		{"t:box", nil, true},
		{"t:bad", []string{boxPack, otherPack}, true},
		{"t:bad", []string{otherPack, boxPack}, false},
		{"t:box", []string{otherPack, boxPack}, false},
	} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			p := place(t, fmt.Sprintf(flowSource, c.name), profile, c.packs...)
			want := []string(nil)
			if c.note {
				want = []string{"icon " + c.name + " is not available"}
			}
			if !slices.Equal(p.diagnostics, want) {
				t.Errorf("%s %v %d packs: diagnostics %v, rule says %v", c.name, profile, len(c.packs), p.diagnostics, want)
			}
			if len(p.spans) == 1 && p.spans[0] <= 0 {
				t.Errorf("%s: empty diagnostic span", c.name)
			}
		}
	}
}

func TestPlaceIconsFirstPackThatDefinesTheIconWins(t *testing.T) {
	cornersWith := func(packs ...string) int {
		p := place(t, fmt.Sprintf(flowSource, "t:box"), scene.ProfileVector, packs...)
		return len(pathPoints(inkPaths(p.items(t, "A"))[0]))
	}
	if got := cornersWith(boxPack, trianglePack); got != 4 {
		t.Errorf("square pack first: %d points, rule says 4", got)
	}
	if got := cornersWith(trianglePack, boxPack); got != 3 {
		t.Errorf("triangle pack first: %d points, rule says 3", got)
	}
}

func TestPlaceIconsMissingDrawsTheQuestionMarkCentredInTheBox(t *testing.T) {
	p := place(t, iconSource, scene.ProfileVector)
	rect := p.rect(t, "A")
	paths := inkPaths(p.items(t, "A"))
	if len(paths) != 1 {
		t.Fatalf("unknown glyph paths: %d", len(paths))
	}
	box := geom.Rect{X: rect.X + rect.W/2 - 768, Y: rect.Y - 768, W: 1536, H: 1536}
	got := bounds(pathPoints(paths[0]))
	if got.X < box.X || got.Y < box.Y || got.X+got.W > box.X+box.W || got.Y+got.H > box.Y+box.H {
		t.Fatalf("glyph %v leaves the box %v", got, box)
	}
	leftGap, rightGap := got.X-box.X, box.X+box.W-(got.X+got.W)
	topGap, bottomGap := got.Y-box.Y, box.Y+box.H-(got.Y+got.H)
	if abs(leftGap-rightGap) > 1 || abs(topGap-bottomGap) > 1 {
		t.Fatalf("glyph %v is not centred in %v", got, box)
	}
}

func abs(v int32) int32 {
	return max(v, -v)
}

func TestPlaceIconsKeepShapesBeforeOverlays(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		p := place(t, fmt.Sprintf(flowSource, "t:box"), profile, boxPack)
		overlay := false
		for _, item := range p.items(t, "A") {
			if overlay && !isOverlay(item) && !isIconItem(item) {
				t.Fatalf("%v: a shape follows an overlay: %T", profile, item)
			}
			overlay = overlay || isOverlay(item)
		}
	}
}

func isIconItem(item scene.Primitive) bool {
	path, ok := item.(*scene.Path)
	return ok && path.Style == "ink"
}

func TestIconRefsAreFlowchartNodesWithAnIcon(t *testing.T) {
	d := ParseDiagram([]byte("flowchart LR\n  A@{ icon: 'x:y' } --> B\n  C[Plain]\n"))
	refs := d.IconRefs()
	if len(refs) != 1 || refs[0].Owner != "A" || refs[0].Name != "x:y" || refs[0].Span.End <= refs[0].Span.Start {
		t.Fatalf("refs: %+v", refs)
	}
	if got := ParseDiagram([]byte("sequenceDiagram\n  A->>B: hi\n")).IconRefs(); got != nil {
		t.Fatalf("sequence refs: %+v", got)
	}
}
