package svg

import (
	"os"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func shapeRow(name string) (string, bool) {
	for _, s := range gen.Shapes {
		if s.ID == name || slices.Contains(s.Aliases, name) {
			return s.ID, true
		}
	}
	return "", false
}

func readShapeDefs(t *testing.T) [][]string {
	t.Helper()
	data, err := os.ReadFile("testdata/shapes_defs.txt")
	if err != nil {
		t.Fatal(err)
	}
	var entries [][]string
	for line := range strings.SplitSeq(strings.TrimSuffix(string(data), "\n"), "\n") {
		fields := strings.Split(line, "|")
		if len(fields) != 3 {
			t.Fatalf("bad fixture line %q", line)
		}
		entries = append(entries, fields)
	}
	return entries
}

func assertEntryNamesResolve(t *testing.T, fields []string) int {
	t.Helper()
	names := append([]string{fields[0]}, splitNames(fields[1], fields[2])...)
	want := ""
	for _, name := range names {
		id, ok := shapeRow(name)
		if !ok {
			t.Errorf("%s of %s resolves to no shapes.json row", name, fields[0])
		}
		if want == "" {
			want = id
		}
		if id != want {
			t.Errorf("%s resolves to %s, but %s resolves to %s", name, id, fields[0], want)
		}
	}
	return len(names)
}

func TestShapeShortNames(t *testing.T) {
	entries := readShapeDefs(t)
	names := 0
	for _, fields := range entries {
		names += assertEntryNamesResolve(t, fields)
	}
	if len(entries) != 53 || names != 155 {
		t.Errorf("fixture holds %d entries and %d names, want 53 and 155", len(entries), names)
	}
}

func splitNames(lists ...string) []string {
	var out []string
	for _, list := range lists {
		if list != "" {
			out = append(out, strings.Split(list, ",")...)
		}
	}
	return out
}

func TestBracketFormShapesResolve(t *testing.T) {
	for _, name := range []string{"squareRect", "roundedRect", "circle", "doublecircle", "stadium", "subroutine", "rect", "cylinder", "diamond", "hexagon", "odd", "trapezoid", "inv_trapezoid", "lean_right", "lean_left", "ellipse"} {
		if _, ok := shapeRow(name); !ok {
			t.Errorf("bracket form shape %s has no row", name)
		}
	}
}

var upstreamMarkers = []string{
	"extension", "composition", "aggregation", "dependency", "lollipop", "point", "circle", "cross", "barb", "barbNeo",
	"hierarchy", "only_one", "zero_or_one", "one_or_more", "zero_or_more", "only_one_neo", "zero_or_one_neo",
	"one_or_more_neo", "zero_or_more_neo", "requirement_arrow", "requirement_contains", "requirement_arrow_neo",
	"requirement_contains_neo", "openArrow", "hollowCircle",
}

var sequenceMarkers = []string{"arrowhead", "solidTopArrowHead", "solidBottomArrowHead", "filled-head", "stickTopArrowHead", "stickBottomArrowHead", "crosshead"}

var markerPaint = map[string]struct{ tag, class string }{
	"filled": {"polygon", "emd-s-mark"},
	"hollow": {"polygon", "emd-s-mark-hollow"},
	"open":   {"polyline", "emd-s-edge"},
}

func TestMarkerKinds(t *testing.T) {
	seen := map[string]bool{}
	for _, m := range gen.Markers {
		if seen[m.Name] {
			t.Errorf("duplicate marker %s", m.Name)
		}
		seen[m.Name] = true
		assertMarkerRow(t, m)
		want := markerPaint[m.Paint]
		for axis := range 4 {
			r := renderer{used: make(map[string]bool)}
			got, err := r.marker(&scene.MarkerRef{Marker: m.Name, At: geom.Point{X: 640, Y: 640}, Axis: scene.Axis(axis)}, 0)
			if err != nil || !strings.HasPrefix(got, "<"+want.tag+" class='"+want.class+"' points='") {
				t.Errorf("%s axis %d: %q (%v)", m.Name, axis, got, err)
			}
		}
	}
	for _, name := range slices.Concat(upstreamMarkers, sequenceMarkers) {
		if !seen[name] {
			t.Errorf("marker %s missing", name)
		}
	}
	if len(gen.Markers) != len(upstreamMarkers)+len(sequenceMarkers) {
		t.Errorf("%d marker rows, want %d", len(gen.Markers), len(upstreamMarkers)+len(sequenceMarkers))
	}
}

func assertMarkerRow(t *testing.T, m gen.Marker) {
	t.Helper()
	if !slices.Contains([]string{"filled", "hollow", "open"}, m.Paint) {
		t.Errorf("%s: paint %q", m.Name, m.Paint)
	}
	if len(m.Cell) != 4 || len(m.Ascii) != 4 || slices.Contains(m.Cell, 0) || slices.Contains(m.Ascii, 0) {
		t.Errorf("%s: cell %v ascii %v must hold four glyphs each", m.Name, m.Cell, m.Ascii)
	}
	if len(m.Points) < 2 {
		t.Fatalf("%s: %d points", m.Name, len(m.Points))
	}
	assertMarkerRef(t, m)
	start := uint32(0)
	for _, end := range append(slices.Clone(m.Breaks), uint32(len(m.Points))) {
		if end < start+2 || int(end) > len(m.Points) {
			t.Errorf("%s: contour %d..%d is shorter than two points", m.Name, start, end)
		}
		start = end
	}
}

func assertMarkerRef(t *testing.T, m gen.Marker) {
	t.Helper()
	lo, hi := m.Points[0], m.Points[0]
	for _, p := range m.Points {
		lo = [2]int32{min(lo[0], p[0]), min(lo[1], p[1])}
		hi = [2]int32{max(hi[0], p[0]), max(hi[1], p[1])}
	}
	if m.Ref[0] < lo[0] || m.Ref[0] > hi[0] || m.Ref[1] < lo[1] || m.Ref[1] > hi[1] {
		t.Errorf("%s: ref %v outside outline %v..%v", m.Name, m.Ref, lo, hi)
	}
}
