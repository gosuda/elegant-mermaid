package cells

import (
	"errors"
	"os"
	"regexp"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func cellScene(w, h int32, items ...scene.Primitive) scene.Scene {
	return scene.Scene{Dump: scene.Dump{Options: scene.Options{Profile: scene.ProfileCell}, Canvas: geom.Size{W: w, H: h}}, Groups: []*scene.Group{{Items: items}}}
}
func edge(ps ...geom.Point) *scene.Polyline {
	return &scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: ps}
}
func label(x, y, w int32, text string) *scene.Text {
	return &scene.Text{Rect: geom.Rect{X: x, Y: y, W: w, H: 1}, Align: scene.AlignMiddle, Lines: [][]scene.Run{{{Text: text}}}}
}
func TestRenderHandOracles(t *testing.T) {
	box := &scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{W: 7, H: 3}}
	cases := []struct {
		name string
		s    scene.Scene
		want string
	}{
		{"centred", cellScene(7, 3, box, label(0, 1, 7, "Hi")), "┌─────┐\n│ Hi  │\n└─────┘\n"},
		{"L", cellScene(5, 4, edge(geom.Point{X: 0, Y: 0}, geom.Point{X: 3, Y: 0}, geom.Point{X: 3, Y: 2})), "╶──┐\n   │\n   ╵\n\n"},
		{"T", cellScene(5, 3, edge(geom.Point{X: 0, Y: 0}, geom.Point{X: 4, Y: 0}), edge(geom.Point{X: 2, Y: 0}, geom.Point{X: 2, Y: 2})), "╶─┬─╴\n  │\n  ╵\n"},
		{"cross", cellScene(5, 3, edge(geom.Point{X: 0, Y: 1}, geom.Point{X: 4, Y: 1}), edge(geom.Point{X: 2, Y: 0}, geom.Point{X: 2, Y: 2})), "  ╷\n╶─┼─╴\n  ╵\n"},
		{"rounded", cellScene(7, 3, &scene.RoundRect{Shape: box.Shape, Rect: box.Rect}), "╭─────╮\n│     │\n╰─────╯\n"},
		{"wide", cellScene(10, 3, &scene.Rect{Shape: box.Shape, Rect: geom.Rect{W: 10, H: 3}}, label(0, 1, 10, "日本語")), "┌────────┐\n│ 日本語 │\n└────────┘\n"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got, err := Render(tc.s, Options{})
			if err != nil {
				t.Fatal(err)
			}
			if string(got.Text) != tc.want {
				t.Fatalf("got %q want %q", got.Text, tc.want)
			}
			if got.RefusedClusters != 0 {
				t.Fatal(got.RefusedClusters)
			}
		})
	}
}
func TestRenderMarkerDirections(t *testing.T) {
	for axis, want := range []string{"╶─▶\n", "◀─╴\n", "╷\n│\n▼\n", "▲\n│\n╵\n"} {
		s := markerScene(axis)
		for _, charset := range []Charset{CharsetUnicode, CharsetASCII} {
			r, e := Render(s, Options{Charset: charset})
			if e != nil {
				t.Fatal(e)
			}
			expected := want
			if charset == CharsetASCII {
				expected = strings.NewReplacer("╶", "-", "─", "-", "╴", "-", "╷", "|", "│", "|", "╵", "|", "▶", ">", "◀", "<", "▼", "v", "▲", "^").Replace(want)
			}
			if string(r.Text) != expected {
				t.Fatalf("axis %d got %q want %q", axis, r.Text, expected)
			}
		}
	}
}
func markerScene(axis int) scene.Scene {
	a, b := geom.Point{}, geom.Point{X: 2}
	at := b
	switch axis {
	case 1:
		at = a
	case 2:
		b = geom.Point{Y: 2}
		at = b
	case 3:
		b = geom.Point{Y: 2}
		at = a
	}
	w, h := int32(3), int32(1)
	if axis >= 2 {
		w, h = 1, 3
	}
	return cellScene(w, h, edge(a, b), &scene.MarkerRef{Marker: "point", At: at, Axis: scene.Axis(axis)})
}
func TestRenderLabelGuard(t *testing.T) {
	s := cellScene(3, 1, edge(geom.Point{}, geom.Point{X: 2}), label(0, 0, 3, "abc"))
	r, e := Render(s, Options{})
	if e != nil {
		t.Fatal(e)
	}
	if r.RefusedClusters != 3 || string(r.Text) != "╶─╴\n" {
		t.Fatalf("%+v", r)
	}
}
func TestMarkerSymbolCellWidth(t *testing.T) {
	glyphs := []rune{'┄', '┆', '⣿'}
	for _, m := range gen.Markers {
		for _, g := range m.Cell {
			glyphs = append(glyphs, rune(g))
		}
	}
	for _, s := range gen.CellSymbols {
		glyphs = append(glyphs, rune(s.Unicode))
	}
	for _, g := range glyphs {
		w, e := measure.CellWidth(string(g))
		if e != nil || w != 1 {
			t.Fatalf("%U width %d: %v", g, w, e)
		}
	}
}
func TestRenderProperties(t *testing.T) {
	sgr := regexp.MustCompile("\x1b\\[[0-9;]*m")
	for seed := uint32(1); seed <= 100; seed++ {
		state := seed
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		n := int32(state%8 + 2)
		items := []scene.Primitive{}
		for x := int32(0); x < n; x++ {
			items = append(items, &scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{X: x * 6, W: 5, H: 3}}, label(x*6, 1, 5, "A"))
		}
		s := cellScene(n*6, 4, items...)
		plain, e := Render(s, Options{Charset: CharsetASCII})
		if e != nil {
			t.Fatal(e)
		}
		col, e := Render(s, Options{Charset: CharsetASCII, Color: ColorTruecolor})
		if e != nil {
			t.Fatal(e)
		}
		if string(sgr.ReplaceAll(col.Text, nil)) != string(plain.Text) {
			t.Fatal("colour changed text")
		}
		checkRows(t, plain.Text)
	}
	_, e := Render(scene.Scene{}, Options{})
	if _, ok := errors.AsType[*ProfileError](e); !ok {
		t.Fatal(e)
	}
}
func checkRows(t *testing.T, text []byte) {
	t.Helper()
	if strings.Count(string(text), "\n") != 4 {
		t.Fatal("height")
	}
	for line := range strings.SplitSeq(string(text), "\n") {
		if strings.HasSuffix(line, " ") {
			t.Fatal("trailing space")
		}
	}
	for _, b := range text {
		if b >= 128 {
			t.Fatal("non ASCII")
		}
	}
}

func TestDemoLeftToRight(t *testing.T) {
	items := []scene.Primitive{}
	for _, b := range []struct {
		x, w int32
		text string
	}{{0, 9, "Start"}, {12, 10, "Choice"}, {25, 8, "Done"}} {
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{X: b.x, W: b.w, H: 3}}, label(b.x, 1, b.w, b.text))
	}
	items = append(items, edge(geom.Point{X: 8, Y: 1}, geom.Point{X: 12, Y: 1}), edge(geom.Point{X: 21, Y: 1}, geom.Point{X: 25, Y: 1}), &scene.MarkerRef{Marker: "point", At: geom.Point{X: 12, Y: 1}}, &scene.MarkerRef{Marker: "point", At: geom.Point{X: 25, Y: 1}})
	want, err := os.ReadFile("testdata/render/demo.txt")
	if err != nil {
		t.Fatal(err)
	}
	got, err := Render(cellScene(33, 3, items...), Options{})
	if err != nil {
		t.Fatal(err)
	}
	if string(got.Text) != string(want) {
		t.Fatalf("got %q want %q", got.Text, want)
	}
}
func TestDottedLine(t *testing.T) {
	p := edge(geom.Point{}, geom.Point{X: 4})
	p.Line = scene.LineDashed
	p.Width.Kind = scene.WidthEmphasis
	for _, tc := range []struct {
		charset Charset
		want    string
	}{{CharsetUnicode, "╶┄┄┄╴\n"}, {CharsetASCII, ".....\n"}} {
		got, err := Render(cellScene(5, 1, p), Options{Charset: tc.charset})
		if err != nil {
			t.Fatal(err)
		}
		if string(got.Text) != tc.want {
			t.Fatalf("%q", got.Text)
		}
	}
}
