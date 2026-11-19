package cells

import (
	"errors"
	"math"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type dotSet map[[2]int]bool

func vectorScene(w, h int32, items ...scene.Primitive) scene.Scene {
	return scene.Scene{Dump: scene.Dump{Options: scene.Options{Profile: scene.ProfileVector}, Canvas: geom.Size{W: w, H: h}}, Groups: []*scene.Group{{Items: items}}}
}

func addCellDots(out dotSet, col, row int, bits uint8) {
	for dx := range 2 {
		for dy := range 4 {
			if bits&DotBit(dx, dy) != 0 {
				out[[2]int{2*col + dx, 4*row + dy}] = true
			}
		}
	}
}

func dotsOf(t *testing.T, w, h int, text string) dotSet {
	t.Helper()
	out := dotSet{}
	rows := strings.Split(strings.TrimSuffix(text, "\n"), "\n")
	if len(rows) > h {
		t.Fatalf("%d rows for height %d", len(rows), h)
	}
	for r, row := range rows {
		glyphs := []rune(row)
		if len(glyphs) > w {
			t.Fatalf("%d columns for width %d", len(glyphs), w)
		}
		for col, g := range glyphs {
			if g >= 0x2800 && g < 0x2900 {
				addCellDots(out, col, r, uint8(g-0x2800))
			}
		}
	}
	return out
}

func sameDots(t *testing.T, got, want dotSet) {
	t.Helper()
	for d := range want {
		if !got[d] {
			t.Fatalf("missing dot %v", d)
		}
	}
	for d := range got {
		if !want[d] {
			t.Fatalf("extra dot %v", d)
		}
	}
}

func oracleInside(ring []geom.Point, px, py int) bool {
	count := 0
	for i, a := range ring {
		b := ring[(i+1)%len(ring)]
		ay, by := int(a.Y), int(b.Y)
		if (ay > py || py >= by) && (by > py || py >= ay) {
			continue
		}
		lhs := (int(b.X)-int(a.X))*(py-ay) + (int(a.X)-px)*(by-ay)
		if lhs*(by-ay) > 0 {
			count++
		}
	}
	return count%2 == 1
}

func oracleFill(ring []geom.Point, columns, rows int) dotSet {
	out := dotSet{}
	for j := range rows * 4 {
		for i := range columns * 2 {
			if oracleInside(ring, 256*i+128, 256*j+128) {
				out[[2]int{i, j}] = true
			}
		}
	}
	return out
}

func oracleLine(x0, y0, x1, y1 int, out dotSet) {
	dx, dy := int(math.Abs(float64(x1-x0))), -int(math.Abs(float64(y1-y0)))
	sx, sy := -1, -1
	if x0 < x1 {
		sx = 1
	}
	if y0 < y1 {
		sy = 1
	}
	e := dx + dy
	for {
		out[[2]int{x0, y0}] = true
		if x0 == x1 && y0 == y1 {
			return
		}
		e2 := 2 * e
		if e2 >= dy {
			e += dy
			x0 += sx
		}
		if e2 <= dx {
			e += dx
			y0 += sy
		}
	}
}

func oracleStroke(ring []geom.Point, closed bool, out dotSet) {
	n := len(ring)
	if closed {
		n++
	}
	for i := 1; i < n; i++ {
		a, b := ring[(i-1)%len(ring)], ring[i%len(ring)]
		oracleLine(int(a.X)>>8, int(a.Y)>>8, int(b.X)>>8, int(b.Y)>>8, out)
	}
}

func renderDots(t *testing.T, s scene.Scene) (dotSet, Result) {
	t.Helper()
	r, err := Render(s, Options{})
	if err != nil {
		t.Fatal(err)
	}
	w, h := int((s.Canvas.W+511)/512), int((s.Canvas.H+1023)/1024)
	return dotsOf(t, w, h, string(r.Text)), r
}

func TestBrailleRenderCircleFill(t *testing.T) {
	c := geom.Point{X: 5 * 512, Y: 3 * 1024}
	rx, ry := int32(4*512), int32(3*1024)
	ring := make([]geom.Point, 64)
	for j := range ring {
		a := int32(j * 1024)
		ring[j] = geom.Point{X: c.X + int32(geom.FloorDiv(int64(rx)*int64(geom.CosQ15(a)), 32768)), Y: c.Y - int32(geom.FloorDiv(int64(ry)*int64(geom.SinQ15(a)), 32768))}
	}
	s := vectorScene(10*512, 6*1024, &scene.Ellipse{Shape: scene.Shape{Style: "ink"}, CX: c.X, CY: c.Y, RX: rx, RY: ry})
	got, _ := renderDots(t, s)
	want := oracleFill(ring, 10, 6)
	sameDots(t, got, want)
	if len(want) < 100 {
		t.Fatal("oracle drew too little", len(want))
	}
}

func TestBrailleRenderSeriesFillAndOutline(t *testing.T) {
	r := geom.Rect{X: 300, Y: 500, W: 1700, H: 1500}
	ring := []geom.Point{{X: 300, Y: 500}, {X: 2000, Y: 500}, {X: 2000, Y: 2000}, {X: 300, Y: 2000}}
	s := vectorScene(4*512, 3*1024, &scene.Rect{Shape: scene.Shape{Style: "series"}, Rect: r})
	got, _ := renderDots(t, s)
	want := oracleFill(ring, 4, 3)
	oracleStroke(ring, true, want)
	sameDots(t, got, want)
}

func TestBrailleRenderDiagonalStroke(t *testing.T) {
	a, b := geom.Point{X: 130, Y: 70}, geom.Point{X: 2900, Y: 3700}
	s := vectorScene(6*512, 4*1024, &scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: []geom.Point{a, b}})
	got, _ := renderDots(t, s)
	want := dotSet{}
	oracleStroke([]geom.Point{a, b}, false, want)
	sameDots(t, got, want)
	if !got[[2]int{0, 0}] || !got[[2]int{11, 14}] {
		t.Fatal("endpoints")
	}
}

func TestBrailleRenderStyleParts(t *testing.T) {
	ring := []geom.Point{{X: 256, Y: 256}, {X: 1792, Y: 256}, {X: 1792, Y: 1792}, {X: 256, Y: 1792}}
	fillOnly, outlineOnly := oracleFill(ring, 4, 2), dotSet{}
	oracleStroke(ring, true, outlineOnly)
	for _, tc := range []struct {
		style string
		want  dotSet
	}{{"ink", fillOnly}, {"node", outlineOnly}, {"series-tint", outlineOnly}, {"band", dotSet{}}} {
		s := vectorScene(4*512, 2*1024, &scene.Rect{Shape: scene.Shape{Style: tc.style}, Rect: geom.Rect{X: 256, Y: 256, W: 1536, H: 1536}})
		got, _ := renderDots(t, s)
		sameDots(t, got, tc.want)
	}
}

func TestBraillePathArcSlice(t *testing.T) {
	centre := geom.Point{X: 2048, Y: 2048}
	start := geom.Point{X: 2048, Y: 2048 - 1536}
	path := &scene.Path{Shape: scene.Shape{Style: "series", Series: 1}, Commands: []scene.Command{
		&scene.MoveTo{P: centre}, &scene.LineTo{P: start}, &scene.ArcTo{CX: centre.X, CY: centre.Y, R: 1536, A0: -16384, Sweep: 16384}, &scene.ClosePath{},
	}}
	s := vectorScene(8*512, 4*1024, path)
	got, _ := renderDots(t, s)
	arc, err := Arc(centre, 1536, -16384, 16384)
	if err != nil {
		t.Fatal(err)
	}
	ring := append([]geom.Point{centre, start}, arc...)
	want := oracleFill(ring, 8, 4)
	oracleStroke(ring, true, want)
	sameDots(t, got, want)
	if !got[[2]int{8, 4}] {
		t.Fatal("slice must cover the dot right of the centre")
	}
}

func TestBrailleCubicSegments(t *testing.T) {
	p := [4]geom.Point{{X: 0, Y: 1500}, {X: 1500, Y: 1500}, {X: 1500, Y: 300}, {X: 3000, Y: 300}}
	path := &scene.Path{Shape: scene.Shape{Style: "series-flow", Series: 2}, Commands: []scene.Command{&scene.MoveTo{P: p[0]}, &scene.CubicTo{C1: p[1], C2: p[2], P: p[3]}}}
	s := vectorScene(6*512, 2*1024, path)
	got, _ := renderDots(t, s)
	pts := make([]geom.Point, 17)
	for k := range int64(17) {
		t3 := 16 - k
		pts[k] = geom.Point{
			X: int32(geom.FloorDiv(t3*t3*t3*int64(p[0].X)+3*k*t3*t3*int64(p[1].X)+3*k*k*t3*int64(p[2].X)+k*k*k*int64(p[3].X)+2048, 4096)),
			Y: int32(geom.FloorDiv(t3*t3*t3*int64(p[0].Y)+3*k*t3*t3*int64(p[1].Y)+3*k*k*t3*int64(p[2].Y)+k*k*k*int64(p[3].Y)+2048, 4096)),
		}
	}
	want := dotSet{}
	oracleStroke(pts, false, want)
	sameDots(t, got, want)
}

func TestBrailleCanvasSize(t *testing.T) {
	for _, tc := range []struct {
		w, h       int32
		cols, rows int
	}{{0, 0, 0, 0}, {1, 1, 1, 1}, {512, 1024, 1, 1}, {513, 1025, 2, 2}, {5120, 2048, 10, 2}} {
		r, err := Render(vectorScene(tc.w, tc.h, &scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: geom.Rect{W: tc.w, H: tc.h}}), Options{})
		if err != nil {
			t.Fatal(err)
		}
		if tc.rows == 0 && len(r.Text) != 0 {
			t.Fatalf("%q", r.Text)
		}
		if got := strings.Count(string(r.Text), "\n"); got != tc.rows {
			t.Fatalf("%dx%d: %d rows", tc.w, tc.h, got)
		}
	}
}

func TestBrailleGlyphsAndASCII(t *testing.T) {
	s := vectorScene(1024, 1024, &scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: geom.Rect{W: 512, H: 1024}})
	u, err := Render(s, Options{})
	if err != nil {
		t.Fatal(err)
	}
	a, err := Render(s, Options{Charset: CharsetASCII})
	if err != nil {
		t.Fatal(err)
	}
	if string(u.Text) != "⣿\n" || string(a.Text) != "#\n" {
		t.Fatalf("%q %q", u.Text, a.Text)
	}
}

func textItem(x, y, w int32, align scene.Align, role scene.TextRole, lines ...string) *scene.Text {
	runs := make([][]scene.Run, len(lines))
	for i, l := range lines {
		runs[i] = []scene.Run{{Text: l}}
	}
	return &scene.Text{Rect: geom.Rect{X: x, Y: y, W: w, H: int32(len(lines)) * 1280}, Role: role, Size: 14, Align: align, Style: "text", Lines: runs}
}

func TestBrailleLabelPlacement(t *testing.T) {
	cases := []struct {
		name    string
		rows    int32
		item    *scene.Text
		want    string
		refused int
	}{
		{"start", 3, textItem(1024, 1024, 2048, scene.AlignStart, scene.TextRoleLabel, "ab"), "\n  ab\n\n", 0},
		{"middle", 3, textItem(0, 0, 5*512, scene.AlignMiddle, scene.TextRoleLabel, "ab"), " ab\n\n\n", 0},
		{"end", 3, textItem(0, 0, 5*512, scene.AlignEnd, scene.TextRoleLabel, "ab"), "   ab\n\n\n", 0},
		{"wide-over-narrow-box", 3, textItem(512, 0, 512, scene.AlignMiddle, scene.TextRoleLabel, "abcd"), "bcd\n\n\n", 1},
		{"label-rows", 3, textItem(0, 700, 2048, scene.AlignStart, scene.TextRoleLabel, "x", "y"), "x\ny\n\n", 0},
		{"label-third-line", 3, textItem(0, 0, 2048, scene.AlignStart, scene.TextRoleLabel, "x", "y", "z"), "x\ny\nz\n", 0},
		{"title-rows", 4, textItem(0, 0, 2048, scene.AlignStart, scene.TextRoleTitle, "x", "y", "z"), "x\ny\n\nz\n", 0},
		{"below-canvas", 3, textItem(0, 3*1024, 2048, scene.AlignStart, scene.TextRoleLabel, "x"), "\n\n\n", 1},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			r, err := Render(vectorScene(7*512, tc.rows*1024, tc.item), Options{})
			if err != nil {
				t.Fatal(err)
			}
			if string(r.Text) != tc.want || r.RefusedClusters != tc.refused {
				t.Fatalf("got %q refused %d, want %q refused %d", r.Text, r.RefusedClusters, tc.want, tc.refused)
			}
		})
	}
}

func TestBrailleLabelOverDotsAndRefusal(t *testing.T) {
	full := &scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: geom.Rect{W: 4 * 512, H: 1024}}
	first := textItem(0, 0, 4*512, scene.AlignStart, scene.TextRoleLabel, "hi")
	second := textItem(512, 0, 1024, scene.AlignStart, scene.TextRoleLabel, "xyz")
	r, err := Render(vectorScene(4*512, 1024, full, first, second), Options{})
	if err != nil {
		t.Fatal(err)
	}
	if string(r.Text) != "hiyz\n" || r.RefusedClusters != 1 {
		t.Fatalf("%q refused %d", r.Text, r.RefusedClusters)
	}
	r, err = Render(vectorScene(512, 1024, textItem(-2048, 0, 512, scene.AlignStart, scene.TextRoleLabel, "ab")), Options{})
	if err != nil || r.RefusedClusters != 2 || string(r.Text) != "\n" {
		t.Fatalf("%q %d %v", r.Text, r.RefusedClusters, err)
	}
}

func TestBrailleMarkerAndErrors(t *testing.T) {
	marker := &scene.MarkerRef{Marker: "point", At: geom.Point{X: 2048, Y: 1024}, Axis: scene.AxisPlusX}
	got, _ := renderDots(t, vectorScene(5*512, 2*1024, marker))
	if len(got) == 0 {
		t.Fatal("marker drew nothing")
	}
	if _, err := Render(vectorScene(512, 1024, &scene.SymbolRef{Symbol: "disc", Style: "ink"}), Options{}); !errors.Is(err, geom.ErrDomain) {
		t.Fatal(err)
	}
	if _, err := Render(vectorScene(512, 1024, &scene.MarkerRef{Marker: "nonesuch"}), Options{}); !errors.Is(err, geom.ErrDomain) {
		t.Fatal(err)
	}
	bad := scene.Scene{Dump: scene.Dump{Options: scene.Options{Profile: scene.Profile(9)}}}
	if _, err := Render(bad, Options{}); err == nil {
		t.Fatal("unknown profile accepted")
	} else if pe, ok := errors.AsType[*ProfileError](err); !ok || pe.Got != scene.Profile(9) {
		t.Fatal(err)
	}
	if _, err := RenderBraille(cellScene(2, 2), Options{}); err == nil {
		t.Fatal("cell scene accepted by braille renderer")
	}
}

func TestBrailleFillWindowEqualsFullScan(t *testing.T) {
	state := uint32(7)
	next := func(n int32) int32 {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		return int32(state % uint32(n))
	}
	for range 200 {
		ring := make([]geom.Point, 3+int(next(5)))
		for i := range ring {
			ring[i] = geom.Point{X: next(5000) - 600, Y: next(3500) - 300}
		}
		assertBrailleFillWindow(t, ring)
	}
}

func assertBrailleFillWindow(t *testing.T, ring []geom.Point) {
	t.Helper()
	c, err := NewBraille(4*512, 3*1024)
	if err != nil {
		t.Fatal(err)
	}
	if err = c.Fill(ring, TokenFG); err != nil {
		t.Fatal(err)
	}
	got := dotSet{}
	for y := range 12 {
		for x := range 8 {
			if hasDot(c, geom.Point{X: int32(x), Y: int32(y)}) {
				got[[2]int{x, y}] = true
			}
		}
	}
	sameDots(t, got, oracleFill(ring, 4, 3))
}
