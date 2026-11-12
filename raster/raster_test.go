package raster

import (
	"bytes"
	"context"
	"errors"
	"image"
	"image/png"
	"io/fs"
	"math"
	"os"
	"path/filepath"
	"slices"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

func firstFixture(t *testing.T, kind string) *mermaid.Scene {
	t.Helper()
	var paths []string
	err := filepath.WalkDir(filepath.Join("..", "corpus", kind), func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && filepath.Ext(path) == ".mmd" {
			paths = append(paths, path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	slices.Sort(paths)
	if len(paths) == 0 {
		t.Fatal("no corpus fixtures")
	}
	src, err := os.ReadFile(paths[0])
	if err != nil {
		t.Fatal(err)
	}
	s, err := mermaid.Layout(context.Background(), mermaid.Parse(src), mermaid.LayoutOptions{})
	if err != nil {
		t.Fatalf("%s: %v", paths[0], err)
	}
	return s
}

func decoded(t *testing.T, data []byte, err error) image.Image {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
	out, err := png.Decode(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	return out
}

func TestPNGKinds(t *testing.T) {
	for _, kind := range []string{"flowchart", "class"} {
		t.Run(kind, func(t *testing.T) {
			s := firstFixture(t, kind)
			value, _ := scenelink.Scene(s)
			for _, scale := range []int{1, 2} {
				data, err := PNG(s, Options{Scale: scale})
				img := decoded(t, data, err)
				want := image.Pt(int((int64(value.Canvas.W)*int64(scale)+63)/64), int((int64(value.Canvas.H)*int64(scale)+63)/64))
				if img.Bounds().Size() != want {
					t.Fatalf("dimensions %v != %v", img.Bounds().Size(), want)
				}
				if singleColour(img) {
					t.Fatal("PNG is a single colour")
				}
			}
		})
	}
}

func singleColour(img image.Image) bool {
	base := img.At(0, 0)
	br, bg, bb, ba := base.RGBA()
	for y := range img.Bounds().Dy() {
		for x := range img.Bounds().Dx() {
			r, g, b, a := img.At(x, y).RGBA()
			if r != br || g != bg || b != bb || a != ba {
				return false
			}
		}
	}
	return true
}

func TestPNGErrors(t *testing.T) {
	s := firstFixture(t, "flowchart")
	assertInvalidScales(t, s)
	a, err := PNG(s, Options{})
	if err != nil {
		t.Fatal(err)
	}
	b, err := PNG(s, Options{Scale: 2})
	if err != nil || !bytes.Equal(a, b) {
		t.Fatal("zero scale must mean default 2")
	}
	large := scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 16385 * 64, H: 64}}}
	_, err = encodeScene(large, Options{Scale: 1})
	if !errors.Is(err, ErrPixelsTooLarge) {
		t.Fatalf("large side: %v", err)
	}
	large.Canvas = geom.Size{W: 8193 * 64, H: 8193 * 64}
	_, err = encodeScene(large, Options{Scale: 1})
	if !errors.Is(err, ErrPixelsTooLarge) {
		t.Fatalf("large area: %v", err)
	}
	_, err = PNG(s, Options{Background: "red"})
	if !errors.Is(err, mermaid.ErrBadConfig) {
		t.Fatalf("bad background: %v", err)
	}
}

func TestPNGScanlineOracle(t *testing.T) {
	for _, kind := range []string{"flowchart", "class"} {
		t.Run(kind, func(t *testing.T) {
			s, _ := scenelink.Scene(firstFixture(t, kind))
			var shapes []scene.Primitive
			var texts []*scene.Text
			s.Groups, shapes, texts = withoutStrokes(s.Groups)
			data, err := encodeScene(s, Options{Scale: 2})
			img := decoded(t, data, err)
			assertOracleRows(t, img, shapes, texts)
		})
	}
}

func assertInvalidScales(t *testing.T, s *mermaid.Scene) {
	t.Helper()
	for _, scale := range []int{-1, 9} {
		_, err := PNG(s, Options{Scale: scale})
		typed, ok := errors.AsType[*RasterError](err)
		if !errors.Is(err, mermaid.ErrBadConfig) || !ok || typed.Kind != InvalidConfig {
			t.Fatalf("scale %d: %v", scale, err)
		}
	}
}

func assertOracleRows(t *testing.T, img image.Image, shapes []scene.Primitive, texts []*scene.Text) {
	t.Helper()
	checked := 0
	for y := range img.Bounds().Dy() {
		if textRow(texts, y) {
			continue
		}
		want := oracleRuns(shapes, y, img.Bounds().Dx())
		got := imageRuns(img, y)
		assertRunEdges(t, y, got, want)
		checked++
	}
	if checked == 0 {
		t.Fatal("oracle checked no rows")
	}
}

func assertRunEdges(t *testing.T, y int, got, want []int) {
	t.Helper()
	if len(want) != len(got) {
		t.Fatalf("row %d runs %v != %v", y, got, want)
	}
	for i := range want {
		if absInt(want[i]-got[i]) > 1 {
			t.Fatalf("row %d edges %v != %v", y, got, want)
		}
	}
}

func withoutStrokes(groups []*scene.Group) ([]*scene.Group, []scene.Primitive, []*scene.Text) {
	var out []*scene.Group
	var shapes []scene.Primitive
	var texts []*scene.Text
	for _, g := range groups {
		copyGroup := &scene.Group{Role: g.Role, Owner: g.Owner}
		for _, p := range g.Items {
			q := fillOnly(p)
			if q != nil {
				copyGroup.Items = append(copyGroup.Items, q)
				shapes = append(shapes, q)
			}
			if text, ok := p.(*scene.Text); ok {
				texts = append(texts, text)
			}
		}
		out = append(out, copyGroup)
	}
	return out, shapes, texts
}

func fillOnly(p scene.Primitive) scene.Primitive {
	zero := scene.Width{Kind: scene.WidthUnits}
	switch v := p.(type) {
	case *scene.Rect:
		q := *v
		q.Width = zero
		return &q
	case *scene.RoundRect:
		q := *v
		q.Width = zero
		return &q
	case *scene.Polygon:
		q := *v
		q.Width = zero
		return &q
	case *scene.Path:
		q := *v
		q.Width = zero
		return &q
	default:
		return nil
	}
}

func textRow(texts []*scene.Text, y int) bool {
	for _, text := range texts {
		if int64(y)*32 >= int64(text.Rect.Y)-32 && int64(y)*32 <= int64(text.Rect.Y)+int64(text.Rect.H)+32 {
			return true
		}
	}
	return false
}

func oracleRuns(shapes []scene.Primitive, y, w int) []int {
	mask := make([]bool, w)
	for _, p := range shapes {
		oracleFill(mask, p, float64(y)+0.5)
	}
	return runEdges(mask)
}

func oracleFill(mask []bool, p scene.Primitive, y float64) {
	shape := oracleShape(p)
	row, err := style(shape.Style)
	if err != nil || row.Fill == "none" {
		return
	}
	for x := range mask {
		mask[x] = mask[x] || oracleContains(p, (float64(x)+0.5)*32, y*32)
	}
}

func oracleShape(p scene.Primitive) scene.Shape {
	switch v := p.(type) {
	case *scene.Rect:
		return v.Shape
	case *scene.RoundRect:
		return v.Shape
	case *scene.Polygon:
		return v.Shape
	case *scene.Path:
		return v.Shape
	default:
		return scene.Shape{}
	}
}

func oracleContains(p scene.Primitive, x, y float64) bool {
	switch v := p.(type) {
	case *scene.Rect:
		return rectContains(v.Rect, x, y)
	case *scene.RoundRect:
		return roundedContains(v, x, y)
	case *scene.Polygon:
		return polygonContains(v.Points, x, y)
	case *scene.Path:
		return oraclePath(v.Commands, x, y)
	default:
		return false
	}
}

func rectContains(b geom.Rect, x, y float64) bool {
	return x >= float64(b.X) && x < float64(b.X)+float64(b.W) && y >= float64(b.Y) && y < float64(b.Y)+float64(b.H)
}

func roundedContains(v *scene.RoundRect, x, y float64) bool {
	if !rectContains(v.Rect, x, y) {
		return false
	}
	r := float64(min(v.R, v.Rect.W/2, v.Rect.H/2))
	cx := max(float64(v.Rect.X)+r, min(x, float64(v.Rect.X)+float64(v.Rect.W)-r))
	cy := max(float64(v.Rect.Y)+r, min(y, float64(v.Rect.Y)+float64(v.Rect.H)-r))
	return (x-cx)*(x-cx)+(y-cy)*(y-cy) <= r*r
}

func polygonContains(ps []geom.Point, x, y float64) bool {
	inside := false
	for i, b := range ps {
		a := ps[(i+len(ps)-1)%len(ps)]
		if (float64(a.Y) > y) != (float64(b.Y) > y) && x < (float64(b.X)-float64(a.X))*(y-float64(a.Y))/(float64(b.Y)-float64(a.Y))+float64(a.X) {
			inside = !inside
		}
	}
	return inside
}

func oraclePath(commands []scene.Command, x, y float64) bool {
	var polygon []geom.Point
	var current geom.Point
	inside := false
	for _, command := range commands {
		switch v := command.(type) {
		case *scene.MoveTo:
			inside = inside != polygonContains(polygon, x, y)
			polygon = []geom.Point{v.P}
			current = v.P
		case *scene.LineTo:
			polygon = append(polygon, v.P)
			current = v.P
		case *scene.CubicTo:
			polygon = append(polygon, oracleCubic(current, v)...)
			current = v.P
		case *scene.ArcTo:
			polygon = append(polygon, oracleArc(v)...)
		case *scene.ClosePath:
			inside = inside != polygonContains(polygon, x, y)
			polygon = nil
		}
	}
	return inside != polygonContains(polygon, x, y)
}

func oracleCubic(a geom.Point, c *scene.CubicTo) []geom.Point {
	var ps []geom.Point
	for k := 0; k <= 16; k++ {
		u := float64(k) / 16
		v := 1 - u
		x := v*v*v*float64(a.X) + 3*u*v*v*float64(c.C1.X) + 3*u*u*v*float64(c.C2.X) + u*u*u*float64(c.P.X)
		y := v*v*v*float64(a.Y) + 3*u*v*v*float64(c.C1.Y) + 3*u*u*v*float64(c.C2.Y) + u*u*u*float64(c.P.Y)
		ps = append(ps, geom.Point{X: int32(math.Floor(x + 0.5)), Y: int32(math.Floor(y + 0.5))})
	}
	return ps
}

func oracleArc(a *scene.ArcTo) []geom.Point {
	n := max(4, int(math.Ceil(math.Abs(float64(a.Sweep))/1024)))
	var ps []geom.Point
	for k := 0; k <= n; k++ {
		angle := (float64(a.A0) + math.Floor(float64(a.Sweep)*float64(k)/float64(n))) * 2 * math.Pi / 65536
		ps = append(ps, geom.Point{X: a.CX + int32(math.Floor(float64(a.R)*math.Cos(angle)+0.5)), Y: a.CY + int32(math.Floor(float64(a.R)*math.Sin(angle)+0.5))})
	}
	return ps
}

func imageRuns(img image.Image, y int) []int {
	mask := make([]bool, img.Bounds().Dx())
	br, bg, bb, _ := img.At(0, 0).RGBA()
	for x := range mask {
		r, g, b, _ := img.At(x, y).RGBA()
		mask[x] = r != br || g != bg || b != bb
	}
	return runEdges(mask)
}

func runEdges(mask []bool) []int {
	var out []int
	previous := false
	for x, on := range append(mask, false) {
		if on != previous {
			out = append(out, x)
			previous = on
		}
	}
	return out
}

func absInt(v int) int {
	if v < 0 {
		return -v
	}
	return v
}

func TestInterOutlines(t *testing.T) {
	outlines := InterOutlines()
	data, ok := scenelink.OutlinesOf(outlines)
	if !ok || len(data[0].Glyphs) == 0 || len(data[1].Glyphs) == 0 {
		t.Fatal("embedded outline value is empty")
	}
	regular := textInk(t, scene.Run{Text: "O"})
	bold := textInk(t, scene.Run{Text: "O", Bold: true})
	if regular == 0 || bold <= regular {
		t.Fatalf("glyph outlines: regular ink %d, bold ink %d", regular, bold)
	}
}

func textInk(t *testing.T, run scene.Run) int {
	t.Helper()
	label := &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 2560, H: 2560}, Size: 32, Role: scene.TextRoleBody, Style: "text", Lines: [][]scene.Run{{run}}}
	s := scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 3840, H: 3840}}, Groups: []*scene.Group{{Items: []scene.Primitive{label}}}}
	data, err := encodeScene(s, Options{Scale: 2})
	img := decoded(t, data, err)
	ink := 0
	for y := range img.Bounds().Dy() {
		edges := imageRuns(img, y)
		for i := 0; i < len(edges); i += 2 {
			ink += edges[i+1] - edges[i]
		}
	}
	return ink
}
