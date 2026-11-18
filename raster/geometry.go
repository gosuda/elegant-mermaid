package raster

import (
	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type (
	point   struct{ x, y float64 }
	contour struct {
		points []point
		closed bool
	}
)

func pointsOf(ps []geom.Point) []point {
	out := make([]point, len(ps))
	for i, p := range ps {
		out[i] = point{float64(p.X), float64(p.Y)}
	}
	return out
}

func rectangle(b geom.Rect) []point {
	x, y, w, h := float64(b.X), float64(b.Y), float64(b.W), float64(b.H)
	return []point{{x, y}, {x + w, y}, {x + w, y + h}, {x, y + h}}
}

func (r *renderer) primitive(p scene.Primitive) error {
	switch v := p.(type) {
	case *scene.Text:
		return r.text(v)
	case *scene.MarkerRef:
		return r.marker(v)
	case *scene.SymbolRef:
		return badConfig("symbol in vector scene")
	default:
		shape, paths, err := geometry(p)
		if err != nil {
			return err
		}
		return r.shape(shape, paths)
	}
}

func geometry(p scene.Primitive) (scene.Shape, []contour, error) {
	switch v := p.(type) {
	case *scene.Rect:
		return v.Shape, []contour{{rectangle(v.Rect), true}}, nil
	case *scene.RoundRect:
		ps, err := roundRectangle(v)
		return v.Shape, []contour{{ps, true}}, err
	case *scene.Ellipse:
		ps, err := cells.Ellipse(geom.Point{X: v.CX, Y: v.CY}, v.RX, v.RY)
		return v.Shape, []contour{{pointsOf(ps), true}}, err
	case *scene.Polygon:
		return v.Shape, []contour{{pointsOf(v.Points), true}}, nil
	case *scene.Polyline:
		ps, err := roundedPolyline(v)
		return v.Shape, []contour{{ps, false}}, err
	case *scene.Path:
		ps, err := pathContours(v.Commands)
		return v.Shape, ps, err
	default:
		return scene.Shape{}, nil, badConfig("unknown primitive")
	}
}

func roundRectangle(v *scene.RoundRect) ([]point, error) {
	b := v.Rect
	rad := min(max(v.R, 0), b.W/2, b.H/2)
	if rad == 0 {
		return rectangle(b), nil
	}
	centers := []geom.Point{{X: b.X + b.W - rad, Y: b.Y + rad}, {X: b.X + b.W - rad, Y: b.Y + b.H - rad}, {X: b.X + rad, Y: b.Y + b.H - rad}, {X: b.X + rad, Y: b.Y + rad}}
	var out []point
	for i, c := range centers {
		ps, err := cells.Arc(c, rad, int32(i*16384-16384), 16384)
		if err != nil {
			return nil, badConfig(err.Error())
		}
		out = append(out, pointsOf(ps)...)
	}
	return out, nil
}

type pathBuilder struct {
	contours []contour
	current  geom.Point
	start    geom.Point
}

func pathContours(commands []scene.Command) ([]contour, error) {
	var path pathBuilder
	for _, command := range commands {
		if err := path.command(command); err != nil {
			return nil, err
		}
	}
	return path.contours, nil
}

func (b *pathBuilder) command(command scene.Command) error {
	switch v := command.(type) {
	case *scene.MoveTo:
		b.current = v.P
		b.start = v.P
		b.contours = append(b.contours, contour{points: pointsOf([]geom.Point{v.P})})
		return nil
	case *scene.ClosePath:
		if len(b.contours) == 0 {
			return badConfig("path missing move")
		}
		b.contours[len(b.contours)-1].closed = true
		b.current = b.start
		return nil
	default:
		return b.extend(command)
	}
}

func (b *pathBuilder) extend(command scene.Command) error {
	if len(b.contours) == 0 {
		return badConfig("path missing move")
	}
	if b.contours[len(b.contours)-1].closed {
		b.contours = append(b.contours, contour{points: pointsOf([]geom.Point{b.current})})
	}
	ps, err := commandPoints(command, b.current)
	if err != nil {
		return err
	}
	last := &b.contours[len(b.contours)-1]
	last.points = append(last.points, pointsOf(ps)...)
	if len(ps) > 0 {
		b.current = ps[len(ps)-1]
	}
	return nil
}

func commandPoints(c scene.Command, current geom.Point) ([]geom.Point, error) {
	switch v := c.(type) {
	case *scene.LineTo:
		return []geom.Point{v.P}, nil
	case *scene.CubicTo:
		return cells.Cubic([4]geom.Point{current, v.C1, v.C2, v.P})
	case *scene.ArcTo:
		return cells.Arc(geom.Point{X: v.CX, Y: v.CY}, v.R, v.A0, v.Sweep)
	default:
		return nil, badConfig("unknown path command")
	}
}

func (r *renderer) shape(s scene.Shape, paths []contour) error {
	row, err := style(s.Style)
	if err != nil {
		return err
	}
	if row.Fill != "none" {
		alpha := uint8(255)
		if row.Tint == 1 {
			alpha = uint8(constant("paint.tint_alpha"))
		}
		ink, err := r.fillPaint(row.Fill, s.Series, alpha)
		if err != nil {
			return err
		}
		r.fill(paths, ink)
	}
	if row.Stroke == "none" {
		return nil
	}
	alpha := uint8(255)
	if row.Tint == 2 {
		alpha = uint8(constant("paint.tint_alpha"))
	}
	ink, err := r.strokePaint(row.Stroke, s.Series, alpha)
	if err != nil {
		return err
	}
	r.fill(strokeContours(paths, width(s.Width), s.Line), ink)
	return nil
}

func width(w scene.Width) float64 {
	switch w.Kind {
	case scene.WidthEmphasis:
		return 128
	case scene.WidthUnits:
		return float64(w.Units)
	default:
		return 64
	}
}

func (r *renderer) marker(m *scene.MarkerRef) error {
	for _, row := range gen.Markers {
		if row.Name == m.Marker {
			return r.markerRow(m, row)
		}
	}
	return badConfig("unknown marker " + m.Marker)
}

func (r *renderer) markerRow(m *scene.MarkerRef, row gen.Marker) error {
	paths := []contour{{closed: row.Paint != "open"}}
	for i, p := range row.Points {
		if markerBreak(row.Breaks, i) {
			paths = append(paths, contour{})
		}
		x, y := float64(p[0]-row.Ref[0]), float64(p[1]-row.Ref[1])
		x, y = rotate(x, y, m.Axis)
		last := &paths[len(paths)-1]
		last.points = append(last.points, point{x + float64(m.At.X), y + float64(m.At.Y)})
	}
	name := "edge"
	switch row.Paint {
	case "filled":
		name = "mark"
	case "hollow":
		name = "mark-hollow"
	}
	return r.shape(scene.Shape{Style: name}, paths)
}

func markerBreak(breaks []uint32, i int) bool {
	for _, b := range breaks {
		if int(b) == i {
			return true
		}
	}
	return false
}

func rotate(x, y float64, axis scene.Axis) (float64, float64) {
	switch axis {
	case scene.AxisMinusX:
		return -x, -y
	case scene.AxisPlusY:
		return -y, x
	case scene.AxisMinusY:
		return y, -x
	default:
		return x, y
	}
}

func roundedPolyline(v *scene.Polyline) ([]point, error) {
	var out []point
	for i, p := range v.Points {
		if i == 0 || i+1 == len(v.Points) || v.Corner <= 0 {
			out = append(out, point{float64(p.X), float64(p.Y)})
			continue
		}
		ps, err := roundedCorner(v.Points[i-1], p, v.Points[i+1], v.Corner)
		if err != nil {
			return nil, err
		}
		out = append(out, ps...)
	}
	return out, nil
}

func axisDirection(a, b geom.Point) (geom.Point, int64) {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	length := abs64(dx) + abs64(dy)
	return geom.Point{X: int32(sign64(dx)), Y: int32(sign64(dy))}, length
}

func sign64(v int64) int64 {
	if v < 0 {
		return -1
	}
	if v > 0 {
		return 1
	}
	return 0
}

func abs64(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func roundedCorner(a, p, b geom.Point, limit int32) ([]point, error) {
	u, l1 := axisDirection(a, p)
	v, l2 := axisDirection(p, b)
	cross := u.X*v.Y - u.Y*v.X
	radius := min(int64(limit), int64(512), min(l1, l2)/2)
	if cross == 0 || abs64(int64(u.X))+abs64(int64(u.Y)) != 1 || abs64(int64(v.X))+abs64(int64(v.Y)) != 1 || radius <= 0 {
		return []point{{float64(p.X), float64(p.Y)}}, nil
	}
	cx := int64(p.X) - radius*int64(u.X) + radius*int64(v.X)
	cy := int64(p.Y) - radius*int64(u.Y) + radius*int64(v.Y)
	angle := arcStart(v)
	sweep := int32(16384)
	if cross < 0 {
		sweep = -sweep
	}
	ps, err := cells.Arc(geom.Point{X: int32(cx), Y: int32(cy)}, int32(radius), angle, sweep)
	return pointsOf(ps), err
}

func arcStart(v geom.Point) int32 {
	switch {
	case v.X > 0:
		return 32768
	case v.X < 0:
		return 0
	case v.Y > 0:
		return 49152
	default:
		return 16384
	}
}
