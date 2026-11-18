package scene

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

// ProjectCellAttachments projects closed route endpoints onto painted cell borders.
// It replaces display primitives without changing the canonical dump or its points.
func ProjectCellAttachments(s *Scene) {
	for _, g := range s.Groups {
		if g.Role != GroupRoleEdge {
			continue
		}
		markerIndex := 0
		for i, p := range g.Items {
			g.Items[i] = projectPrimitive(s, g.Owner, p, markerIndex)
			if _, ok := p.(*MarkerRef); ok {
				markerIndex++
			}
		}
	}
}

func attachment(s *Scene, id string, p geom.Point) geom.Point {
	for _, b := range s.Boxes {
		if b.ID == id {
			return paintedAttachment(b.Rect, p)
		}
	}
	return p
}

func paintedAttachment(r geom.Rect, p geom.Point) geom.Point {
	x, y := int64(p.X), int64(p.Y)
	right, bottom := int64(r.X)+int64(r.W), int64(r.Y)+int64(r.H)
	if r.W <= 0 || r.H <= 0 {
		return p
	}
	if x < int64(r.X) || x > right || y < int64(r.Y) || y > bottom {
		return p
	}
	if x == right {
		p.X--
	}
	if y == bottom {
		p.Y--
	}
	return p
}

type routeAttachments struct {
	first, last geom.Point
	a, b        geom.Point
}

func projectPrimitive(s *Scene, owner string, p Primitive, markerIndex int) Primitive {
	for _, r := range s.Routes {
		if r.ID != owner || len(r.Points) == 0 {
			continue
		}
		ends := routeAttachments{first: r.Points[0], last: r.Points[len(r.Points)-1]}
		ends.a = attachment(s, r.From, ends.first)
		ends.b = attachment(s, r.To, ends.last)
		switch v := p.(type) {
		case *MarkerRef:
			copy := *v
			copy.At = ends.markerPoint(v, r, markerIndex)
			return &copy
		case *Polyline:
			if !ends.matches(v.Points) {
				return p
			}
			copy := *v
			copy.Points = projectLine(v.Points, ends.a, ends.b)
			return &copy
		}
		return p
	}
	return p
}

func (e routeAttachments) matches(points []geom.Point) bool {
	if len(points) == 0 || e.a == e.first && e.b == e.last {
		return false
	}
	return points[0] == e.first && points[len(points)-1] == e.last
}

func (e routeAttachments) markerPoint(v *MarkerRef, r Route, markerIndex int) geom.Point {
	if e.first == e.last && v.At == e.first {
		target := r.MarkerEnd == v.Marker && (r.MarkerStart != v.Marker || markerIndex > 0)
		if target {
			return e.b
		}
		return e.a
	}
	switch v.At {
	case e.first:
		return e.a
	case e.last:
		return e.b
	default:
		return v.At
	}
}

func projectLine(points []geom.Point, first, last geom.Point) []geom.Point {
	out := make([]geom.Point, 0, len(points)+2)
	out = append(out, first)
	count := max(2, len(points))
	for i := 1; i < count; i++ {
		a := out[len(out)-1]
		b := points[min(i, len(points)-1)]
		if i == count-1 {
			b = last
		}
		originalA, originalB := points[i-1], points[min(i, len(points)-1)]
		segment := attachmentSegment{a: a, b: b, originalA: originalA, originalB: originalB}
		if elbow, ok := segment.elbow(i == count-1 && i != 1); ok {
			out = append(out, elbow)
		}
		if out[len(out)-1] != b {
			out = append(out, b)
		}
	}
	return out
}

type attachmentSegment struct {
	a, b, originalA, originalB geom.Point
}

func (s attachmentSegment) elbow(target bool) (geom.Point, bool) {
	a, b, originalA, originalB := s.a, s.b, s.originalA, s.originalB
	if originalA.X != originalB.X && originalA.Y != originalB.Y {
		return geom.Point{}, false
	}
	if a.X == b.X || a.Y == b.Y {
		return geom.Point{}, false
	}
	horizontal := originalA.Y == originalB.Y
	if target {
		horizontal = !horizontal
	}
	if horizontal {
		return geom.Point{X: b.X, Y: a.Y}, true
	}
	return geom.Point{X: a.X, Y: b.Y}, true
}
