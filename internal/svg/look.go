package svg

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const sketchMultiplier = 2654435761

type vec struct{ x, y int64 }

type segment [2]vec

type sketchedClasses [22][12]uint8

func (c *sketchedClasses) mark(style, key string, series uint8, flag uint8) {
	if key == style {
		series = 0
	}
	for i := range c {
		if styleName(i) == style {
			c[i][series%12] |= flag
			return
		}
	}
}

func (r *renderer) sketchRules(key string, row gen.Style, n, flags uint8) error {
	if flags&1 != 0 {
		fill, err := r.fillColour(row.Fill, n)
		if err != nil {
			return err
		}
		r.WriteString(".emd-f-" + key + "{fill:" + fill)
		if row.Tint == 1 {
			r.WriteString(";fill-opacity:0.4")
		}
		r.WriteString("}\n")
	}
	if flags&2 != 0 {
		stroke, err := r.strokeColour(row.Stroke, n)
		if err != nil {
			return err
		}
		r.WriteString(".emd-h-" + key + "{fill:none;stroke:" + stroke + ";stroke-linecap:round;stroke-linejoin:round")
		if row.Tint == 2 {
			r.WriteString(";stroke-opacity:0.4")
		}
		r.WriteString("}\n")
	}
	return nil
}

type sketcher struct{ state uint32 }

func newSketcher(seed uint32, index int) sketcher {
	state := seed ^ uint32(index+1)*sketchMultiplier
	if state == 0 {
		state = 1
	}
	return sketcher{state}
}

func (s *sketcher) next() uint32 {
	x := s.state
	x ^= x << 13
	x ^= x >> 17
	x ^= x << 5
	s.state = x
	return x
}

func (s *sketcher) offset() int64 { return int64(s.next()%129) - 64 }

func (s *sketcher) pass(from, to vec) string {
	bow := s.offset()
	a := vec{from.x + s.offset(), from.y + s.offset()}
	b := vec{to.x + s.offset(), to.y + s.offset()}
	dx, dy := b.x-a.x, b.y-a.y
	mx, my := geom.FloorDiv(a.x+b.x, 2), geom.FloorDiv(a.y+b.y, 2)
	if length := max(abs(dx), abs(dy)); length > 0 {
		mx += roundHalfUp(bow*-dy, length)
		my += roundHalfUp(bow*dx, length)
	}
	return "M " + vecPair(a) + " Q " + vecPair(vec{mx, my}) + " " + vecPair(b)
}

func roundHalfUp(a, b int64) int64 { return geom.FloorDiv(2*a+b, 2*b) }

func vecPair(v vec) string { return number(v.x) + " " + number(v.y) }

func (r *renderer) sketch(o outline, index int) (string, error) {
	s := newSketcher(r.look.Seed, index)
	return r.sketchShape(o, &s)
}

func (r *renderer) sketchShape(o outline, s *sketcher) (string, error) {
	row, err := styleRow(o.shape.Style)
	if err != nil {
		return "", err
	}
	key := class(o.shape.Style, o.shape.Series)
	if row.Stroke == "none" {
		return r.element(o.tag, o.shape, o.geometry)
	}
	var out strings.Builder
	if row.Fill != "none" {
		r.sketched.mark(o.shape.Style, key, o.shape.Series, 1)
		out.WriteString("<" + o.tag + " class='emd-f-" + key + "' " + o.geometry + "/>\n")
	}
	r.sketched.mark(o.shape.Style, key, o.shape.Series, 2)
	for _, seg := range o.segments {
		for range 2 {
			out.WriteString("<path class='emd-h-" + key + "' d='" + s.pass(seg[0], seg[1]) + "'" + r.strokeAttributes(o.shape, row) + "/>\n")
		}
	}
	return out.String(), nil
}

func rectSegments(p geom.Rect) []segment {
	x0, y0 := int64(p.X), int64(p.Y)
	x1, y1 := x0+int64(p.W), y0+int64(p.H)
	return closedSegments([]vec{{x0, y0}, {x1, y0}, {x1, y1}, {x0, y1}})
}

func toVecs(ps []geom.Point) []vec {
	vs := make([]vec, len(ps))
	for i, p := range ps {
		vs[i] = vec{int64(p.X), int64(p.Y)}
	}
	return vs
}

func closedPointSegments(ps []geom.Point) []segment { return closedSegments(toVecs(ps)) }

func openPointSegments(ps []geom.Point) []segment { return openSegments(toVecs(ps)) }

func openSegments(vs []vec) []segment {
	var out []segment
	for i := 1; i < len(vs); i++ {
		out = append(out, segment{vs[i-1], vs[i]})
	}
	return out
}

func closedSegments(vs []vec) []segment {
	out := openSegments(vs)
	if len(vs) > 2 && vs[len(vs)-1] != vs[0] {
		out = append(out, segment{vs[len(vs)-1], vs[0]})
	}
	return out
}

func pathSegments(cs []scene.Command) []segment {
	var out []segment
	var cur, start vec
	for _, c := range cs {
		switch v := c.(type) {
		case *scene.MoveTo:
			cur = vec{int64(v.P.X), int64(v.P.Y)}
			start = cur
		case *scene.LineTo:
			next := vec{int64(v.P.X), int64(v.P.Y)}
			out = append(out, segment{cur, next})
			cur = next
		case *scene.ClosePath:
			if cur != start {
				out = append(out, segment{cur, start})
				cur = start
			}
		default:
			return nil
		}
	}
	return out
}
