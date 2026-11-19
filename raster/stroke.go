package raster

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func segmentOutline(a, b point, w float64) []point {
	dx, dy := b.x-a.x, b.y-a.y
	length := math.Hypot(dx, dy)
	if length == 0 {
		return nil
	}
	nx, ny := -dy*w/(2*length), dx*w/(2*length)
	return []point{{a.x - nx, a.y - ny}, {b.x - nx, b.y - ny}, {b.x + nx, b.y + ny}, {a.x + nx, a.y + ny}}
}

func capOutline(p point, w float64) []point {
	out := make([]point, 16)
	for i := range out {
		a := int32(i * 4096)
		out[i] = point{p.x + w*float64(geom.CosQ15(a))/65536, p.y + w*float64(geom.SinQ15(a))/65536}
	}
	return out
}

func strokeContours(paths []contour, w float64, line scene.LineStyle) []contour {
	if w <= 0 {
		return nil
	}
	var out []contour
	for _, path := range paths {
		for _, run := range dashRuns(path, line) {
			out = appendStroke(out, run, w)
		}
	}
	return out
}

func appendStroke(out []contour, run []point, w float64) []contour {
	for i, p := range run {
		out = append(out, contour{capOutline(p, w), true})
		if i > 0 {
			out = append(out, contour{segmentOutline(run[i-1], p, w), true})
		}
	}
	return out
}

func dashPattern(line scene.LineStyle) (float64, float64) {
	switch line {
	case scene.LineDotted:
		return float64(constant("paint.dash_dotted_on")), float64(constant("paint.dash_dotted_off"))
	case scene.LineDashed:
		return float64(constant("paint.dash_dashed_on")), float64(constant("paint.dash_dashed_off"))
	default:
		return 0, 0
	}
}

type dashState struct {
	on, off, remaining float64
	index              int
	runs               [][]point
	current            []point
}

func dashRuns(path contour, line scene.LineStyle) [][]point {
	ps := path.points
	if len(ps) == 0 {
		return nil
	}
	if path.closed {
		ps = append(slices.Clone(ps), ps[0])
	}
	on, off := dashPattern(line)
	if on <= 0 || off <= 0 {
		return [][]point{ps}
	}
	d := dashState{on: on, off: off, remaining: on}
	for i := 1; i < len(ps); i++ {
		d.segment(ps[i-1], ps[i])
	}
	if len(d.current) > 0 {
		d.runs = append(d.runs, d.current)
	}
	return d.runs
}

func (d *dashState) segment(a, b point) {
	length := math.Hypot(b.x-a.x, b.y-a.y)
	if length == 0 {
		return
	}
	for offset := 0.0; offset < length; {
		take := min(d.remaining, length-offset)
		start := interpolate(a, b, offset/length)
		end := interpolate(a, b, (offset+take)/length)
		d.add(start, end)
		offset += take
		d.remaining -= take
		if d.remaining <= 0 {
			d.advance()
		}
	}
}

func (d *dashState) add(a, b point) {
	if d.index%2 != 0 {
		return
	}
	if len(d.current) == 0 {
		d.current = append(d.current, a)
	}
	d.current = append(d.current, b)
}

func (d *dashState) advance() {
	if len(d.current) > 0 {
		d.runs = append(d.runs, d.current)
		d.current = nil
	}
	d.index++
	d.remaining = d.on
	if d.index%2 != 0 {
		d.remaining = d.off
	}
}

func interpolate(a, b point, t float64) point {
	return point{a.x + (b.x-a.x)*t, a.y + (b.y-a.y)*t}
}
