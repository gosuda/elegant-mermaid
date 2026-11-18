package cells

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

const (
	columnUnits   = 512
	rowUnits      = 1024
	titleLineUnit = 1536
	bodyLineUnit  = 1280
)

type rasterInk struct {
	fill, stroke    Token
	filled, stroked bool
}

func RenderBraille(s scene.Scene, opts Options) (Result, error) {
	if s.Options.Profile != scene.ProfileVector {
		return Result{}, &ProfileError{Want: scene.ProfileVector, Got: s.Options.Profile}
	}
	t, err := theme.Resolve(opts.Theme)
	if err != nil {
		return Result{}, err
	}
	c, err := NewBraille(s.Canvas.W, s.Canvas.H)
	if err != nil {
		return Result{}, err
	}
	labels, err := c.rasteriseGroups(s.Groups, t)
	if err != nil {
		return Result{}, err
	}
	refused, err := c.placeBraille(labels, t)
	if err != nil {
		return Result{}, err
	}
	return Result{Text: c.Serialise(opts.Charset, opts.Color, func(token Token) RGB { return RGB(t.Colour(theme.Token(token))) }), RefusedClusters: refused}, nil
}

func (c *Canvas) rasteriseGroups(groups []*scene.Group, t theme.Theme) ([]*scene.Text, error) {
	var labels []*scene.Text
	for _, g := range groups {
		for _, p := range g.Items {
			if text, ok := p.(*scene.Text); ok {
				labels = append(labels, text)
			} else if err := c.rasterise(p, t); err != nil {
				return nil, err
			}
		}
	}
	return labels, nil
}

func rasterPaint(s scene.Shape, t theme.Theme) rasterInk {
	for _, row := range gen.Styles {
		if row.Name != s.Style {
			continue
		}
		return rasterInk{
			fill:    tokenNamed(row.Fill, s.Series),
			filled:  row.Cell == 2 && row.Fill != "none",
			stroke:  Token(t.Stroke(theme.Token(tokenNamed(row.Stroke, s.Series)))),
			stroked: row.Cell != 0 && row.Stroke != "none",
		}
	}
	return rasterInk{stroke: TokenLine, stroked: true}
}

func (c *Canvas) rasterise(p scene.Primitive, t theme.Theme) error {
	switch v := p.(type) {
	case *scene.Rect:
		return c.rasterRect(v.Rect, v.Shape, t)
	case *scene.RoundRect:
		return c.rasterRect(v.Rect, v.Shape, t)
	case *scene.Ellipse:
		return c.rasterEllipse(v, t)
	case *scene.Polygon:
		return c.rasterPolygons([][]geom.Point{v.Points}, rasterPaint(v.Shape, t))
	case *scene.Polyline:
		return c.rasterOpen(v.Points, rasterPaint(v.Shape, t))
	case *scene.Path:
		return c.rasterPath(v, t)
	case *scene.MarkerRef:
		return c.rasterMarker(v, t)
	case *scene.SymbolRef:
		return geom.ErrDomain
	}
	return nil
}

func closedRing(points []geom.Point) []geom.Point {
	return append(slices.Clone(points), points[:min(1, len(points))]...)
}

func (c *Canvas) rasterPolygons(rings [][]geom.Point, ink rasterInk) error {
	if ink.filled {
		if err := c.FillRings(rings, ink.fill); err != nil {
			return err
		}
	}
	for _, ring := range rings {
		if err := c.rasterOpen(closedRing(ring), ink); err != nil {
			return err
		}
	}
	return nil
}

func (c *Canvas) rasterOpen(points []geom.Point, ink rasterInk) error {
	if !ink.stroked {
		return nil
	}
	return c.Stroke(points, ink.stroke)
}

func (c *Canvas) rasterRect(r geom.Rect, s scene.Shape, t theme.Theme) error {
	far, err := checkedPoint(int64(r.X)+int64(r.W), int64(r.Y)+int64(r.H))
	if err != nil || r.W < 0 || r.H < 0 {
		return err
	}
	ring := []geom.Point{{X: r.X, Y: r.Y}, {X: far.X, Y: r.Y}, far, {X: r.X, Y: far.Y}}
	return c.rasterPolygons([][]geom.Point{ring}, rasterPaint(s, t))
}

func (c *Canvas) rasterEllipse(e *scene.Ellipse, t theme.Theme) error {
	if e.RX < 0 || e.RY < 0 {
		return nil
	}
	ring, err := Ellipse(geom.Point{X: e.CX, Y: e.CY}, e.RX, e.RY)
	if err != nil {
		return err
	}
	return c.rasterPolygons([][]geom.Point{ring}, rasterPaint(e.Shape, t))
}

type subpath struct {
	points []geom.Point
	closed bool
}

type pathWalk struct {
	subpaths       []subpath
	current, start geom.Point
	open           bool
}

func (w *pathWalk) begin(at geom.Point) {
	w.subpaths = append(w.subpaths, subpath{points: []geom.Point{at}})
	w.open = true
}

func (w *pathWalk) extend(points ...geom.Point) {
	if !w.open {
		w.begin(w.current)
	}
	last := &w.subpaths[len(w.subpaths)-1]
	last.points = append(last.points, points...)
	w.current = points[len(points)-1]
}

func (w *pathWalk) close() {
	if w.open {
		w.subpaths[len(w.subpaths)-1].closed = true
	}
	w.open = false
	w.current = w.start
}

func (w *pathWalk) step(cmd scene.Command) error {
	switch v := cmd.(type) {
	case *scene.MoveTo:
		w.begin(v.P)
		w.current, w.start = v.P, v.P
	case *scene.LineTo:
		w.extend(v.P)
	case *scene.CubicTo:
		points, err := Cubic([4]geom.Point{w.current, v.C1, v.C2, v.P})
		if err != nil {
			return err
		}
		w.extend(points[1:]...)
	case *scene.ArcTo:
		points, err := Arc(geom.Point{X: v.CX, Y: v.CY}, v.R, v.A0, v.Sweep)
		if err != nil {
			return err
		}
		w.extend(points...)
	case *scene.ClosePath:
		w.close()
	}
	return nil
}

func pathSubpaths(commands []scene.Command) ([]subpath, error) {
	var w pathWalk
	for _, cmd := range commands {
		if err := w.step(cmd); err != nil {
			return nil, err
		}
	}
	return w.subpaths, nil
}

func (c *Canvas) rasterPath(p *scene.Path, t theme.Theme) error {
	subpaths, err := pathSubpaths(p.Commands)
	if err != nil {
		return err
	}
	ink := rasterPaint(p.Shape, t)
	if ink.filled {
		rings := make([][]geom.Point, len(subpaths))
		for i, sp := range subpaths {
			rings[i] = sp.points
		}
		if err = c.FillRings(rings, ink.fill); err != nil {
			return err
		}
	}
	for _, sp := range subpaths {
		points := sp.points
		if sp.closed {
			points = closedRing(points)
		}
		if err = c.rasterOpen(points, ink); err != nil {
			return err
		}
	}
	return nil
}

func markerVertex(p, ref [2]int32, m *scene.MarkerRef) (geom.Point, error) {
	x, y := int64(p[0])-int64(ref[0]), int64(p[1])-int64(ref[1])
	switch m.Axis {
	case scene.AxisMinusX:
		x, y = -x, -y
	case scene.AxisPlusY:
		x, y = -y, x
	case scene.AxisMinusY:
		x, y = y, -x
	}
	return checkedPoint(x+int64(m.At.X), y+int64(m.At.Y))
}

func markerOf(name string) (gen.Marker, bool) {
	for _, row := range gen.Markers {
		if row.Name == name {
			return row, len(row.Points) >= 2
		}
	}
	return gen.Marker{}, false
}

func (c *Canvas) rasterMarker(m *scene.MarkerRef, t theme.Theme) error {
	row, ok := markerOf(m.Marker)
	if !ok {
		return geom.ErrDomain
	}
	points := make([]geom.Point, len(row.Points))
	for i, p := range row.Points {
		v, err := markerVertex(p, row.Ref, m)
		if err != nil {
			return err
		}
		points[i] = v
	}
	style := map[string]string{"filled": "mark", "hollow": "mark-hollow", "open": "edge"}[row.Paint]
	ink := rasterPaint(scene.Shape{Style: style}, t)
	parts := markerParts(points, row.Breaks)
	if row.Paint == "open" {
		return c.rasterOpenParts(parts, ink)
	}
	return c.rasterPolygons(parts, ink)
}

func markerParts(points []geom.Point, breaks []uint32) [][]geom.Point {
	var parts [][]geom.Point
	start := 0
	for _, end := range append(slices.Clone(breaks), uint32(len(points))) {
		parts = append(parts, points[start:end])
		start = int(end)
	}
	return parts
}

func (c *Canvas) rasterOpenParts(parts [][]geom.Point, ink rasterInk) error {
	for _, part := range parts {
		if err := c.rasterOpen(part, ink); err != nil {
			return err
		}
	}
	return nil
}

func lineUnits(role scene.TextRole) int64 {
	if role == scene.TextRoleTitle {
		return titleLineUnit
	}
	return bodyLineUnit
}

func (c *Canvas) placeBraille(labels []*scene.Text, t theme.Theme) (int, error) {
	refused := 0
	for _, p := range labels {
		n, err := c.placeBrailleText(p, textInk(p, t))
		if err != nil {
			return 0, err
		}
		refused += n
	}
	return refused, nil
}

func (c *Canvas) placeBrailleText(p *scene.Text, ink Token) (int, error) {
	first := geom.FloorDiv(int64(p.Rect.X), columnUnits)
	span := measure.CeilDiv(int64(p.Rect.X)+int64(p.Rect.W), columnUnits) - first
	refused := 0
	for k, runs := range p.Lines {
		var b strings.Builder
		for _, run := range runs {
			b.WriteString(run.Text)
		}
		text := terminalText(b.String())
		width, err := measure.CellWidth(text)
		if err != nil {
			return 0, err
		}
		row := geom.FloorDiv(int64(p.Rect.Y)+int64(k)*lineUnits(p.Role), rowUnits)
		refused += c.placeClusters(text, lineStart(p.Align, int(first), int(span), int(width)), int(row), ink)
	}
	return refused, nil
}
