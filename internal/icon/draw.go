package icon

import (
	"math"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	boxUnits         = 1536
	builtinViewBox   = 80
	missingCode      = "icon/pack-missing"
	cellSymbolBuilt  = "ink-line"
	cellSymbolPacked = "ink"
)

type Drawing struct {
	Items   []scene.Primitive
	Missing bool
}

type target struct {
	name   string
	shapes []shape
	icon   *Icon
}

func resolve(packs []*Pack, name string) (target, bool) {
	if prefix, local, qualified := strings.Cut(name, ":"); qualified {
		for _, p := range packs {
			if icon, ok := p.lookup(local); ok && p.Prefix == prefix {
				return target{name: name, icon: icon}, icon.supported
			}
		}
		return target{}, false
	}
	if shapes, ok := builtins[name]; ok {
		return target{name: name, shapes: shapes}, true
	}
	return target{name: name}, name == unknownName
}

func Draw(packs []*Pack, name string, at geom.Point, profile scene.Profile) Drawing {
	t, ok := resolve(packs, name)
	if !ok {
		t = target{name: unknownName}
	}
	items, drawn := t.draw(at, profile)
	if !drawn {
		t, ok = target{name: unknownName}, false
		items, _ = t.draw(at, profile)
	}
	return Drawing{Items: items, Missing: !ok}
}

func (t target) draw(at geom.Point, profile scene.Profile) ([]scene.Primitive, bool) {
	if profile == scene.ProfileCell {
		return t.cellSymbol(at), true
	}
	switch {
	case t.icon != nil:
		return t.icon.draw(at)
	case t.name == unknownName:
		return []scene.Primitive{drawUnknownGlyph(at)}, true
	}
	return drawShapes(t.shapes, at), true
}

func (t target) cellSymbol(at geom.Point) []scene.Primitive {
	symbol, style := t.name, cellSymbolBuilt
	if t.icon != nil {
		symbol, style = unknownName, cellSymbolPacked
	}
	if t.name == unknownName {
		style = cellSymbolPacked
	}
	return []scene.Primitive{&scene.SymbolRef{Symbol: symbol, At: at, Style: style}}
}

func MissingDiagnostic(name string, span source.Span) diag.Diagnostic {
	row := registryRow()
	return diag.Diagnostic{Code: missingCode, Severity: diag.SeverityInfo, Message: strings.ReplaceAll(row.Summary, "NAME", name), Span: span, Help: row.Help}
}

func registryRow() gen.Diagnostic {
	for _, row := range gen.Diagnostics {
		if row.Code == missingCode {
			return row
		}
	}
	return gen.Diagnostic{Code: missingCode, Summary: "icon NAME is not available"}
}

type frame struct {
	num, den int64
	left     int64
	top      int64
	origin   point
	bad      bool
}

func (f *frame) unit(v int64) int64 {
	d := f.den * fixedScale
	return geom.FloorDiv(2*v*f.num+d, 2*d)
}

func (f *frame) clamp(v int64) int32 {
	if v < math.MinInt32 || v > math.MaxInt32 {
		f.bad = true
		return 0
	}
	return int32(v)
}

func (f *frame) at(p point) geom.Point {
	return geom.Point{X: f.clamp(f.origin.x + f.unit(p.x-f.left)), Y: f.clamp(f.origin.y + f.unit(p.y-f.top))}
}

func (f *frame) length(v int64) int32 { return f.clamp(f.unit(v)) }

func (i *Icon) draw(at geom.Point) ([]scene.Primitive, bool) {
	maxSide := max(i.width, i.height)
	scale := max(1, geom.FloorDiv(2*boxUnits*fixedScale+maxSide, 2*maxSide))
	f := &frame{num: scale, den: 1, left: i.left, top: i.top}
	f.origin = point{
		int64(at.X) + geom.FloorDiv(boxUnits-f.unit(i.width), 2),
		int64(at.Y) + geom.FloorDiv(boxUnits-f.unit(i.height), 2),
	}
	items := make([]scene.Primitive, 0, len(i.paths))
	for _, path := range i.paths {
		items = append(items, &scene.Path{Shape: scene.Shape{Style: "ink"}, Commands: f.commands(path)})
	}
	return items, !f.bad
}

func (f *frame) commands(cs []command) []scene.Command {
	var out []scene.Command
	var cur, start geom.Point
	for _, c := range cs {
		switch c.op {
		case 'M', 'L':
			cur = f.at(c.p[0])
			if c.op == 'M' {
				start = cur
				out = append(out, &scene.MoveTo{P: cur})
			} else {
				out = append(out, &scene.LineTo{P: cur})
			}
		case 'C':
			cubic := &scene.CubicTo{C1: f.at(c.p[0]), C2: f.at(c.p[1]), P: f.at(c.p[2])}
			cur = cubic.P
			out = append(out, cubic)
		case 'Q':
			cubic := quadToCubic(point{int64(cur.X), int64(cur.Y)}, toPoint(f.at(c.p[0])), toPoint(f.at(c.p[1])))
			cur = cubic.P
			out = append(out, cubic)
		case 'Z':
			cur = start
			out = append(out, &scene.ClosePath{})
		}
	}
	return out
}

func toPoint(p geom.Point) point { return point{int64(p.X), int64(p.Y)} }

func drawShapes(shapes []shape, at geom.Point) []scene.Primitive {
	f := &frame{num: boxUnits, den: builtinViewBox, origin: point{int64(at.X), int64(at.Y)}}
	var out []scene.Primitive
	for _, s := range shapes {
		p, ok := f.shape(s)
		if !ok {
			return nil
		}
		out = append(out, p)
	}
	if f.bad {
		return nil
	}
	return out
}

func (f *frame) number(s string) int64 {
	v, ok := parseDecimal(s)
	if !ok {
		f.bad = true
	}
	return v
}

func (f *frame) shape(s shape) (scene.Primitive, bool) {
	stroked := scene.Shape{Style: "ink-line", Width: scene.Width{Kind: scene.WidthEmphasis}}
	filled := scene.Shape{Style: "ink"}
	switch s.kind {
	case shapeRect:
		return f.rect(s.args, stroked), !f.bad
	case shapeEllipse:
		return f.ellipse(s.args, stroked), !f.bad
	case shapeFilledEllipse:
		return f.ellipse(s.args, filled), !f.bad
	case shapeLine:
		return f.line(s.args, stroked), !f.bad
	}
	return f.path(s.args[0], s.kind, stroked, filled)
}

func (f *frame) rect(args []string, shape scene.Shape) scene.Primitive {
	x, y, w, h := f.number(args[0]), f.number(args[1]), f.number(args[2]), f.number(args[3])
	a, b := f.at(point{x, y}), f.at(point{x + w, y + h})
	r := geom.Rect{X: a.X, Y: a.Y, W: b.X - a.X, H: b.Y - a.Y}
	return &scene.RoundRect{Shape: shape, Rect: r, R: f.length(f.number(args[4]))}
}

func (f *frame) ellipse(args []string, shape scene.Shape) scene.Primitive {
	c := f.at(point{f.number(args[0]), f.number(args[1])})
	return &scene.Ellipse{Shape: shape, CX: c.X, CY: c.Y, RX: f.length(f.number(args[2])), RY: f.length(f.number(args[3]))}
}

func (f *frame) line(args []string, shape scene.Shape) scene.Primitive {
	a := f.at(point{f.number(args[0]), f.number(args[1])})
	b := f.at(point{f.number(args[2]), f.number(args[3])})
	return &scene.Polyline{Shape: shape, Points: []geom.Point{a, b}}
}

func (f *frame) path(d string, kind shapeKind, stroked, filled scene.Shape) (scene.Primitive, bool) {
	cmds, ok := parsePath(d)
	if !ok {
		return nil, false
	}
	shape := stroked
	if kind == shapeFill {
		shape = filled
	}
	return &scene.Path{Shape: shape, Commands: f.commands(cmds)}, !f.bad
}
