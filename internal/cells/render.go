package cells

import (
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

type Options struct {
	Charset Charset
	Color   ColorMode
	Theme   string
}
type Result struct {
	Text            []byte
	RefusedClusters int
}
type ProfileError struct{ Profile scene.Profile }

func (e *ProfileError) Error() string {
	return "cells: expected cell profile, got " + e.Profile.String()
}
func Render(s scene.Scene, opts Options) (Result, error) {
	if s.Options.Profile != scene.ProfileCell {
		return Result{}, &ProfileError{s.Options.Profile}
	}
	t, err := theme.Resolve(opts.Theme)
	if err != nil {
		return Result{}, err
	}
	c, err := New(int(s.Canvas.W), int(s.Canvas.H))
	if err != nil {
		return Result{}, err
	}
	labels, err := c.drawGroups(s, opts.Charset, t)
	if err != nil {
		return Result{}, err
	}
	refused, err := c.placeAll(labels, t)
	if err != nil {
		return Result{}, err
	}
	return Result{Text: c.Serialise(opts.Charset, opts.Color, func(token Token) RGB { return RGB(t.Colour(theme.Token(token))) }), RefusedClusters: refused}, nil
}

func (c *Canvas) drawGroups(s scene.Scene, charset Charset, t theme.Theme) ([]*scene.Text, error) {
	var labels []*scene.Text
	for _, g := range s.Groups {
		groupLabels, err := c.drawGroup(g, charset, t)
		if err != nil {
			return nil, err
		}
		labels = append(labels, groupLabels...)
	}
	return labels, nil
}

func (c *Canvas) drawGroup(g *scene.Group, charset Charset, t theme.Theme) ([]*scene.Text, error) {
	var labels []*scene.Text
	for _, p := range g.Items {
		if text, ok := p.(*scene.Text); ok {
			labels = append(labels, text)
			continue
		}
		if err := c.draw(p, charset, t); err != nil {
			return nil, err
		}
	}
	return labels, nil
}
func lineStyle(s scene.Shape, base Style) Style {
	switch {
	case s.Line == scene.LineDouble:
		return StyleDouble
	case s.Line == scene.LineDashed || s.Line == scene.LineDotted:
		return StyleDotted
	case s.Width.Kind == scene.WidthEmphasis:
		return StyleHeavy
	default:
		return base
	}
}
func tokenNamed(name string, series uint8) Token {
	if name == "series" {
		return TokenSeries0 + Token(series%12)
	}
	for v := TokenBG; v <= TokenSuccess; v++ {
		if theme.Token(v).String() == name {
			return v
		}
	}
	return TokenFG
}
func symbolGlyph(charset Charset, name string) rune { g, _ := Symbol(charset, name); return g }
func paint(s scene.Shape, t theme.Theme) (Token, uint8) {
	for _, row := range gen.Styles {
		if row.Name != s.Style {
			continue
		}
		if row.Cell == 2 {
			return tokenNamed(row.Fill, s.Series), row.Cell
		}
		return Token(t.Stroke(theme.Token(tokenNamed(row.Stroke, s.Series)))), row.Cell
	}
	return TokenLine, 1
}
func (c *Canvas) symbol(at geom.Point, g rune, ink Token) {
	c.Put(int(at.X), int(at.Y), func(v *Cell) { v.Symbol = max(v.Symbol, g); v.Ink = max(v.Ink, ink) })
}
func (c *Canvas) marker(p *scene.MarkerRef, charset Charset) {
	for _, m := range gen.Markers {
		if m.Name != p.Marker {
			continue
		}
		glyphs := m.Cell
		if charset == CharsetASCII {
			glyphs = m.Ascii
		}
		if int(p.Axis) < len(glyphs) {
			c.symbol(p.At, rune(glyphs[p.Axis]), TokenLine)
		}
		return
	}
}
func (c *Canvas) draw(p scene.Primitive, charset Charset, t theme.Theme) error {
	switch v := p.(type) {
	case *scene.Rect:
		return c.rectangle(v.Rect, v.Shape, StyleLight, charset, t)
	case *scene.RoundRect:
		return c.rectangle(v.Rect, v.Shape, StyleRounded, charset, t)
	case *scene.Polyline:
		ink, cell := paint(v.Shape, t)
		if cell == 0 {
			return nil
		}
		return c.polyline(v.Points, lineStyle(v.Shape, StyleLight), ink)
	case *scene.MarkerRef:
		c.marker(v, charset)
	case *scene.SymbolRef:
		ink, _ := paint(scene.Shape{Style: v.Style}, t)
		c.symbol(v.At, symbolGlyph(charset, v.Symbol), ink)
	case *scene.Polygon:
		return c.polygon(v, charset, t)
	case *scene.Ellipse:
		return c.ellipse(v, charset, t)
	case *scene.Path:
		return c.path(v, t)
	}
	return nil
}
func (c *Canvas) rectangle(r geom.Rect, s scene.Shape, base Style, charset Charset, t theme.Theme) error {
	if _, err := checkedPoint(int64(r.X)+int64(r.W), int64(r.Y)+int64(r.H)); err != nil {
		return err
	}
	ink, cell := paint(s, t)
	if cell == 0 || r.W <= 0 || r.H <= 0 {
		return nil
	}
	x, y, w, h := int(r.X), int(r.Y), int(r.W), int(r.H)
	if min(w, h) == 1 {
		return c.thinRect(r, s, charset, t)
	}
	style := lineStyle(s, base)
	c.inkSegment(geom.Point{X: r.X, Y: r.Y}, geom.Point{X: int32(x + w - 1), Y: r.Y}, style, ink)
	c.inkSegment(geom.Point{X: r.X, Y: int32(y + h - 1)}, geom.Point{X: int32(x + w - 1), Y: int32(y + h - 1)}, style, ink)
	c.inkSegment(geom.Point{X: r.X, Y: r.Y}, geom.Point{X: r.X, Y: int32(y + h - 1)}, style, ink)
	c.inkSegment(geom.Point{X: int32(x + w - 1), Y: r.Y}, geom.Point{X: int32(x + w - 1), Y: int32(y + h - 1)}, style, ink)
	return nil
}
func (c *Canvas) thinRect(r geom.Rect, s scene.Shape, charset Charset, t theme.Theme) error {
	ink, cell := paint(s, t)
	if cell == 2 {
		for y := int(r.Y); y < int(r.Y+r.H); y++ {
			for x := int(r.X); x < int(r.X+r.W); x++ {
				c.PutDot(x*2, y*4, ink)
				c.Put(x, y, func(v *Cell) { v.Dots = 255; v.Ink = max(v.Ink, ink) })
			}
		}
		return nil
	}
	if r.W == 1 && r.H == 1 {
		c.symbol(geom.Point{X: r.X, Y: r.Y}, symbolGlyph(charset, "box-hollow"), ink)
		return nil
	}
	c.inkSegment(geom.Point{X: r.X, Y: r.Y}, geom.Point{X: r.X + r.W - 1, Y: r.Y + r.H - 1}, lineStyle(s, StyleLight), ink)
	return nil
}
func (c *Canvas) inkSegment(a, b geom.Point, style Style, ink Token) {
	c.Segment(a, b, style)
	if a.Y == b.Y {
		for x := max(0, int(min(a.X, b.X))); x <= min(c.W-1, int(max(a.X, b.X))); x++ {
			c.Put(x, int(a.Y), func(v *Cell) { v.Ink = max(v.Ink, ink) })
		}
		return
	}
	for y := max(0, int(min(a.Y, b.Y))); y <= min(c.H-1, int(max(a.Y, b.Y))); y++ {
		c.Put(int(a.X), y, func(v *Cell) { v.Ink = max(v.Ink, ink) })
	}
}
func (c *Canvas) polyline(ps []geom.Point, style Style, ink Token) error {
	if geom.IsOrthogonal(ps) {
		for i := 1; i < len(ps); i++ {
			c.inkSegment(ps[i-1], ps[i], style, ink)
		}
		return nil
	}
	dots := make([]geom.Point, len(ps))
	for i, p := range ps {
		d, err := CellDot(p)
		if err != nil {
			return err
		}
		dots[i] = d
	}
	return c.dotLines(dots, ink)
}
func (c *Canvas) dotLines(ps []geom.Point, ink Token) error {
	for i := 1; i < len(ps); i++ {
		if err := c.StrokeDots(ps[i-1], ps[i], ink); err != nil {
			return err
		}
	}
	return nil
}
func (c *Canvas) polygon(p *scene.Polygon, charset Charset, t theme.Theme) error {
	ink, cell := paint(p.Shape, t)
	if cell == 0 || len(p.Points) == 0 {
		return nil
	}
	lo, hi := p.Points[0], p.Points[0]
	for _, v := range p.Points {
		lo.X = min(lo.X, v.X)
		lo.Y = min(lo.Y, v.Y)
		hi.X = max(hi.X, v.X)
		hi.Y = max(hi.Y, v.Y)
	}
	if hi.X-lo.X <= 1 && hi.Y-lo.Y <= 1 {
		name := "diamond-hollow"
		if cell == 2 {
			name = "diamond"
		}
		c.symbol(lo, symbolGlyph(charset, name), ink)
		return nil
	}
	ps := make([]geom.Point, 0, len(p.Points)+1)
	for _, v := range p.Points {
		d, err := CellDot(v)
		if err != nil {
			return err
		}
		ps = append(ps, d)
	}
	ps = append(ps, ps[0])
	return c.dotLines(ps, ink)
}
func (c *Canvas) ellipse(p *scene.Ellipse, charset Charset, t theme.Theme) error {
	ink, cell := paint(p.Shape, t)
	if cell == 0 {
		return nil
	}
	if p.RX <= 1 && p.RY <= 1 {
		name := "ring"
		if cell == 2 {
			name = "disc"
		}
		c.symbol(geom.Point{X: p.CX, Y: p.CY}, symbolGlyph(charset, name), ink)
		return nil
	}
	center, err := CellDot(geom.Point{X: p.CX, Y: p.CY})
	if err != nil {
		return err
	}
	rx, err := checkedPoint(2*int64(p.RX), 4*int64(p.RY))
	if err != nil {
		return err
	}
	ps, err := Ellipse(center, rx.X, rx.Y)
	if err != nil {
		return err
	}
	ps = append(ps, ps[0])
	return c.dotLines(ps, ink)
}
func (c *Canvas) path(p *scene.Path, t theme.Theme) error {
	ink, cell := paint(p.Shape, t)
	if cell == 0 {
		return nil
	}
	var current, start geom.Point
	for _, cmd := range p.Commands {
		ps, next, err := pathPoints(cmd, current, start)
		if err != nil {
			return err
		}
		if _, ok := cmd.(*scene.MoveTo); ok {
			start = next
		}
		if err = c.dotLines(ps, ink); err != nil {
			return err
		}
		current = next
	}
	return nil
}
func pathPoints(cmd scene.Command, current, start geom.Point) ([]geom.Point, geom.Point, error) {
	switch v := cmd.(type) {
	case *scene.MoveTo:
		d, e := CellDot(v.P)
		return nil, d, e
	case *scene.LineTo:
		d, e := CellDot(v.P)
		return []geom.Point{current, d}, d, e
	case *scene.ClosePath:
		return []geom.Point{current, start}, start, nil
	case *scene.CubicTo:
		return cubicPoints(v, current)
	case *scene.ArcTo:
		return arcPoints(v, current)
	}
	return nil, current, nil
}

func cubicPoints(v *scene.CubicTo, current geom.Point) ([]geom.Point, geom.Point, error) {
	a, e := CellDot(v.C1)
	if e != nil {
		return nil, current, e
	}
	b, e := CellDot(v.C2)
	if e != nil {
		return nil, current, e
	}
	d, e := CellDot(v.P)
	if e != nil {
		return nil, current, e
	}
	ps, e := Cubic([4]geom.Point{current, a, b, d})
	return ps, d, e
}
func arcPoints(v *scene.ArcTo, current geom.Point) ([]geom.Point, geom.Point, error) {
	center, e := CellDot(geom.Point{X: v.CX, Y: v.CY})
	if e != nil {
		return nil, current, e
	}
	radius, e := checkedPoint(2*int64(v.R), 0)
	if e != nil {
		return nil, current, e
	}
	ps, e := Arc(center, radius.X, v.A0, v.Sweep)
	if e != nil {
		return nil, current, e
	}
	return ps, ps[len(ps)-1], nil
}
