package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type pieGeom struct {
	width, height, cx, cy, radius, inner, labelRadius int64
}

func (p *piePlan) geometry() pieGeom {
	g := pieGeom{width: p.c.height, height: p.c.height}
	g.cx, g.cy = geom.FloorDiv(g.width, 2), geom.FloorDiv(g.height, 2)
	g.radius = min(g.cx, g.cy) - p.c.margin
	g.inner = geom.FloorDiv(g.radius*p.donut, scale)
	g.labelRadius = geom.FloorDiv(g.radius*p.textPosition, scale)
	return g
}

func arcVertex(cx, cy, r, angle int64) (x, y int64) {
	a := int32(geom.FloorMod(angle, pieFullTurn))
	x = cx + geom.FloorDiv(2*r*int64(geom.CosQ15(a))+pieHalfTurn, pieFullTurn)
	y = cy + geom.FloorDiv(2*r*int64(geom.SinQ15(a))+pieHalfTurn, pieFullTurn)
	return x, y
}

type bounds struct {
	x0, y0, x1, y1 int64
	set            bool
}

func (b *bounds) add(x, y int64) {
	if !b.set {
		b.x0, b.y0, b.x1, b.y1, b.set = x, y, x, y, true
		return
	}
	b.x0, b.y0, b.x1, b.y1 = min(b.x0, x), min(b.y0, y), max(b.x1, x), max(b.y1, y)
}

func (b *bounds) addRect(r rect) {
	b.add(r.x, r.y)
	b.add(r.x+r.w, r.y+r.h)
}

func (b *bounds) addArc(cx, cy, r, a0, sweep int64) {
	b.add(arcVertex(cx, cy, r, a0))
	b.add(arcVertex(cx, cy, r, a0+sweep))
	lo, hi := min(a0, a0+sweep), max(a0, a0+sweep)
	for q := geom.FloorDiv(lo+pieQuarterTurn-1, pieQuarterTurn) * pieQuarterTurn; q <= hi; q += pieQuarterTurn {
		b.add(arcVertex(cx, cy, r, q))
	}
}

func (b *bounds) rect() rect { return rect{b.x0, b.y0, b.x1 - b.x0, b.y1 - b.y0} }

type pathBuilder struct {
	commands []scene.Command
	err      error
}

func (b *pathBuilder) point(x, y int64) geom.Point {
	p, err := pointOf(x, y)
	b.err = firstError(b.err, err)
	return p
}

func firstError(a, b error) error {
	if a != nil {
		return a
	}
	return b
}

func (b *pathBuilder) move(x, y int64) {
	b.commands = append(b.commands, &scene.MoveTo{P: b.point(x, y)})
}

func (b *pathBuilder) line(x, y int64) {
	b.commands = append(b.commands, &scene.LineTo{P: b.point(x, y)})
}

func (b *pathBuilder) close() { b.commands = append(b.commands, &scene.ClosePath{}) }

func (b *pathBuilder) arc(cx, cy, r, a0, sweep int64) {
	var out [5]int32
	for i, v := range []int64{cx, cy, r, geom.FloorMod(a0, pieFullTurn), sweep} {
		var err error
		out[i], err = i32(v)
		b.err = firstError(b.err, err)
	}
	b.commands = append(b.commands, &scene.ArcTo{CX: out[0], CY: out[1], R: out[2], A0: out[3], Sweep: out[4]})
}

func (b *pathBuilder) circle(cx, cy, r, a0, half int64) {
	x, y := arcVertex(cx, cy, r, a0)
	b.move(x, y)
	b.arc(cx, cy, r, a0, half)
	b.arc(cx, cy, r, a0+half, half)
	b.close()
}

func (b *pathBuilder) slice(cx, cy, r, inner, a0, sweep int64) {
	if sweep == pieFullTurn {
		b.circle(cx, cy, r, a0, pieHalfTurn)
		if inner > 0 {
			b.circle(cx, cy, inner, a0, -pieHalfTurn)
		}
		return
	}
	x, y := arcVertex(cx, cy, r, a0)
	if inner == 0 {
		b.move(cx, cy)
		b.line(x, y)
	} else {
		b.move(x, y)
	}
	b.arc(cx, cy, r, a0, sweep)
	if inner > 0 {
		x, y = arcVertex(cx, cy, inner, a0+sweep)
		b.line(x, y)
		b.arc(cx, cy, inner, a0+sweep, -sweep)
	}
	b.close()
}

type pieScene struct {
	p        *piePlan
	g        pieGeom
	specs    []pieLabel
	texts    []textBox
	rects    []rect
	swatches []rect
	boxes    []rect
	canvas   geom.Size
}

func pieStyle(kind pieLabelKind) (measure.Role, int32) {
	if kind == pieLabelTitle {
		return measure.RoleTitle, measure.RoleTitle.SizePx()
	}
	return measure.RoleLabel, measure.RoleLabel.SizePx()
}

func measurePie(text string, role measure.Role, size int32, fontFamily string) (textBox, error) {
	metric := measure.Metric{Profile: measure.ProfileVector, SizePx: size, Weight: role.Weight(), FontFamily: fontFamily != ""}
	lines, err := measure.StyledLines(text, geom.I32Max, metric)
	if err != nil {
		return textBox{}, err
	}
	var widest int64
	for _, line := range lines {
		widest = max(widest, int64(line.Width))
	}
	height := measure.RoundHalfUp(int64(size)*64*int64(role.LineHeightPx()), int64(role.SizePx()))
	return textBox{lines: lines, w: widest, h: int64(len(lines)) * height}, nil
}

func (p *piePlan) arrange() (*pieScene, error) {
	s := &pieScene{p: p, g: p.geometry(), specs: p.labelSpecs()}
	s.texts = make([]textBox, len(s.specs))
	for i, spec := range s.specs {
		role, size := pieStyle(spec.kind)
		t, err := measurePie(spec.text, role, size, p.fontFamily)
		if err != nil {
			return nil, err
		}
		s.texts[i] = t
	}
	if err := s.place(); err != nil {
		return nil, err
	}
	return s, nil
}

func (s *pieScene) place() error {
	g, c := s.g, s.p.c
	extent := bounds{}
	extent.addRect(rect{0, 0, g.width, g.height})
	rows := int64(len(s.p.pie.Sections))
	top := g.cy - geom.FloorDiv(c.legendRow*rows, 2)
	left := g.cx + c.legendOffset
	var longest int64
	s.rects = make([]rect, len(s.specs))
	for i, spec := range s.specs {
		t := s.texts[i]
		switch spec.kind {
		case pieLabelTitle:
			s.rects[i] = rect{g.cx - geom.FloorDiv(t.w, 2), c.titlePad, t.w, t.h}
		case pieLabelPercent:
			s.rects[i] = s.percentRect(s.p.slices[spec.index], t)
		default:
			row := top + int64(spec.index)*c.legendRow
			s.rects[i] = rect{left + c.legendRow, row + geom.FloorDiv(c.legendSize-t.h, 2), t.w, t.h}
			s.swatches = append(s.swatches, rect{left, row, c.legendSize, c.legendSize})
			longest = max(longest, t.w)
		}
		extent.addRect(s.rects[i])
	}
	for _, sw := range s.swatches {
		extent.addRect(sw)
	}
	if rows > 0 {
		extent.add(g.width+c.margin+c.legendRow+longest, extent.y1)
	}
	s.shift(-extent.x0, -extent.y0)
	s.boxes = []rect{{s.g.cx - g.cx, s.g.cy - g.cy, g.width, g.height}}
	for _, sl := range s.p.slices {
		var b bounds
		s.sliceBounds(&b, sl)
		s.boxes = append(s.boxes, b.rect())
	}
	w, err := i32(extent.x1 - extent.x0)
	if err != nil {
		return err
	}
	h, err := i32(extent.y1 - extent.y0)
	s.canvas = geom.Size{W: w, H: h}
	return err
}

func (s *pieScene) percentRect(sl pieSlice, t textBox) rect {
	mid := sl.start + geom.FloorDiv(sl.sweep, 2)
	a := int32(geom.FloorMod(mid, pieFullTurn))
	x := s.g.cx + geom.FloorDiv(s.g.labelRadius*int64(geom.SinQ15(a)), pieHalfTurn)
	y := s.g.cy - geom.FloorDiv(s.g.labelRadius*int64(geom.CosQ15(a)), pieHalfTurn)
	return rect{x - geom.FloorDiv(t.w, 2), y - geom.FloorDiv(t.h, 2), t.w, t.h}
}

func (s *pieScene) shift(dx, dy int64) {
	for i := range s.rects {
		s.rects[i].x += dx
		s.rects[i].y += dy
	}
	for i := range s.swatches {
		s.swatches[i].x += dx
		s.swatches[i].y += dy
	}
	s.g.cx += dx
	s.g.cy += dy
}

func (s *pieScene) sliceBounds(b *bounds, sl pieSlice) {
	g := s.g
	a0 := geom.FloorMod(sl.start-pieQuarterTurn, pieFullTurn)
	b.addArc(g.cx, g.cy, g.radius, a0, sl.sweep)
	if g.inner == 0 {
		b.add(g.cx, g.cy)
		return
	}
	b.addArc(g.cx, g.cy, g.inner, a0, sl.sweep)
}

func (s *pieScene) dumpBoxes() ([]scene.Box, error) {
	out := make([]scene.Box, len(s.boxes))
	for i, b := range s.p.boxSpecs() {
		parent := plotID
		if b.slice < 0 {
			parent = ""
		}
		g, err := s.boxes[i].geom()
		if err != nil {
			return nil, err
		}
		out[i] = scene.Box{ID: b.id, Role: scene.RoleNode, Parent: parent, Rect: g}
	}
	return out, nil
}

func (s *pieScene) dumpLabels() ([]scene.Label, error) {
	out := make([]scene.Label, len(s.specs))
	for i, spec := range s.specs {
		g, err := s.rects[i].geom()
		if err != nil {
			return nil, err
		}
		lines := make([]string, len(s.texts[i].lines))
		for j, line := range s.texts[i].lines {
			lines[j] = line.Text
		}
		out[i] = scene.Label{ID: spec.id, Owner: spec.owner, Text: spec.text, Rect: g, Lines: lines}
	}
	return out, nil
}

func (s *pieScene) textItem(i int) (*scene.Text, error) {
	spec := s.specs[i]
	role, size := pieStyle(spec.kind)
	g, err := s.rects[i].geom()
	if err != nil {
		return nil, err
	}
	lines := make([][]scene.Run, len(s.texts[i].lines))
	for j, line := range s.texts[i].lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	align := scene.AlignStart
	if spec.kind != pieLabelLegend {
		align = scene.AlignMiddle
	}
	return &scene.Text{Rect: g, Role: textRole(role), Size: size, Align: align, Style: "text", Lines: lines}, nil
}

func (s *pieScene) groups() ([]*scene.Group, error) {
	plot := &scene.Group{Role: scene.GroupRoleNode, Owner: plotID}
	for i, sw := range s.swatches {
		g, err := sw.geom()
		if err != nil {
			return nil, err
		}
		plot.Items = append(plot.Items, &scene.Rect{Shape: barShape(i), Rect: g})
	}
	groups := []*scene.Group{plot}
	slices := map[string]*scene.Group{}
	for _, b := range s.p.boxSpecs() {
		if b.slice < 0 {
			continue
		}
		path, err := s.slicePath(s.p.slices[b.slice])
		if err != nil {
			return nil, err
		}
		g := &scene.Group{Role: scene.GroupRoleNode, Owner: b.id, Items: []scene.Primitive{path}}
		slices[b.id] = g
		groups = append(groups, g)
	}
	for i, spec := range s.specs {
		text, err := s.textItem(i)
		if err != nil {
			return nil, err
		}
		if spec.kind != pieLabelPercent {
			plot.Items = append(plot.Items, text)
			continue
		}
		plate := &scene.Rect{Shape: scene.Shape{Style: "plate"}, Rect: text.Rect}
		slices[spec.owner].Items = append(slices[spec.owner].Items, plate, text)
	}
	return groups, nil
}

func (s *pieScene) slicePath(sl pieSlice) (*scene.Path, error) {
	g := s.g
	b := &pathBuilder{}
	b.slice(g.cx, g.cy, g.radius, g.inner, geom.FloorMod(sl.start-pieQuarterTurn, pieFullTurn), sl.sweep)
	if b.err != nil {
		return nil, b.err
	}
	return &scene.Path{Shape: barShape(sl.section), Commands: b.commands}, nil
}

func layoutPie(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newPiePlan(m)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	p.fontFamily = o.FontFamily
	s, err := p.arrange()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	boxes, err := s.dumpBoxes()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	labels, err := s.dumpLabels()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	groups, err := s.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: string(m.Kind), Options: o, Canvas: s.canvas, Boxes: boxes, Labels: labels}
	dump.Options.Direction = scene.DirectionTB
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}
