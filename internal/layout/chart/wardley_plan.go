package chart

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type pt struct{ x, y int64 }

type wardleyConsts struct {
	padX, padY, width, height               int64
	nodeRadius, labelGap, squareSize        int64
	pipelinePad, pipelineHeight, inertiaGap int64
	inertiaWidth, marketRing, marketDot     int64
	annotationRadius, boxPad, arrowWidth    int64
	arrowShaft, arrowHead, arrowTip         int64
	linkLabelGap, axisGap, stageGap         int64
	labelSize, axisSize, noteSize, edge     int64
}

func loadWardleyConsts(profile scene.Profile, config []scene.Config) (wardleyConsts, error) {
	var c wardleyConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"wardley.padding_x", &c.padX}, {"wardley.padding_y", &c.padY}, {"wardley.width", &c.width}, {"wardley.height", &c.height},
		{"wardley.node_radius", &c.nodeRadius}, {"wardley.label_gap", &c.labelGap}, {"wardley.square_size", &c.squareSize},
		{"wardley.pipeline_pad", &c.pipelinePad}, {"wardley.pipeline_height", &c.pipelineHeight}, {"wardley.inertia_gap", &c.inertiaGap},
		{"wardley.inertia_width", &c.inertiaWidth}, {"wardley.market_ring", &c.marketRing}, {"wardley.market_dot", &c.marketDot},
		{"wardley.annotation_radius", &c.annotationRadius}, {"wardley.box_pad", &c.boxPad}, {"wardley.arrow_width", &c.arrowWidth},
		{"wardley.arrow_shaft", &c.arrowShaft}, {"wardley.arrow_head", &c.arrowHead}, {"wardley.arrow_tip", &c.arrowTip},
		{"wardley.link_label_gap", &c.linkLabelGap}, {"wardley.axis_gap", &c.axisGap}, {"wardley.stage_gap", &c.stageGap},
		{"wardley.label_size", &c.labelSize}, {"wardley.axis_size", &c.axisSize}, {"wardley.note_size", &c.noteSize},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return wardleyConsts{}, err
		}
		*row.into = value
	}
	if profile == scene.ProfileCell {
		c.edge = 1
	}
	c.applyConfig(profile, config)
	return c, nil
}

func configInteger(config []scene.Config, key string) (int64, bool) {
	for _, entry := range config {
		if entry.Key != key {
			continue
		}
		n, err := strconv.ParseInt(entry.Value, 10, 64)
		return n, err == nil
	}
	return 0, false
}

func (c *wardleyConsts) applyConfig(profile scene.Profile, config []scene.Config) {
	if n, ok := configInteger(config, "width"); ok {
		c.width = canvasSide(profile, n, 64, 8)
	}
	if n, ok := configInteger(config, "height"); ok {
		c.height = canvasSide(profile, n, 64, 16)
	}
	if n, ok := configInteger(config, "padding"); ok {
		c.padX, c.padY = canvasSide(profile, n, 64, 8), canvasSide(profile, n, 64, 16)
	}
}

type wardleyPlan struct {
	w        *Wardley
	o        scene.Options
	c        wardleyConsts
	cell     bool
	width    int64
	height   int64
	plot     rect
	base     []pt
	pos      []pt
	frames   []rect
	ghosts   []pt
	accels   []rect
	decels   []rect
	points   []pt
	notes    []pt
	box      rect
	boxed    []int
	specs    []wardleySpec
	texts    []textBox
	shown    []bool
	rects    []geom.Rect
	aligns   []scene.Align
	lines    [][]string
	boxRects []geom.Rect
	routes   []scene.Route
}

func newWardleyPlan(w *Wardley, o scene.Options) (*wardleyPlan, error) {
	c, err := loadWardleyConsts(o.Profile, o.Config)
	if err != nil {
		return nil, err
	}
	p := &wardleyPlan{w: w, o: o, c: c, cell: o.Profile == scene.ProfileCell, boxed: w.boxLines(), specs: w.specs()}
	p.width = max(c.width, 2*c.padX+c.arrowWidth+c.edge)
	p.height = max(c.height, 2*c.padY+2*(c.arrowShaft+c.arrowHead)+c.edge)
	p.plot = rect{c.padX, c.padY, p.width - 2*c.padX, p.height - 2*c.padY}
	return p, nil
}

func (p *wardleyPlan) project(x, y int64) pt {
	fx, fy := Clamp(x, 0, wardleyFullScale), Clamp(y, 0, wardleyFullScale)
	return pt{
		x: p.plot.x + geom.FloorDiv(fx*p.plot.w, wardleyFullScale),
		y: p.plot.y + p.plot.h - geom.FloorDiv(fy*p.plot.h, wardleyFullScale),
	}
}

func (p *wardleyPlan) clampPlot(q pt) pt {
	return pt{Clamp(q.x, p.plot.x, p.plot.x+p.plot.w), Clamp(q.y, p.plot.y, p.plot.y+p.plot.h)}
}

func (p *wardleyPlan) fitPlot(r rect) rect {
	r.x = Clamp(r.x, p.plot.x, max(p.plot.x+p.plot.w-r.w, p.plot.x))
	r.y = Clamp(r.y, p.plot.y, max(p.plot.y+p.plot.h-r.h, p.plot.y))
	return r
}

func (p *wardleyPlan) fitCanvas(r rect) rect {
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	r.y = Clamp(r.y, 0, max(p.height-r.h, 0))
	return r
}

func (p *wardleyPlan) clipPlot(r rect) rect {
	x0, y0 := max(r.x, p.plot.x), max(r.y, p.plot.y)
	x1, y1 := min(r.x+r.w, p.plot.x+p.plot.w), min(r.y+r.h, p.plot.y+p.plot.h)
	return rect{x0, y0, max(x1-x0, 0), max(y1-y0, 0)}
}

func (p *wardleyPlan) arrange() {
	w := p.w
	p.base = make([]pt, len(w.Nodes))
	for i, n := range w.Nodes {
		p.base[i] = p.project(n.X, n.Y)
	}
	p.pos = slices.Clone(p.base)
	p.frames = make([]rect, len(w.Pipelines))
	for k, pl := range w.Pipelines {
		p.placePipeline(k, pl)
	}
	for _, t := range w.Trends {
		p.ghosts = append(p.ghosts, p.project(t.TargetX, t.TargetY))
	}
	for _, f := range w.Accelerators {
		p.accels = append(p.accels, p.forceRect(f))
	}
	for _, f := range w.Deaccelerators {
		p.decels = append(p.decels, p.forceRect(f))
	}
	for _, a := range w.Annotations {
		p.points = append(p.points, p.project(a.X, a.Y))
	}
	for _, n := range w.Notes {
		p.notes = append(p.notes, p.project(n.X, n.Y))
	}
}

func (p *wardleyPlan) placePipeline(k int, pl WardleyPipeline) {
	lo := p.base[pl.Children[0]]
	hi := lo
	for _, child := range pl.Children[1:] {
		b := p.base[child]
		lo, hi = pt{min(lo.x, b.x), min(lo.y, b.y)}, pt{max(hi.x, b.x), max(hi.y, b.y)}
	}
	c := p.c
	half := geom.FloorDiv(c.pipelineHeight, 2)
	top := lo.y - half
	p.frames[k] = p.clipPlot(rect{lo.x - c.pipelinePad, top, hi.x - lo.x + 2*c.pipelinePad + c.edge, hi.y - lo.y + 2*half + c.edge})
	p.pos[pl.Parent] = p.clampPlot(pt{geom.FloorDiv(lo.x+hi.x, 2), top - geom.FloorDiv(c.squareSize, 6)})
}

func (p *wardleyPlan) forceRect(f WardleyForce) rect {
	c := p.c
	at := p.project(f.X, f.Y)
	half := c.arrowShaft + c.arrowHead
	return p.fitPlot(rect{at.x, at.y - half, c.arrowWidth + c.edge, 2*half + c.edge})
}

func (p *wardleyPlan) stageSpan(i int) (start, end int64) {
	stages := int64(len(p.w.Stages))
	if len(p.w.Boundaries) == len(p.w.Stages) {
		start = p.plot.x
		if i > 0 {
			start = p.plot.x + geom.FloorDiv(Clamp(p.w.Boundaries[i-1], 0, scale)*p.plot.w, scale)
		}
		return start, p.plot.x + geom.FloorDiv(Clamp(p.w.Boundaries[i], 0, scale)*p.plot.w, scale)
	}
	return p.plot.x + geom.FloorDiv(int64(i)*p.plot.w, stages), p.plot.x + geom.FloorDiv(int64(i+1)*p.plot.w, stages)
}

func (p *wardleyPlan) styleOf(s wardleySpec) (measure.Role, int32) {
	switch s.kind {
	case kindTitle:
		return measure.RoleTitle, measure.RoleTitle.SizePx()
	case kindAxisX, kindAxisY, kindStage:
		return measure.RoleLabel, int32(p.c.axisSize / 64)
	case kindNote, kindNumber:
		return measure.RoleLabel, int32(p.c.noteSize / 64)
	case kindAnnotation:
		return measure.RoleBody, int32(p.c.noteSize / 64)
	}
	return measure.RoleBody, int32(p.c.labelSize / 64)
}

func (p *wardleyPlan) textStyleFor(role measure.Role, size int32) textStyle {
	profile := scene.ProfileVector
	if p.cell {
		profile = scene.ProfileCell
	}
	return textStyle{profile: profile, role: role, size: size, fontFamily: p.o.FontFamily}
}

func (p *wardleyPlan) measureAll() error {
	p.texts = make([]textBox, len(p.specs))
	for i, s := range p.specs {
		if s.text == "" {
			continue
		}
		role, size := p.styleOf(s)
		box, err := p.textStyleFor(role, size).measure(s.text)
		if err != nil {
			return err
		}
		p.texts[i] = box
	}
	return nil
}
