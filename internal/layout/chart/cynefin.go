package chart

import (
	"context"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type placedLabel struct {
	at    rect
	align scene.Align
	box   textBox
}

type cynefinPlan struct {
	m          *chartmodel.Cynefin
	profile    scene.Profile
	c          cynefinConsts
	title      textBox
	titleAt    rect
	titleShown bool
	domains    []domainPlan
	routes     []cynefinRoute
	routeBoxes []textBox
	paths      [][]curvePoint
	labels     map[string]placedLabel
	extents    []rect
	cx, cy     int64
	width      int64
	height     int64
}

func newCynefinPlan(m *chartmodel.Cynefin, o scene.Options) (*cynefinPlan, error) {
	c, err := loadCynefinConsts(o.Profile, m)
	if err != nil {
		return nil, err
	}
	p := &cynefinPlan{m: m, profile: o.Profile, c: c, routes: cynefinRoutes(m), labels: map[string]placedLabel{}}
	p.cx, p.cy = geom.FloorDiv(c.width, 2), geom.FloorDiv(c.height, 2)
	return p, p.measure()
}

func (p *cynefinPlan) style(role measure.Role) textStyle {
	return textStyle{profile: p.profile, role: role, size: role.SizePx()}
}

func (p *cynefinPlan) measure() error {
	var err error
	p.titleShown = p.m.Title != ""
	if p.titleShown {
		if p.title, err = p.style(measure.RoleTitle).measure(p.m.Title); err != nil {
			return err
		}
	}
	for _, d := range normalizedDomains(p.m) {
		plan := domainPlan{name: d.Name}
		if plan.title, err = p.style(measure.RoleLabel).measure(domainTitle(d.Name)); err != nil {
			return err
		}
		for _, item := range d.Items {
			box, err := p.style(measure.RoleBody).measure(item)
			if err != nil {
				return err
			}
			plan.items = append(plan.items, box)
		}
		p.domains = append(p.domains, plan)
	}
	for _, r := range p.routes {
		box, err := p.style(measure.RoleBody).measure(r.label)
		if err != nil {
			return err
		}
		p.routeBoxes = append(p.routeBoxes, box)
	}
	return nil
}

func (p *cynefinPlan) quadrant(name string) rect {
	hw, hh := geom.FloorDiv(p.c.width, 2), geom.FloorDiv(p.c.height, 2)
	switch name {
	case "complex":
		return rect{0, 0, hw, hh}
	case "complicated":
		return rect{hw, 0, p.c.width - hw, hh}
	case "clear":
		return rect{hw, hh, p.c.width - hw, p.c.height - hh}
	}
	return rect{0, hh, hw, p.c.height - hh}
}

func (p *cynefinPlan) stackOrigin(d *domainPlan) (cx, top int64) {
	c := p.c
	if d.name == confusionName {
		return p.cx, max(c.boxPad, p.cy-geom.FloorDiv(d.height(c), 2))
	}
	q := p.quadrant(d.name)
	cx, top = q.x+geom.FloorDiv(q.w, 2), q.y+c.pad
	if q.y == 0 && p.titleShown {
		top = q.y + 2*c.pad + p.title.h
	}
	return cx, top
}

func (p *cynefinPlan) place() {
	if p.titleShown {
		half := geom.FloorDiv(p.title.w, 2)
		p.titleAt = rect{max(0, p.cx-half), p.c.pad, p.title.w, p.title.h}
	}
	for i := range p.domains {
		d := &p.domains[i]
		lo, hi := d.span(p.c)
		cx, top := p.stackOrigin(d)
		d.place(p.c, max(lo, min(cx, p.c.width-hi)), top)
	}
	p.placeLabels()
	p.route()
	p.fitCanvas()
}

func (p *cynefinPlan) domain(name string) *domainPlan {
	i := slices.IndexFunc(p.domains, func(d domainPlan) bool { return d.name == name })
	return &p.domains[i]
}

func (p *cynefinPlan) fitCanvas() {
	p.width, p.height = p.c.width, p.c.height
	grow := func(r rect) {
		p.width, p.height = max(p.width, r.right()), max(p.height, r.bottom())
	}
	for _, r := range p.extents {
		grow(r)
	}
	for _, d := range p.domains {
		grow(d.box)
	}
	for _, path := range p.paths {
		for _, pt := range path {
			grow(rect{pt.x, pt.y, 0, 0})
		}
	}
}

func (p *cynefinPlan) frame() rect { return rect{0, 0, p.width, p.height} }

func (p *cynefinPlan) ellipse() (rx, ry int64) {
	return geom.FloorDiv(p.c.width*p.c.confusion, 1000), geom.FloorDiv(p.c.height*p.c.confusion, 1000)
}

func LayoutCynefin(ctx context.Context, m *chartmodel.Cynefin, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	if err := ctx.Err(); err != nil {
		return scene.Scene{}, nil, err
	}
	p, err := newCynefinPlan(m, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	p.place()
	w, err := i32(p.width)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	h, err := i32(p.height)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: cynefinKind, Options: o, Canvas: geom.Size{W: w, H: h}}
	dump.Options.Direction = scene.DirectionTB
	if dump.Boxes, dump.Routes, dump.Labels, err = p.dump(); err != nil {
		return scene.Scene{}, nil, err
	}
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}
