package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *cynefinPlan) placeLabels() {
	if p.titleShown {
		p.setLabel(cynefinTitleID, p.titleAt, scene.AlignMiddle, p.title)
	}
	for i := range p.domains {
		d := &p.domains[i]
		p.setLabel(domainLabelID(d.name), d.nameAt, scene.AlignMiddle, d.title)
		for k, item := range d.items {
			p.setLabel(itemLabelID(d.name, k), d.texts[k], scene.AlignMiddle, item)
		}
	}
}

func (p *cynefinPlan) dump() ([]scene.Box, []scene.Route, []scene.Label, error) {
	frame := CynefinSkeleton(p.m)
	for i := range frame.Boxes {
		b := &frame.Boxes[i]
		at := p.frame()
		if b.ID != cynefinFrameID {
			at = p.domain(b.ID).box
		}
		g, err := at.geom()
		if err != nil {
			return nil, nil, nil, err
		}
		b.Rect = g
	}
	for i := range frame.Routes {
		for _, pt := range p.paths[i] {
			at, err := pointOf(pt.x, pt.y)
			if err != nil {
				return nil, nil, nil, err
			}
			frame.Routes[i].Points = append(frame.Routes[i].Points, at)
		}
	}
	for i := range frame.Labels {
		l := &frame.Labels[i]
		placed := p.labels[l.ID]
		g, err := placed.at.geom()
		if err != nil {
			return nil, nil, nil, err
		}
		l.Rect, l.Lines = g, placed.box.plain()
	}
	return frame.Boxes, frame.Routes, frame.Labels, nil
}

func (p *cynefinPlan) textItem(id string, role measure.Role) (*scene.Text, error) {
	placed := p.labels[id]
	return p.style(role).item(placed.box, placed.at, placed.align)
}

func (p *cynefinPlan) groups() ([]*scene.Group, error) {
	decor, err := p.decor()
	if err != nil {
		return nil, err
	}
	groups := []*scene.Group{{Role: scene.GroupRoleDecor, Items: decor}}
	for i, r := range p.routes {
		items, err := p.edgeItems(i)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: r.id, Items: items})
	}
	frame := &scene.Group{Role: scene.GroupRoleNode, Owner: cynefinFrameID}
	if p.titleShown {
		title, err := p.textItem(cynefinTitleID, measure.RoleTitle)
		if err != nil {
			return nil, err
		}
		frame.Items = append(frame.Items, title)
	}
	groups = append(groups, frame)
	for i := range p.domains {
		items, err := p.domainItems(&p.domains[i])
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: p.domains[i].name, Items: items})
	}
	return groups, nil
}

func (p *cynefinPlan) domainItems(d *domainPlan) ([]scene.Primitive, error) {
	var items []scene.Primitive
	if p.profile == scene.ProfileVector {
		for _, badge := range d.badges {
			g, err := badge.geom()
			if err != nil {
				return nil, err
			}
			items = append(items, &scene.RoundRect{Shape: scene.Shape{Style: "node"}, Rect: g, R: int32(p.c.corner)})
		}
	}
	name, err := p.textItem(domainLabelID(d.name), measure.RoleLabel)
	if err != nil {
		return nil, err
	}
	items = append(items, name)
	for k := range d.items {
		item, err := p.textItem(itemLabelID(d.name, k), measure.RoleBody)
		if err != nil {
			return nil, err
		}
		items = append(items, item)
	}
	return items, nil
}

func (p *cynefinPlan) edgeItems(index int) ([]scene.Primitive, error) {
	path := p.paths[index]
	line := &scene.Polyline{Shape: scene.Shape{Style: "edge"}, Corner: int32(p.c.corner)}
	for _, pt := range path {
		at, err := pointOf(pt.x, pt.y)
		if err != nil {
			return nil, err
		}
		line.Points = append(line.Points, at)
	}
	items := []scene.Primitive{line}
	if n := len(path); n > 1 {
		items = append(items, &scene.MarkerRef{Marker: "point", At: line.Points[n-1], Axis: axisOf(path[n-2], path[n-1])})
	}
	if p.routes[index].label != "" {
		label, err := p.textItem(routeLabelID(index), measure.RoleBody)
		if err != nil {
			return nil, err
		}
		items = append(items, label)
	}
	return items, nil
}

func (p *cynefinPlan) decor() ([]scene.Primitive, error) {
	var items []scene.Primitive
	for _, name := range [...]string{"complex", "complicated", "clear", "chaotic"} {
		g, err := p.quadrant(name).geom()
		if err != nil {
			return nil, err
		}
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: g})
	}
	fold, err := p.foldItem()
	if err != nil {
		return nil, err
	}
	items = append(items, fold)
	dividers, err := p.dividers()
	if err != nil {
		return nil, err
	}
	items = append(items, dividers...)
	cliff, err := cliffPath(p.c.width, p.c.height, p.cx, p.cy)
	if err != nil {
		return nil, err
	}
	items = append(items, cliff)
	ellipse, err := p.ellipseItem()
	if err != nil {
		return nil, err
	}
	return append(items, ellipse), nil
}

func (p *cynefinPlan) foldItem() (scene.Primitive, error) {
	fold := newFold(p.c.seed, p.cx, p.c.height, p.c.amplitude, p.c.waves)
	if p.profile == scene.ProfileCell {
		return fold.linePath()
	}
	return fold.path()
}

func (p *cynefinPlan) dividers() ([]scene.Primitive, error) {
	rx, _ := p.ellipse()
	var items []scene.Primitive
	for _, span := range [...][2]int64{{0, p.cx - rx}, {p.cx + rx, p.c.width - p.c.edge}} {
		if span[0] >= span[1] {
			continue
		}
		from, err := pointOf(span[0], p.cy)
		if err != nil {
			return nil, err
		}
		to, err := pointOf(span[1], p.cy)
		if err != nil {
			return nil, err
		}
		items = append(items, &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{from, to}})
	}
	return items, nil
}

func (p *cynefinPlan) ellipseItem() (scene.Primitive, error) {
	rx, ry := p.ellipse()
	cx, err := i32(p.cx)
	if err != nil {
		return nil, err
	}
	cy, err := i32(p.cy)
	if err != nil {
		return nil, err
	}
	rxs, err := i32(rx)
	if err != nil {
		return nil, err
	}
	rys, err := i32(ry)
	if err != nil {
		return nil, err
	}
	return &scene.Ellipse{Shape: scene.Shape{Style: "group"}, CX: cx, CY: cy, RX: rxs, RY: rys}, nil
}
