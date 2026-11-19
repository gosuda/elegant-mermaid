package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *treemapPlan) frame(i int) ([]scene.Primitive, error) {
	r := p.nodes[i].rect.rect()
	if i == 0 || r.w <= 0 || r.h <= 0 {
		return nil, nil
	}
	g, err := r.geom()
	if err != nil {
		return nil, err
	}
	return []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "group"}, Rect: g}}, nil
}

func (p *treemapPlan) leafShape(i int) scene.Shape {
	style := "series-tint"
	if p.cell {
		style = "series"
	}
	return scene.Shape{Style: style, Series: uint8(p.nodes[i].series % seriesCount)}
}

func (p *treemapPlan) leafBody(i int) ([]scene.Primitive, error) {
	r := p.nodes[i].rect.rect()
	if r.w <= 0 || r.h <= 0 {
		return nil, nil
	}
	g, err := r.geom()
	if err != nil {
		return nil, err
	}
	return []scene.Primitive{&scene.Rect{Shape: p.leafShape(i), Rect: g}}, nil
}

func (p *treemapPlan) textItem(l *treemapLabel) *scene.Text {
	runs := []scene.Run{{Text: l.shown, Italic: l.italic}}
	return &scene.Text{Rect: l.rect, Role: l.role, Size: l.size, Align: l.align, Style: l.style, Lines: [][]scene.Run{runs}}
}

func (p *treemapPlan) texts(i int) []scene.Primitive {
	var indexes []int
	if i == 0 && p.title != "" {
		indexes = []int{0}
	}
	if i > 0 {
		indexes = []int{p.nodes[i].nameLabel, p.nodes[i].valueLabel}
	}
	var out []scene.Primitive
	for _, k := range indexes {
		if k >= 0 && p.labels[k].ok {
			out = append(out, p.textItem(&p.labels[k]))
		}
	}
	return out
}

func (p *treemapPlan) group(i int, role scene.GroupRole) (*scene.Group, error) {
	var items []scene.Primitive
	var err error
	if role == scene.GroupRoleNode {
		items, err = p.leafBody(i)
	} else {
		items, err = p.frame(i)
	}
	if err != nil {
		return nil, err
	}
	return &scene.Group{Role: role, Owner: treemapBoxID(i), Items: append(items, p.texts(i)...)}, nil
}

func (p *treemapPlan) groups() ([]*scene.Group, error) {
	var out []*scene.Group
	for _, role := range []struct {
		box   scene.BoxRole
		group scene.GroupRole
	}{{scene.RoleGroup, scene.GroupRoleGroup}, {scene.RoleNode, scene.GroupRoleNode}} {
		for i := range p.nodes {
			if p.role(i) != role.box {
				continue
			}
			g, err := p.group(i, role.group)
			if err != nil {
				return nil, err
			}
			out = append(out, g)
		}
	}
	return out, nil
}

var _ = geom.Rect{}
