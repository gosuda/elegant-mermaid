package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *wardleyPlan) buildRoutes() error {
	p.routes = p.w.skeletonRoutes()
	var ends [][2]pt
	for k := range p.w.Pipelines {
		for _, pair := range p.w.pipelineLinks(k) {
			ends = append(ends, [2]pt{p.pos[pair[0]], p.pos[pair[1]]})
		}
	}
	for _, l := range p.w.Links {
		ends = append(ends, [2]pt{p.pos[l.From], p.pos[l.To]})
	}
	for k, t := range p.w.Trends {
		ends = append(ends, [2]pt{p.pos[t.Node], p.ghosts[k]})
	}
	for i, e := range ends {
		a, err := pointOf(e[0].x, e[0].y)
		if err != nil {
			return err
		}
		b, err := pointOf(e[1].x, e[1].y)
		if err != nil {
			return err
		}
		p.routes[i].Points = []geom.Point{a, b}
	}
	return nil
}

func (p *wardleyPlan) placeBoxes() error {
	rects := []rect{p.plot}
	rects = append(rects, p.frames...)
	for _, q := range p.pos {
		rects = append(rects, rect{q.x, q.y, 0, 0})
	}
	for _, q := range p.ghosts {
		rects = append(rects, rect{q.x, q.y, 0, 0})
	}
	rects = append(rects, p.accels...)
	rects = append(rects, p.decels...)
	for _, q := range p.points {
		rects = append(rects, rect{q.x, q.y, 0, 0})
	}
	if p.w.showsBox() {
		rects = append(rects, p.box)
	}
	p.boxRects = make([]geom.Rect, len(rects))
	for i, r := range rects {
		g, err := r.geom()
		if err != nil {
			return err
		}
		p.boxRects[i] = g
	}
	return nil
}

func (p *wardleyPlan) grow() {
	for i, r := range p.rects {
		if p.shown[i] {
			p.width, p.height = max(p.width, int64(r.X)+int64(r.W)), max(p.height, int64(r.Y)+int64(r.H))
		}
	}
	if p.w.showsBox() {
		p.width, p.height = max(p.width, p.box.x+p.box.w), max(p.height, p.box.y+p.box.h)
	}
}

func (p *wardleyPlan) dumpBoxes() []scene.Box {
	boxes := p.w.skeletonBoxes()
	for i := range boxes {
		boxes[i].Rect = p.boxRects[i]
	}
	return boxes
}

func (p *wardleyPlan) dumpLabels() []scene.Label {
	labels := make([]scene.Label, len(p.specs))
	for i, s := range p.specs {
		labels[i] = scene.Label{ID: s.id, Owner: s.owner, Text: s.text, Rect: p.rects[i], Lines: p.lines[i]}
	}
	return labels
}

func (p *wardleyPlan) textItems(owner string) []scene.Primitive {
	var items []scene.Primitive
	for i, s := range p.specs {
		if s.owner == owner && p.shown[i] {
			items = append(items, p.textItem(i))
		}
	}
	return items
}

func (p *wardleyPlan) textItem(i int) *scene.Text {
	s := p.specs[i]
	role, size := p.styleOf(s)
	return &scene.Text{Rect: p.rects[i], Role: textRole(role), Size: size, Align: p.aligns[i], Style: wardleyTextStyle(s.kind), Lines: p.texts[i].runs()}
}

func wardleyTextStyle(kind wardleyKind) string {
	if kind == kindAxisX || kind == kindAxisY || kind == kindStage {
		return "text-muted"
	}
	return "text"
}

type groupList struct{ groups []*scene.Group }

func (g *groupList) add(role scene.GroupRole, owner string, items []scene.Primitive, err error) error {
	if err == nil && len(items) > 0 {
		g.groups = append(g.groups, &scene.Group{Role: role, Owner: owner, Items: items})
	}
	return err
}

func (p *wardleyPlan) groups() ([]*scene.Group, error) {
	list := &groupList{}
	if err := p.underlay(list); err != nil {
		return nil, err
	}
	if err := p.overlay(list); err != nil {
		return nil, err
	}
	return list.groups, nil
}

func (p *wardleyPlan) underlay(list *groupList) error {
	decor, err := p.decorItems()
	if err = list.add(scene.GroupRoleDecor, "", decor, err); err != nil {
		return err
	}
	for i := range p.routes {
		items, err := p.routeItems(i)
		if err = list.add(scene.GroupRoleEdge, p.routes[i].ID, items, err); err != nil {
			return err
		}
	}
	return nil
}

func (p *wardleyPlan) overlay(list *groupList) error {
	if err := list.add(scene.GroupRoleNode, wardleyPlotID, p.textItems(wardleyPlotID), nil); err != nil {
		return err
	}
	for k := range p.w.Pipelines {
		items, err := p.frameItems(k)
		if err = list.add(scene.GroupRoleNode, wardleyPipelineID(k), items, err); err != nil {
			return err
		}
	}
	for k := range p.w.Nodes {
		if err := p.nodeGroup(list, k); err != nil {
			return err
		}
	}
	return p.extraGroups(list)
}

func (p *wardleyPlan) nodeGroup(list *groupList, k int) error {
	id := wardleyNodeID(k)
	items, err := p.nodeItems(k)
	return list.add(scene.GroupRoleNode, id, append(items, p.textItems(id)...), err)
}

func (p *wardleyPlan) extraGroups(list *groupList) error {
	for k := range p.ghosts {
		items, err := p.ghostItems(k)
		if err = list.add(scene.GroupRoleNode, wardleyGhostID(k), items, err); err != nil {
			return err
		}
	}
	for k, r := range p.accels {
		items, err := p.acceleratorItems(r)
		id := wardleyAcceleratorID(k)
		if err = list.add(scene.GroupRoleNode, id, append(items, p.textItems(id)...), err); err != nil {
			return err
		}
	}
	for k, r := range p.decels {
		items, err := p.deacceleratorItems(r)
		id := wardleyDeacceleratorID(k)
		if err = list.add(scene.GroupRoleNode, id, append(items, p.textItems(id)...), err); err != nil {
			return err
		}
	}
	return p.annotationGroups(list)
}

func (p *wardleyPlan) annotationGroups(list *groupList) error {
	for k := range p.points {
		items, err := p.annotationItems(k)
		id := wardleyAnnotationID(k)
		if err = list.add(scene.GroupRoleNode, id, append(items, p.textItems(id)...), err); err != nil {
			return err
		}
	}
	if !p.w.showsBox() {
		return nil
	}
	items, err := p.boxItems()
	return list.add(scene.GroupRoleNode, wardleyBoxID, append(items, p.textItems(wardleyBoxID)...), err)
}
