package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const sankeyKind = "sankey"

func (p *sankeyPlan) linkPoints(l flowLink) (from, to geom.Point, err error) {
	start := p.nodes[l.source]
	if from, err = pointOf(start.x+start.w, l.y0); err != nil {
		return from, to, err
	}
	to, err = pointOf(p.nodes[l.target].x, l.y1)
	return from, to, err
}

func (p *sankeyPlan) dump(o scene.Options) (scene.Dump, error) {
	w, err := i32(p.width)
	if err != nil {
		return scene.Dump{}, err
	}
	h, err := i32(p.height)
	if err != nil {
		return scene.Dump{}, err
	}
	d := scene.Dump{Stage: scene.StageLayout, Kind: sankeyKind, Options: o, Canvas: geom.Size{W: w, H: h}}
	d.Options.Profile, d.Options.Direction = scene.ProfileVector, scene.DirectionTB
	if err = p.dumpNodes(&d); err != nil {
		return scene.Dump{}, err
	}
	return d, p.dumpLinks(&d)
}

func (p *sankeyPlan) dumpNodes(d *scene.Dump) error {
	for i, r := range p.nodes {
		g, err := r.geom()
		if err != nil {
			return err
		}
		d.Boxes = append(d.Boxes, scene.Box{ID: SankeyNodeID(i), Role: scene.RoleNode, Rect: g})
		if p.texts[i] == nil {
			continue
		}
		lg, err := p.places[i].geom()
		if err != nil {
			return err
		}
		lines := make([]string, len(p.texts[i].lines))
		for j, l := range p.texts[i].lines {
			lines[j] = l.Text
		}
		d.Labels = append(d.Labels, scene.Label{ID: sankeyLabelID(i), Owner: SankeyNodeID(i), Text: p.s.Nodes[i].Label, Rect: lg, Lines: lines})
	}
	return nil
}

func (p *sankeyPlan) dumpLinks(d *scene.Dump) error {
	for i, l := range p.flow.links {
		from, to, err := p.linkPoints(l)
		if err != nil {
			return err
		}
		d.Routes = append(d.Routes, scene.Route{ID: SankeyLinkID(i), From: SankeyNodeID(l.source), To: SankeyNodeID(l.target), Points: []geom.Point{from, to}})
	}
	return nil
}

func (p *sankeyPlan) groups() ([]*scene.Group, error) {
	groups := make([]*scene.Group, 0, len(p.flow.links)+len(p.nodes))
	for i, l := range p.flow.links {
		path, err := p.linkPath(l)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: SankeyLinkID(i), Items: []scene.Primitive{path}})
	}
	for i, r := range p.nodes {
		g, err := r.geom()
		if err != nil {
			return nil, err
		}
		items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "series", Series: uint8(i % seriesCount)}, Rect: g}}
		if text, err := p.textItem(i); err != nil {
			return nil, err
		} else if text != nil {
			items = append(items, text)
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: SankeyNodeID(i), Items: items})
	}
	return groups, nil
}

func (p *sankeyPlan) linkPath(l flowLink) (*scene.Path, error) {
	from, to, err := p.linkPoints(l)
	if err != nil {
		return nil, err
	}
	width, err := i32(l.width)
	if err != nil {
		return nil, err
	}
	mid := int32(geom.FloorDiv(int64(from.X)+int64(to.X), 2))
	shape := scene.Shape{Style: "series-flow", Series: uint8(l.source % seriesCount), Width: scene.Width{Kind: scene.WidthUnits, Units: width}}
	curve := &scene.CubicTo{C1: geom.Point{X: mid, Y: from.Y}, C2: geom.Point{X: mid, Y: to.Y}, P: to}
	return &scene.Path{Shape: shape, Commands: []scene.Command{&scene.MoveTo{P: from}, curve}}, nil
}

func (p *sankeyPlan) textItem(i int) (*scene.Text, error) {
	text := p.texts[i]
	if text == nil {
		return nil, nil
	}
	box, err := p.places[i].geom()
	if err != nil {
		return nil, err
	}
	lines := make([][]scene.Run, len(text.lines))
	for j, l := range text.lines {
		lines[j] = []scene.Run{{Text: l.Text}}
	}
	return &scene.Text{Rect: box, Role: scene.TextRoleLabel, Size: measure.RoleLabel.SizePx(), Align: p.aligns[i], Style: "text", Lines: lines}, nil
}
