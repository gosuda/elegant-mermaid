package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/grid"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *packetPlan) dump(result grid.PacketLayout) scene.Dump {
	options := p.in.Options
	options.Profile, options.Direction = p.profile, p.in.Direction
	d := scene.Dump{Kind: packetKind, Options: options, Canvas: result.Canvas}
	for i, box := range p.in.Boxes {
		rect := result.Title
		if !p.boxes[i].title {
			rect = result.Rects[p.boxes[i].piece]
		}
		p.boxes[i].rect = rect
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rect, Parent: box.Parent, Exclusive: box.Exclusive})
	}
	for j, label := range p.in.Labels {
		bit := p.bits[j]
		if bit == nil {
			continue
		}
		bit.rect = result.Lead[p.boxes[bit.owner].piece]
		if bit.trail {
			bit.rect = result.Trail[p.boxes[bit.owner].piece]
		}
		entry := scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text, Rect: bit.rect}
		for _, line := range bit.lines {
			entry.Lines = append(entry.Lines, line.Text)
		}
		d.Labels = append(d.Labels, entry)
	}
	return d
}

func (p *packetPlan) groups() []*scene.Group {
	groups := make([]*scene.Group, len(p.in.Boxes))
	for i, box := range p.in.Boxes {
		groups[i] = &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: p.items(p.boxes[i])}
	}
	return groups
}

func (p *packetPlan) items(box packetBox) []scene.Primitive {
	if box.title {
		return p.caption(box, scene.TextRoleTitle)
	}
	var items []scene.Primitive
	if box.rect.W > 0 {
		items = append(items, &scene.Rect{Shape: plainShape("node"), Rect: box.rect})
	}
	items = append(items, p.caption(box, scene.TextRoleLabel)...)
	alignLead := scene.AlignStart
	if box.start == box.end {
		alignLead = scene.AlignMiddle
	}
	for _, bit := range []struct {
		at    *packetBit
		align scene.Align
	}{{box.lead, alignLead}, {box.trail, scene.AlignEnd}} {
		if bit.at != nil {
			items = append(items, p.text(bit.at.rect, scene.TextRoleBody, bit.at.packetText, bit.align, "text-muted"))
		}
	}
	return items
}

func (p *packetPlan) caption(box packetBox, role scene.TextRole) []scene.Primitive {
	if len(box.text.lines) == 0 {
		return nil
	}
	textBox := geom.Rect{X: box.rect.X, Y: box.rect.Y + half(box.rect.H-box.text.size.H), W: box.rect.W, H: box.text.size.H}
	return []scene.Primitive{p.text(textBox, role, box.text, scene.AlignMiddle, "text")}
}

func (p *packetPlan) text(rect geom.Rect, role scene.TextRole, text packetText, align scene.Align, style string) *scene.Text {
	return &scene.Text{Rect: rect, Role: role, Size: packetRole(role).SizePx(), Align: align, Style: style, Lines: sequenceRuns(text.lines)}
}
