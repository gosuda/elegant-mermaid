package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/grid"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *kanbanPlan) groups(placed grid.KanbanLayout) []*scene.Group {
	groups := make([]*scene.Group, 0, len(p.sections)+len(p.cards))
	for k, i := range p.sections {
		items := []scene.Primitive{&scene.RoundRect{Shape: plainShape("group"), Rect: placed.Sections[k], R: p.c.corner}}
		if len(p.titles[k]) > 0 {
			items = append(items, p.textItem(placed.Labels[k], scene.AlignMiddle, p.titles[k]))
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: p.in.Boxes[i].ID, Items: items})
	}
	for k, i := range p.cards {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: p.in.Boxes[i].ID, Items: p.cardItems(placed.Cards[k], p.texts[k])})
	}
	return groups
}

func (p *kanbanPlan) cardItems(rect geom.Rect, lines []measure.StyledLine) []scene.Primitive {
	frame := &scene.RoundRect{Shape: plainShape("node"), Rect: rect, R: p.c.corner}
	height := int32(len(lines)) * p.c.lineHeight
	box := geom.Rect{X: rect.X + p.c.cardPadX, Y: rect.Y + p.c.border + p.c.cardPadY, W: rect.W - 2*p.c.cardPadX, H: height}
	return []scene.Primitive{frame, p.textItem(box, scene.AlignStart, lines)}
}

func (p *kanbanPlan) textItem(rect geom.Rect, align scene.Align, lines []measure.StyledLine) *scene.Text {
	return &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: align, Style: "text", Lines: sequenceRuns(lines)}
}
