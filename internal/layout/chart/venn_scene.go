package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *vennPlan) build() (scene.Scene, []diag.Diagnostic, error) {
	w, err := i32(p.width)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	h, err := i32(p.height)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: string(chartmodel.KindVenn), Options: p.o, Canvas: geom.Size{W: w, H: h}, Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}
	dump.Options.Direction = scene.DirectionTB
	groups, err := p.groups()
	return scene.Scene{Dump: dump, Groups: groups}, nil, err
}

func (p *vennPlan) groups() ([]*scene.Group, error) {
	groups := make([]*scene.Group, 0, len(p.boxes))
	for _, b := range p.boxes {
		items, err := p.boxItems(b)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: b.id, Items: items})
	}
	return groups, nil
}

func (p *vennPlan) boxItems(b vennBox) ([]scene.Primitive, error) {
	var out []scene.Primitive
	if b.set >= 0 {
		circle, err := p.ellipse(b.set)
		if err != nil {
			return nil, err
		}
		out = append(out, circle)
	}
	for _, id := range b.items {
		out = append(out, p.textItem(p.items[id]))
	}
	return out, nil
}

func (p *vennPlan) ellipse(set int) (*scene.Ellipse, error) {
	c := p.circles[set]
	var out [3]int32
	for i, v := range [3]int64{c.x, c.y, c.r} {
		var err error
		if out[i], err = i32(v); err != nil {
			return nil, err
		}
	}
	shape := scene.Shape{Style: "series-tint", Series: uint8(set % seriesCount)}
	return &scene.Ellipse{Shape: shape, CX: out[0], CY: out[1], RX: out[2], RY: out[2]}, nil
}

func (p *vennPlan) textItem(it vennItem) *scene.Text {
	role := measure.RoleLabel
	if it.title {
		role = measure.RoleTitle
	}
	lines := make([][]scene.Run, len(it.box.lines))
	for j, line := range it.box.lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return &scene.Text{Rect: it.rect, Role: textRole(role), Size: role.SizePx(), Align: scene.AlignMiddle, Style: "text", Lines: lines}
}
