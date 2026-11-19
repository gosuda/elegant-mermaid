package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *ganttPlan) fit(r rect) rect {
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	r.y = Clamp(r.y, 0, max(p.height-r.h, 0))
	return r
}

func (p *ganttPlan) place() error {
	if err := p.placeBoxes(); err != nil {
		return err
	}
	return p.placeLabels()
}

func (p *ganttPlan) taskRect(t chartmodel.GanttTask, row int) (rect, error) {
	start, err := p.timeX(t.Start)
	if err != nil {
		return rect{}, err
	}
	top := p.rowTop(row)
	switch {
	case t.Vert:
		return rect{start - geom.FloorDiv(p.c.vertW, 2), p.c.topPad, p.c.vertW, p.rows * p.pitch}, nil
	case t.Milestone:
		end, err := p.timeX(t.End)
		if err != nil {
			return rect{}, err
		}
		return rect{start + geom.FloorDiv(end-start, 2) - geom.FloorDiv(p.c.barH, 2), top, p.c.barH, p.c.barH}, nil
	}
	end, err := p.timeX(t.RenderEnd)
	if err != nil {
		return rect{}, err
	}
	return rect{start, top, max(end-start, 0) + p.c.edge, p.c.barH}, nil
}

func (p *ganttPlan) boxRect(b ganttBox) (rect, error) {
	switch b.kind {
	case ganttBoxPlot:
		return p.plot, nil
	case ganttBoxSection:
		return rect{0, p.rowTop(b.row), p.width, p.pitch}, nil
	}
	r, err := p.taskRect(p.g.Tasks[b.index], b.row)
	if err != nil {
		return rect{}, err
	}
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	return r, nil
}

func (p *ganttPlan) placeBoxes() error {
	p.boxRects = make([]geom.Rect, len(p.boxes))
	for i, b := range p.boxes {
		r, err := p.boxRect(b)
		if err != nil {
			return err
		}
		if p.boxRects[i], err = r.geom(); err != nil {
			return err
		}
	}
	p.laidOut = true
	return nil
}

func (p *ganttPlan) placeLabels() error {
	n := len(p.labels)
	p.labelRects = make([]geom.Rect, n)
	p.labelLines = make([][]string, n)
	p.aligns = make([]scene.Align, n)
	p.shown = make([]bool, n)
	p.chips = make([]bool, n)
	boxOf := p.boxIndex()
	for i, l := range p.labels {
		p.labelLines[i] = []string{}
		r, align, ok, err := p.labelRect(i, l, boxOf)
		if err != nil {
			return err
		}
		if !ok {
			continue
		}
		r = p.fit(r)
		if p.overlapsShown(i, r) {
			continue
		}
		g, err := r.geom()
		if err != nil {
			return err
		}
		p.labelRects[i], p.aligns[i], p.shown[i] = g, align, true
		p.chips[i] = p.needsChip(l, align)
		for _, line := range p.texts[i].lines {
			p.labelLines[i] = append(p.labelLines[i], line.Text)
		}
	}
	return nil
}

func (p *ganttPlan) boxIndex() map[string]int {
	out := make(map[string]int, len(p.boxes))
	for i, b := range p.boxes {
		out[b.id] = i
	}
	return out
}

func (p *ganttPlan) overlapsShown(i int, r rect) bool {
	if !p.cell {
		return false
	}
	for j := range i {
		if !p.shown[j] {
			continue
		}
		b := p.labelRects[j]
		if r.x < int64(b.X+b.W)+p.c.edge && int64(b.X) < r.x+r.w+p.c.edge && r.y < int64(b.Y+b.H) && int64(b.Y) < r.y+r.h {
			return true
		}
	}
	return false
}

func (p *ganttPlan) labelRect(i int, l ganttLabel, boxOf map[string]int) (rect, scene.Align, bool, error) {
	t := p.texts[i]
	switch l.kind {
	case ganttLabelTitle:
		half := geom.FloorDiv(t.w, 2)
		centre := Clamp(geom.FloorDiv(p.width, 2), half, p.width-half)
		return rect{centre - half, p.c.titlePad, t.w, t.h}, scene.AlignMiddle, true, nil
	case ganttLabelSection:
		row := p.boxes[boxOf[ganttBoxID(ganttBoxSection, l.index)]].row
		return rect{p.c.sectionPad, p.rowTop(row) + geom.FloorDiv(p.c.barH-t.h, 2), t.w, t.h}, scene.AlignStart, true, nil
	case ganttLabelTask:
		r, align := p.taskLabelRect(l, t, p.boxRects[boxOf[ganttBoxID(ganttBoxTask, l.index)]])
		return r, align, true, nil
	}
	x, err := p.timeX(p.ticks[l.index])
	if err != nil {
		return rect{}, scene.AlignMiddle, false, err
	}
	y := p.axisY() + p.c.tickLen + p.c.edge + p.c.tickGap
	if l.kind == ganttLabelTopTick {
		y = p.topAxisY() - p.c.tickLen - p.c.tickGap - t.h
	}
	return rect{x - geom.FloorDiv(t.w, 2), y, t.w, t.h}, scene.AlignMiddle, true, nil
}

func (p *ganttPlan) taskLabelRect(l ganttLabel, t textBox, box geom.Rect) (rect, scene.Align) {
	task := p.g.Tasks[l.index]
	x0, x1 := int64(box.X), int64(box.X)+int64(box.W)
	if task.Vert {
		below := p.axisY() + p.c.tickLen + p.c.edge + p.c.tickGap + p.lineHeight(measure.RoleLabel, ganttTickFont) + p.c.tickGap
		return rect{x0 + geom.FloorDiv(int64(box.W)-t.w, 2), below, t.w, t.h}, scene.AlignMiddle
	}
	y := int64(box.Y) + geom.FloorDiv(p.c.barH-t.h, 2)
	inside := rect{x0 + geom.FloorDiv(int64(box.W)-t.w, 2), y, t.w, t.h}
	if !p.cell && !task.Milestone && t.w <= int64(box.W) {
		return inside, scene.AlignMiddle
	}
	left := rect{x0 - p.c.labelGap - t.w, y, t.w, t.h}
	right := rect{x1 + p.c.labelGap, y, t.w, t.h}
	preferLeft := 2*(x1+t.w)+p.c.gutter > 2*p.width
	switch {
	case preferLeft && left.x >= 0:
		return left, scene.AlignEnd
	case right.x+right.w <= p.width:
		return right, scene.AlignStart
	case left.x >= 0:
		return left, scene.AlignEnd
	case p.cell:
		return rect{x0, int64(box.Y) + p.c.barH, t.w, t.h}, scene.AlignStart
	}
	return inside, scene.AlignMiddle
}

func (p *ganttPlan) needsChip(l ganttLabel, align scene.Align) bool {
	if l.kind != ganttLabelTask || align != scene.AlignMiddle {
		return false
	}
	t := p.g.Tasks[l.index]
	return !t.Vert && !t.Milestone && p.hasSeries(t)
}

func (p *ganttPlan) hasSeries(t chartmodel.GanttTask) bool {
	return !t.Crit && !t.Done && !t.Active && t.Section >= 0
}
