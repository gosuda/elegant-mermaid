package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *ganttPlan) groups() ([]*scene.Group, error) {
	var groups []*scene.Group
	under, err := p.underItems()
	if err != nil {
		return nil, err
	}
	if len(under) > 0 {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleDecor, Items: under})
	}
	for i, b := range p.boxes {
		items, err := p.boxItems(i, b)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: b.id, Items: items})
	}
	return groups, nil
}

func (p *ganttPlan) underItems() ([]scene.Primitive, error) {
	items, err := p.excludedColumns()
	if err != nil {
		return nil, err
	}
	axes := []int64{p.axisY()}
	if p.g.TopAxis {
		axes = append(axes, p.topAxisY())
	}
	for k, y := range axes {
		sign := int64(1)
		if k == 1 {
			sign = -1
		}
		lines, err := p.axisLines(y, sign)
		if err != nil {
			return nil, err
		}
		items = append(items, lines...)
	}
	return items, nil
}

func (p *ganttPlan) line(x0, y0, x1, y1 int64) (scene.Primitive, error) {
	from, err := pointOf(x0, y0)
	if err != nil {
		return nil, err
	}
	to, err := pointOf(x1, y1)
	if err != nil {
		return nil, err
	}
	return &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{from, to}}, nil
}

func (p *ganttPlan) axisLines(y, sign int64) ([]scene.Primitive, error) {
	first, err := p.line(p.c.gutter, y, p.c.width-p.c.sidePad, y)
	if err != nil {
		return nil, err
	}
	items := []scene.Primitive{first}
	for _, t := range p.ticks {
		x, err := p.timeX(t)
		if err != nil {
			return nil, err
		}
		if p.c.tickLen > 0 {
			tick, err := p.line(x, y, x, y+sign*p.c.tickLen)
			if err != nil {
				return nil, err
			}
			items = append(items, tick)
		}
		if p.cell || sign < 0 || p.rows == 0 {
			continue
		}
		grid, err := p.line(x, p.c.topPad, x, y)
		if err != nil {
			return nil, err
		}
		items = append(items, grid)
	}
	return items, nil
}

func (p *ganttPlan) excludedColumns() ([]scene.Primitive, error) {
	span := p.d1 - p.d0
	if span <= 0 || span > p.c.excludeYears*366*civil.SecondsPerDay || p.rows == 0 {
		return nil, nil
	}
	cal := civil.NewCalendar(p.g.Excludes, p.g.Includes, p.g.Weekend)
	var items []scene.Primitive
	first, last := geom.FloorDiv(p.d0, civil.SecondsPerDay), geom.FloorDiv(p.d1-1, civil.SecondsPerDay)
	for day := first; day <= last; day++ {
		if !cal.Excluded(day) {
			continue
		}
		run := day
		for run < last && cal.Excluded(run+1) {
			run++
		}
		item, err := p.excludedRun(day, run)
		if err != nil {
			return nil, err
		}
		items = append(items, item)
		day = run
	}
	return items, nil
}

func (p *ganttPlan) excludedRun(first, last int64) (scene.Primitive, error) {
	x0, err := p.timeX(max(first*civil.SecondsPerDay, p.d0))
	if err != nil {
		return nil, err
	}
	x1, err := p.timeX(min((last+1)*civil.SecondsPerDay, p.d1))
	if err != nil {
		return nil, err
	}
	r, err := rect{min(x0, x1), p.c.topPad, abs64(x1 - x0), p.rows * p.pitch}.geom()
	if err != nil {
		return nil, err
	}
	return &scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: r}, nil
}

func abs64(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func (p *ganttPlan) boxItems(i int, b ganttBox) ([]scene.Primitive, error) {
	var items []scene.Primitive
	switch b.kind {
	case ganttBoxSection:
		items = []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: p.boxRects[i]}}
	case ganttBoxTask, ganttBoxVert:
		items = p.taskItems(p.g.Tasks[b.index], p.boxRects[i])
	}
	return append(items, p.textItems(b.id)...), nil
}

func (p *ganttPlan) barShape(t chartmodel.GanttTask) scene.Shape {
	switch {
	case t.Crit:
		return scene.Shape{Style: "error"}
	case t.Done:
		return scene.Shape{Style: "success"}
	case t.Active:
		return scene.Shape{Style: "note"}
	case t.Section < 0:
		return scene.Shape{Style: "node"}
	}
	return scene.Shape{Style: "series", Series: uint8(t.Section % seriesCount)}
}

func (p *ganttPlan) taskItems(t chartmodel.GanttTask, r geom.Rect) []scene.Primitive {
	switch {
	case t.Vert:
		return []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: r}}
	case t.Milestone && p.cell:
		return []scene.Primitive{&scene.SymbolRef{Symbol: "diamond", At: geom.Point{X: r.X, Y: r.Y}, Style: "ink"}}
	case t.Milestone:
		cx, cy := r.X+r.W/2, r.Y+r.H/2
		points := []geom.Point{{X: cx, Y: r.Y}, {X: r.X + r.W, Y: cy}, {X: cx, Y: r.Y + r.H}, {X: r.X, Y: cy}}
		return []scene.Primitive{&scene.Polygon{Shape: scene.Shape{Style: "ink"}, Points: points}}
	}
	return []scene.Primitive{&scene.Rect{Shape: p.barShape(t), Rect: r}}
}

func (p *ganttPlan) textItems(owner string) []scene.Primitive {
	var items []scene.Primitive
	for i, l := range p.labels {
		if l.owner != owner || !p.shown[i] {
			continue
		}
		if p.chips[i] {
			items = append(items, &scene.Rect{Shape: scene.Shape{Style: "plate"}, Rect: p.labelRects[i]})
		}
		items = append(items, p.textItem(i))
	}
	return items
}

func (p *ganttPlan) textItem(i int) *scene.Text {
	role, size := p.styleOf(p.labels[i])
	style := "text"
	if kind := p.labels[i].kind; kind == ganttLabelTick || kind == ganttLabelTopTick {
		style = "text-muted"
	}
	lines := make([][]scene.Run, len(p.texts[i].lines))
	for j, line := range p.texts[i].lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return &scene.Text{Rect: p.labelRects[i], Role: textRole(role), Size: size, Align: p.aligns[i], Style: style, Lines: lines}
}
