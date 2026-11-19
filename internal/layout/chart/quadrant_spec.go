package chart

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	quadrantKind = "quadrant"
	tileCount    = 4

	NoPointRadius = -1
)

type QuadrantPoint struct {
	X, Y   int64
	Radius int64
	Label  string
}

type Quadrant struct {
	Title   string
	Config  map[string]int64
	Tiles   [tileCount]string
	XLeft   string
	XRight  string
	YBottom string
	YTop    string
	Points  []QuadrantPoint
}

type quadBoxKind uint8

const (
	quadPlot quadBoxKind = iota
	quadTile
	quadPoint
)

type quadBox struct {
	id    string
	kind  quadBoxKind
	index int
}

type quadLabelKind uint8

const (
	quadTitle quadLabelKind = iota
	quadXLeft
	quadXRight
	quadYBottom
	quadYTop
	quadTileLabel
	quadPointLabel
)

type quadLabel struct {
	id, owner, text string
	kind            quadLabelKind
	index           int
}

func tileBoxID(i int) string { return "q" + strconv.Itoa(i+1) }

func pointBoxID(i int) string { return "p" + strconv.Itoa(i) }

func quadrantBoxes(q *Quadrant) []quadBox {
	boxes := []quadBox{{id: plotID, kind: quadPlot}}
	for i := range tileCount {
		boxes = append(boxes, quadBox{id: tileBoxID(i), kind: quadTile, index: i})
	}
	for i := range q.Points {
		boxes = append(boxes, quadBox{id: pointBoxID(i), kind: quadPoint, index: i})
	}
	return boxes
}

func quadrantLabels(q *Quadrant) []quadLabel {
	var out []quadLabel
	add := func(label quadLabel) {
		if label.text != "" {
			out = append(out, label)
		}
	}
	add(quadLabel{id: "title", owner: plotID, text: q.Title, kind: quadTitle})
	add(quadLabel{id: "x.left", owner: plotID, text: q.XLeft, kind: quadXLeft})
	add(quadLabel{id: "x.right", owner: plotID, text: q.XRight, kind: quadXRight})
	add(quadLabel{id: "y.bottom", owner: plotID, text: q.YBottom, kind: quadYBottom})
	add(quadLabel{id: "y.top", owner: plotID, text: q.YTop, kind: quadYTop})
	for i, text := range q.Tiles {
		add(quadLabel{id: tileBoxID(i) + ".label", owner: tileBoxID(i), text: text, kind: quadTileLabel, index: i})
	}
	for i, point := range q.Points {
		add(quadLabel{id: pointBoxID(i) + ".label", owner: pointBoxID(i), text: point.Label, kind: quadPointLabel, index: i})
	}
	return out
}

func QuadrantSkeleton(q *Quadrant) Skeleton {
	plan := &quadPlan{q: q, boxes: quadrantBoxes(q), specs: quadrantLabels(q)}
	return Skeleton{Boxes: plan.dumpBoxes(), Labels: plan.dumpLabels()}
}

func (p *quadPlan) dumpBoxes() []scene.Box {
	out := make([]scene.Box, len(p.boxes))
	for i, b := range p.boxes {
		parent := plotID
		if b.kind == quadPlot {
			parent = ""
		}
		out[i] = scene.Box{ID: b.id, Role: scene.RoleNode, Parent: parent}
		if p.laidOut {
			out[i].Rect = p.boxRects[i]
		}
	}
	return out
}

func (p *quadPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.specs))
	for i, s := range p.specs {
		out[i] = scene.Label{ID: s.id, Owner: s.owner, Text: s.text}
		if p.laidOut {
			out[i].Rect = p.labelRects[i]
			out[i].Lines = p.labelLines[i]
		}
	}
	return out
}

func (r rect) within(outer rect) rect {
	x0, y0 := max(r.x, outer.x), max(r.y, outer.y)
	x1, y1 := min(r.x+r.w, outer.x+outer.w), min(r.y+r.h, outer.y+outer.h)
	return rect{x0, y0, max(x1-x0, 0), max(y1-y0, 0)}
}
