package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	emath "github.com/gosuda/elegant-mermaid/internal/math"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func mathCoordinate(v int64) (int32, error) {
	if v < int64(geom.I32Min) || v > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func mathRect(x, y, w, h int64) (geom.Rect, error) {
	values := [4]int64{x, y, w, h}
	var out [4]int32
	for i, v := range values {
		n, err := mathCoordinate(v)
		if err != nil {
			return geom.Rect{}, err
		}
		out[i] = n
	}
	return geom.Rect{X: out[0], Y: out[1], W: out[2], H: out[3]}, nil
}

type mathPlacement struct {
	text              *scene.Text
	baseline, drop, x int64
	shapes, texts     []scene.Primitive
	plain             []scene.Run
	start, width      int64
}

func hasMeasuredMath(lines []measure.StyledLine) bool {
	for _, line := range lines {
		for _, run := range line.Runs {
			if run.Math != nil {
				return true
			}
		}
	}
	return false
}

func measuredTextItems(text *scene.Text, lines []measure.StyledLine) ([]scene.Primitive, error) {
	if !hasMeasuredMath(lines) {
		return []scene.Primitive{text}, nil
	}
	lh := int64(1280)
	if text.Role == scene.TextRoleTitle {
		lh = 1536
	}
	p := mathPlacement{text: text, drop: lh/2 + int64(text.Size)*64*35/100}
	for k, line := range lines {
		p.baseline = int64(text.Rect.Y) + int64(k)*lh + p.drop
		p.x = int64(text.Rect.X)
		switch text.Align {
		case scene.AlignMiddle:
			p.x += int64(text.Rect.W)/2 - int64(line.Width)/2
		case scene.AlignEnd:
			p.x += int64(text.Rect.W) - int64(line.Width)
		}
		if err := p.emitLine(line); err != nil {
			return nil, err
		}
	}
	return append(p.shapes, p.texts...), nil
}

func (p *mathPlacement) flush() error {
	if len(p.plain) == 0 {
		return nil
	}
	r, err := mathRect(p.start, p.baseline-p.drop, p.width, p.drop)
	if err != nil {
		return err
	}
	p.texts = append(p.texts, &scene.Text{Rect: r, Role: p.text.Role, Size: p.text.Size, Align: scene.AlignStart, Style: p.text.Style, Lines: [][]scene.Run{p.plain}})
	p.plain = nil
	p.width = 0
	return nil
}

func (p *mathPlacement) emitLine(line measure.StyledLine) error {
	for _, run := range line.Runs {
		if run.Math == nil {
			p.appendPlain(run)
		} else if err := p.emitFormula(run.Math); err != nil {
			return err
		}
		p.x += int64(run.Width)
	}
	return p.flush()
}

func (p *mathPlacement) appendPlain(run measure.StyledRun) {
	if len(p.plain) == 0 {
		p.start = p.x
	}
	p.plain = append(p.plain, scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
	p.width += int64(run.Width)
}

func (p *mathPlacement) emitFormula(box *emath.Box) error {
	if err := p.flush(); err != nil {
		return err
	}
	for _, leaf := range box.Leaves {
		item, err := p.leafItem(leaf, box)
		if err != nil {
			return err
		}
		if leaf.Kind == emath.LeafGlyph {
			p.texts = append(p.texts, item)
		} else {
			p.shapes = append(p.shapes, item)
		}
	}
	return nil
}

func (p *mathPlacement) leafItem(leaf emath.Leaf, box *emath.Box) (scene.Primitive, error) {
	x, baseline, style := p.x, p.baseline, p.text.Style
	if leaf.Kind == emath.LeafGlyph {
		size := (int64(leaf.Size) + 32) / 64
		drop := int64(640) + size*64*35/100
		r, err := mathRect(x+int64(leaf.Rect.X), baseline-drop, int64(leaf.Rect.W), drop)
		if err != nil {
			return nil, err
		}
		cp := leaf.Codepoint
		for _, mapping := range gen.MathGlyphMappings {
			if rune(mapping.Codepoint) == cp {
				cp = rune(mapping.FontCodepoint)
				break
			}
		}
		return &scene.Text{Rect: r, Role: scene.TextRoleBody, Size: int32(size), Align: scene.AlignStart, Style: style, Lines: [][]scene.Run{{{Text: string(cp), Bold: leaf.Weight == emath.WeightBold, Italic: leaf.Shear}}}}, nil
	}
	shape := scene.Shape{Style: "rule"}
	if leaf.Kind == emath.LeafRule {
		r, err := mathRect(x+int64(leaf.Rect.X), baseline-int64(box.A)+int64(leaf.Rect.Y), int64(leaf.Rect.W), int64(leaf.Rect.H))
		return &scene.Rect{Shape: shape, Rect: r}, err
	}
	points := make([]geom.Point, len(leaf.Points))
	for i, point := range leaf.Points {
		px, err := mathCoordinate(x + int64(point.X))
		if err != nil {
			return nil, err
		}
		py, err := mathCoordinate(baseline - int64(box.A) + int64(point.Y))
		if err != nil {
			return nil, err
		}
		points[i] = geom.Point{X: px, Y: py}
	}
	return &scene.Polyline{Shape: shape, Points: points}, nil
}

func lowerMeasuredMath(s *scene.Scene, boxes, labels map[string][]measure.StyledLine) error {
	for _, group := range s.Groups {
		lines := mathGroupLines(group, s.Labels, boxes, labels)
		if err := lowerMathGroup(group, lines); err != nil {
			return err
		}
	}
	return nil
}

func mathGroupLines(group *scene.Group, relations []scene.Label, boxes, labels map[string][]measure.StyledLine) [][]measure.StyledLine {
	if group.Role != scene.GroupRoleEdge {
		return [][]measure.StyledLine{boxes[group.Owner]}
	}
	var lines [][]measure.StyledLine
	for _, label := range relations {
		if label.Owner == group.Owner {
			lines = append(lines, labels[label.ID])
		}
	}
	return lines
}

func lowerMathGroup(group *scene.Group, lines [][]measure.StyledLine) error {
	if !hasGroupMath(lines) {
		return nil
	}
	var items []scene.Primitive
	var labelShapes, texts []scene.Primitive
	index := 0
	for _, item := range group.Items {
		text, ok := item.(*scene.Text)
		if !ok || index >= len(lines) {
			items = append(items, item)
			continue
		}
		lowered, err := measuredTextItems(text, lines[index])
		if err != nil {
			return err
		}
		index++
		for _, primitive := range lowered {
			if _, ok := primitive.(*scene.Text); ok {
				texts = append(texts, primitive)
			} else {
				labelShapes = append(labelShapes, primitive)
			}
		}
	}
	if group.Role == scene.GroupRoleEdge {
		items = append(labelShapes, items...)
	} else {
		items = append(items, labelShapes...)
	}
	group.Items = append(items, texts...)
	return nil
}

func measuredMathLines(g *Graph, in Input, lines [][]measure.StyledLine) (map[string][]measure.StyledLine, map[string][]measure.StyledLine) {
	boxes := make(map[string][]measure.StyledLine, len(in.Boxes))
	labels := make(map[string][]measure.StyledLine, len(in.Labels))
	for i, box := range in.Boxes {
		boxes[box.ID] = lines[i]
	}
	for _, edge := range g.Edges {
		if edge.Label == nil {
			continue
		}
		for _, label := range edge.Label.Items {
			labels[label.ID] = label.Lines
		}
	}
	for _, label := range in.Labels {
		if lines, ok := boxes[label.Owner]; ok {
			labels[label.ID] = lines
		}
	}
	return boxes, labels
}

func hasGroupMath(lines [][]measure.StyledLine) bool {
	for _, line := range lines {
		if hasMeasuredMath(line) {
			return true
		}
	}
	return false
}
