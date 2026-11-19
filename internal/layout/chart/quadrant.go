package chart

import (
	"context"
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	unitsPerPx = 64
	cellPxX    = 8
	cellPxY    = 16
	minPlot    = 2
	cellInset  = 1
)

type quadConsts struct {
	width, height, padX, padY, titleBand, xBand, yBand int64
	titlePadPx, titleFontPx, xPadPx, xFontPx           int64
	yPadPx, yFontPx, radiusX, radiusY, textPad         int64
	labelFontPx, pointFontPx, topPad, edge             int64
}

func (c *quadConsts) unitsX(profile scene.Profile, px int64) int64 {
	return canvasSide(profile, px, unitsPerPx, cellPxX)
}

func (c *quadConsts) unitsY(profile scene.Profile, px int64) int64 {
	return canvasSide(profile, px, unitsPerPx, cellPxY)
}

func loadQuadConsts(profile scene.Profile, config map[string]int64) (quadConsts, error) {
	var c quadConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"quadrant.width", &c.width}, {"quadrant.height", &c.height}, {"quadrant.padding", &c.padX},
		{"quadrant.axis_band_x", &c.yBand}, {"quadrant.axis_band_y", &c.xBand}, {"quadrant.title_band", &c.titleBand},
		{"quadrant.point_radius", &c.radiusX}, {"quadrant.point_text_pad", &c.textPad},
		{"quadrant.axis_label_padding_px", &c.xPadPx}, {"quadrant.axis_font_px", &c.xFontPx},
		{"quadrant.title_padding_px", &c.titlePadPx}, {"quadrant.title_font_px", &c.titleFontPx},
		{"quadrant.label_font_px", &c.labelFontPx}, {"quadrant.point_font_px", &c.pointFontPx}, {"quadrant.text_top_pad", &c.topPad},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return quadConsts{}, err
		}
		*row.into = value
	}
	c.padY, c.radiusY = c.padX, c.radiusX
	c.yPadPx, c.yFontPx = c.xPadPx, c.xFontPx
	if profile == scene.ProfileCell {
		c.edge = cellInset
	}
	c.applyConfig(profile, config)
	return c, nil
}

func (c *quadConsts) applyConfig(profile scene.Profile, config map[string]int64) {
	c.applyGeometry(profile, config)
	for _, b := range []struct {
		padKey, fontKey string
		pad, font, band *int64
		horizontal      bool
	}{
		{"titlePadding", "titleFontSize", &c.titlePadPx, &c.titleFontPx, &c.titleBand, false},
		{"xAxisLabelPadding", "xAxisLabelFontSize", &c.xPadPx, &c.xFontPx, &c.xBand, false},
		{"yAxisLabelPadding", "yAxisLabelFontSize", &c.yPadPx, &c.yFontPx, &c.yBand, true},
	} {
		padN, hasPad := config[b.padKey]
		fontN, hasFont := config[b.fontKey]
		if !hasPad && !hasFont {
			continue
		}
		if hasPad {
			*b.pad = padN
		}
		if hasFont {
			*b.font = fontN
		}
		span := 2**b.pad + *b.font
		if b.horizontal {
			*b.band = c.unitsX(profile, span)
		} else {
			*b.band = c.unitsY(profile, span)
		}
	}
}

func (c *quadConsts) applyGeometry(profile scene.Profile, config map[string]int64) {
	if n, ok := config["chartWidth"]; ok {
		c.width = c.unitsX(profile, n)
	}
	if n, ok := config["chartHeight"]; ok {
		c.height = c.unitsY(profile, n)
	}
	if n, ok := config["quadrantPadding"]; ok {
		c.padX, c.padY = c.unitsX(profile, n), c.unitsY(profile, n)
	}
	if n, ok := config["pointRadius"]; ok {
		c.radiusX, c.radiusY = c.unitsX(profile, n), c.unitsY(profile, n)
	}
	if n, ok := config["pointTextPadding"]; ok {
		c.textPad = c.unitsX(profile, n)
	}
}

type quadPlan struct {
	q          *Quadrant
	o          scene.Options
	c          quadConsts
	cell       bool
	boxes      []quadBox
	specs      []quadLabel
	texts      []textBox
	width      int64
	height     int64
	plot       rect
	inner      [tileCount]rect
	tiles      [tileCount]rect
	centres    []spot
	radii      []spot
	pointBoxes []rect
	taken      []rect
	boxRects   []geom.Rect
	labelRects []geom.Rect
	labelLines [][]string
	aligns     []scene.Align
	laidOut    bool
}

type spot struct{ x, y int64 }

func newQuadPlan(q *Quadrant, o scene.Options) (*quadPlan, error) {
	c, err := loadQuadConsts(o.Profile, q.Config)
	if err != nil {
		return nil, err
	}
	for _, p := range q.Points {
		if p.X < 0 || p.X > scale || p.Y < 0 || p.Y > scale {
			return nil, fmt.Errorf("quadrant layout: point outside the unit square: %w", errDomain)
		}
	}
	return &quadPlan{q: q, o: o, c: c, cell: o.Profile == scene.ProfileCell, boxes: quadrantBoxes(q), specs: quadrantLabels(q)}, nil
}

func LayoutQuadrant(ctx context.Context, q *Quadrant, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	if err := ctx.Err(); err != nil {
		return scene.Scene{}, nil, err
	}
	p, err := newQuadPlan(q, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.arrange(); err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.place(); err != nil {
		return scene.Scene{}, nil, err
	}
	w, err := i32(p.width)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	h, err := i32(p.height)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: quadrantKind, Options: o, Canvas: geom.Size{W: w, H: h}, Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}
	dump.Options.Direction = scene.DirectionTB
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}

func (p *quadPlan) lineHeight(role measure.Role, size int32) int64 {
	if p.cell {
		return 1
	}
	return measure.RoundHalfUp(int64(size)*unitsPerPx*int64(role.LineHeightPx()), int64(role.SizePx()))
}

func (p *quadPlan) metric(role measure.Role, size int32) measure.Metric {
	if p.cell {
		return measure.CellMetric()
	}
	return measure.Metric{Profile: measure.ProfileVector, SizePx: size, Weight: role.Weight()}
}

func (p *quadPlan) styleOf(s quadLabel) (measure.Role, int32) {
	switch s.kind {
	case quadTitle:
		return measure.RoleTitle, int32(p.c.titleFontPx)
	case quadXLeft, quadXRight:
		return measure.RoleLabel, int32(p.c.xFontPx)
	case quadYBottom, quadYTop:
		return measure.RoleLabel, int32(p.c.yFontPx)
	case quadTileLabel:
		return measure.RoleLabel, int32(p.c.labelFontPx)
	}
	return measure.RoleBody, int32(p.c.pointFontPx)
}

func (p *quadPlan) measureAt(i int, target int64) (textBox, error) {
	role, size := p.styleOf(p.specs[i])
	wrap := int32(geom.I32Max)
	if target > 0 && target < int64(geom.I32Max) {
		wrap = int32(target)
	}
	lines, err := measure.StyledLines(p.specs[i].text, wrap, p.metric(role, size))
	if err != nil {
		return textBox{}, err
	}
	var widest int64
	for _, line := range lines {
		widest = max(widest, int64(line.Width))
	}
	return textBox{lines: lines, w: widest, h: int64(len(lines)) * p.lineHeight(role, size)}, nil
}

func (p *quadPlan) find(kind quadLabelKind) (int, bool) {
	for i, s := range p.specs {
		if s.kind == kind {
			return i, true
		}
	}
	return 0, false
}
