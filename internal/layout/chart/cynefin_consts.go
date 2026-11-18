package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type cynefinConsts struct {
	width, height, confusion, amplitude, waves int64
	seed                                       uint32
	pad, nameGap, itemPadX, itemPadY           int64
	itemGap, boxPad, labelGap, corner          int64
	edge                                       int64
}

func loadCynefinConsts(profile scene.Profile, m *chartmodel.Cynefin) (cynefinConsts, error) {
	var c cynefinConsts
	var seed, permille int64
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"cynefin.width", &c.width}, {"cynefin.height", &c.height}, {"cynefin.confusion_permille", &c.confusion},
		{"cynefin.amplitude_permille", &permille}, {"cynefin.wave_segments", &c.waves}, {"cynefin.default_seed", &seed},
		{"cynefin.pad", &c.pad}, {"cynefin.name_gap", &c.nameGap}, {"cynefin.item_pad_x", &c.itemPadX},
		{"cynefin.item_pad_y", &c.itemPadY}, {"cynefin.item_gap", &c.itemGap}, {"cynefin.box_pad", &c.boxPad},
		{"cynefin.label_gap", &c.labelGap}, {"corner_radius", &c.corner},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return cynefinConsts{}, err
		}
		*row.into = value
	}
	if profile == scene.ProfileCell {
		c.edge = 1
	}
	if n, ok := m.Integer("width"); ok {
		c.width = canvasSide(profile, n, 64, 8)
	}
	if n, ok := m.Integer("height"); ok {
		c.height = canvasSide(profile, n, 64, 16)
	}
	c.amplitude = geom.FloorDiv(c.width*permille, 1000)
	if n, ok := m.Integer("boundaryAmplitude"); ok {
		c.amplitude = canvasSide(profile, n, 64, 8)
	}
	if n, ok := m.Integer("seed"); ok {
		seed = n
	}
	c.seed = uint32(seed)
	return c, nil
}
