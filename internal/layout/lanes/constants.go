package lanes

import (
	"errors"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var ErrConstants = errors.New("lanes layout: missing constant")

type gitgraphConstants struct {
	commitStep, lanePitch, rotationExtra, labelOffset, commitRadius int64
	tagOffset, tagPad, labelGap, branchPadX, branchPadY             int64
	cornerRadius, canvasMargin                                      int64
}

func constant(profile scene.Profile, name string) (int64, bool) {
	key := profile.String() + "." + name
	for _, c := range gen.LayoutConst {
		if c.Name == key {
			return int64(c.Value), true
		}
	}
	return 0, false
}

func loadGitgraphConstants(profile scene.Profile) (gitgraphConstants, error) {
	var c gitgraphConstants
	required := []struct {
		name string
		into *int64
	}{
		{"gitgraph.commit_step", &c.commitStep}, {"gitgraph.lane_pitch", &c.lanePitch},
		{"gitgraph.label_rotation_extra", &c.rotationExtra}, {"gitgraph.label_offset", &c.labelOffset},
		{"gitgraph.commit_radius", &c.commitRadius}, {"gitgraph.tag_offset", &c.tagOffset},
		{"gitgraph.tag_pad", &c.tagPad}, {"gitgraph.label_gap", &c.labelGap},
		{"gitgraph.branch_pad_x", &c.branchPadX}, {"gitgraph.branch_pad_y", &c.branchPadY},
		{"corner_radius", &c.cornerRadius}, {"canvas_margin", &c.canvasMargin},
	}
	for _, row := range required {
		value, ok := constant(profile, row.name)
		if !ok {
			return gitgraphConstants{}, ErrConstants
		}
		*row.into = value
	}
	return c, nil
}
