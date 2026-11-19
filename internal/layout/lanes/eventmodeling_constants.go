package lanes

import "github.com/gosuda/elegant-mermaid/internal/scene"

type eventConstants struct {
	laneMinHeight, lanePadding, laneGap, boxPadding, boxOverlap int64
	boxMinWidth, boxMaxWidth, boxMinHeight, boxMaxHeight        int64
	contentStartX, lineHeight, cornerRadius, canvasMargin       int64
}

func loadEventConstants(profile scene.Profile) (eventConstants, error) {
	var c eventConstants
	required := []struct {
		name string
		into *int64
	}{
		{"eventmodeling.swimlane_min_height", &c.laneMinHeight}, {"eventmodeling.swimlane_padding", &c.lanePadding},
		{"eventmodeling.swimlane_gap", &c.laneGap}, {"eventmodeling.box_padding", &c.boxPadding},
		{"eventmodeling.box_overlap", &c.boxOverlap}, {"eventmodeling.box_min_width", &c.boxMinWidth},
		{"eventmodeling.box_max_width", &c.boxMaxWidth}, {"eventmodeling.box_min_height", &c.boxMinHeight},
		{"eventmodeling.box_max_height", &c.boxMaxHeight}, {"eventmodeling.content_start_x", &c.contentStartX},
		{"line_h", &c.lineHeight}, {"corner_radius", &c.cornerRadius}, {"canvas_margin", &c.canvasMargin},
	}
	for _, row := range required {
		value, ok := constant(profile, row.name)
		if !ok {
			return eventConstants{}, ErrConstants
		}
		*row.into = value
	}
	return c, nil
}

type EventWraps struct {
	Lane  int32
	Frame int32
}

func (c eventConstants) labelInset() int64 { return 2 * c.lanePadding }

func EventModelingWraps(profile scene.Profile) (EventWraps, error) {
	c, err := loadEventConstants(profile)
	if err != nil {
		return EventWraps{}, err
	}
	return EventWraps{Lane: int32(c.contentStartX - 2*c.labelInset()), Frame: int32(c.boxMaxWidth)}, nil
}
