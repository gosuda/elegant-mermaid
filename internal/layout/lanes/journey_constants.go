package lanes

import "github.com/gosuda/elegant-mermaid/internal/scene"

type journeyConstants struct {
	taskWidth, taskHeight, columnGap, scoreStep, scoreMin, scoreMax int64
	bandHeight, faceRadius, padX, padY, cornerRadius, canvasMargin  int64
}

func loadJourneyConstants(profile scene.Profile, in JourneyInput) (journeyConstants, error) {
	var c journeyConstants
	var padX, padY, border int64
	required := []struct {
		name string
		into *int64
	}{
		{"journey.task_width", &c.taskWidth}, {"journey.task_height", &c.taskHeight},
		{"journey.column_gap", &c.columnGap}, {"journey.score_step", &c.scoreStep},
		{"journey.score_min", &c.scoreMin}, {"journey.score_max", &c.scoreMax},
		{"journey.band_height", &c.bandHeight}, {"journey.face_radius", &c.faceRadius},
		{"node_pad_x", &padX}, {"node_pad_y", &padY}, {"node_border", &border},
		{"corner_radius", &c.cornerRadius}, {"canvas_margin", &c.canvasMargin},
	}
	for _, row := range required {
		value, ok := constant(profile, row.name)
		if !ok {
			return journeyConstants{}, ErrConstants
		}
		*row.into = value
	}
	c.padX, c.padY = padX+border, padY+border
	for _, override := range []struct {
		value int64
		into  *int64
	}{{in.TaskWidth, &c.taskWidth}, {in.TaskHeight, &c.taskHeight}, {in.BandHeight, &c.bandHeight}, {in.ColumnGap, &c.columnGap}} {
		if override.value > 0 {
			*override.into = override.value
		}
	}
	return c, nil
}
