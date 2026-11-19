package lanes

import "github.com/gosuda/elegant-mermaid/internal/scene"

type timelineConstants struct {
	cardWidth, columnGap, eventGap, sectionGap, cardPadding, leftMargin int64
	cornerRadius, canvasMargin                                          int64
}

func loadTimelineConstants(profile scene.Profile) (timelineConstants, error) {
	var c timelineConstants
	required := []struct {
		name string
		into *int64
	}{
		{"timeline.card_width", &c.cardWidth}, {"timeline.column_gap", &c.columnGap},
		{"timeline.event_gap", &c.eventGap}, {"timeline.section_gap", &c.sectionGap},
		{"timeline.card_padding", &c.cardPadding}, {"timeline.left_margin", &c.leftMargin},
		{"corner_radius", &c.cornerRadius}, {"canvas_margin", &c.canvasMargin},
	}
	for _, row := range required {
		value, ok := constant(profile, row.name)
		if !ok {
			return timelineConstants{}, ErrConstants
		}
		*row.into = value
	}
	return c, nil
}
