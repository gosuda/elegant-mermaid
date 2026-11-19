package layered

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func wrapLabel(text, kind string, o scene.Options) ([]measure.StyledLine, error) {
	metric := metricFor(o.Profile)
	maxWidth := int32(0)
	if o.Profile == scene.ProfileCell {
		maxWidth = o.MaxWidth
	}
	return measure.StyledLines(text, measure.WrapTarget(metric.Profile, kindWrapWidth(o.Profile, kind), maxWidth), metric)
}

func measuredTitle(lines []measure.StyledLine, o scene.Options) (geom.Size, error) {
	var width int32
	for _, line := range lines {
		width = max(width, line.Width)
	}
	height, err := coordinate(int64(max(1, len(lines))) * int64(constant(o.Profile, "line_h")))
	if err != nil {
		return geom.Size{}, err
	}
	size := geom.Size{W: width, H: height}
	if o.Direction == scene.DirectionLR || o.Direction == scene.DirectionRL {
		size.W, size.H = size.H, size.W
	}
	return size, nil
}
