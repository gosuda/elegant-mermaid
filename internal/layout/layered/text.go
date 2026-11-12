package layered

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func wrapLabel(text string, o scene.Options) ([]measure.Line, error) {
	metric := metricFor(o.Profile)
	maxWidth := int32(0)
	if o.Profile == scene.ProfileCell {
		text = terminalText(text)
		maxWidth = o.MaxWidth
	}
	return measure.Wrap(text, measure.WrapTarget(metric.Profile, 0, maxWidth), metric)
}
func terminalText(text string) string {
	return strings.Map(func(r rune) rune {
		if r < 0x20 || r >= 0x7f && r <= 0x9f {
			return '\ufffd'
		}
		return r
	}, text)
}

func measuredTitle(lines []measure.Line, o scene.Options) (geom.Size, error) {
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
