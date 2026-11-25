package cells

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

func textInk(p *scene.Text, t theme.Theme) Token {
	switch p.Style {
	case "text-muted":
		return TokenMuted
	case "text-inverse":
		return TokenBG
	case "text-on-series":
		if t.SeriesText(p.Series) == theme.TextBackground {
			return TokenBG
		}
	}
	return TokenFG
}

func lineStart(align scene.Align, x, w, lineW int64) int64 {
	switch align {
	case scene.AlignMiddle:
		return x + geom.FloorDiv(w-lineW, 2)
	case scene.AlignEnd:
		return x + w - lineW
	default:
		return x
	}
}

func (c *Canvas) placeAll(labels []*scene.Text, t theme.Theme) (int, error) {
	refused := 0
	for _, p := range labels {
		lines, err := PositionedLines(p)
		if err != nil {
			return 0, err
		}
		for _, line := range lines {
			refused += c.placeClusters(line.Text, int(line.Rect.X), int(line.Rect.Y), textInk(p, t))
		}
	}
	return refused, nil
}

func (c *Canvas) placeClusters(text string, col, row int, ink Token) int {
	refused := 0
	for _, cluster := range measure.Segment(text) {
		w := int(measure.ClusterWidth(cluster))
		if !c.PutLabel(col, row, cluster.Text, w, ink) {
			refused++
		}
		col += w
	}
	return refused
}
