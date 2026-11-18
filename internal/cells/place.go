package cells

import (
	"strings"

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

func lineStart(align scene.Align, x, w, lineW int) int {
	switch align {
	case scene.AlignMiddle:
		return x + int(geom.FloorDiv(int64(w-lineW), 2))
	case scene.AlignEnd:
		return x + w - lineW
	default:
		return x
	}
}

func (c *Canvas) placeAll(labels []*scene.Text, t theme.Theme) (int, error) {
	refused := 0
	for _, p := range labels {
		for k, runs := range p.Lines {
			var b strings.Builder
			for _, run := range runs {
				b.WriteString(run.Text)
			}
			n, err := c.placeLine(p, b.String(), k, textInk(p, t))
			if err != nil {
				return 0, err
			}
			refused += n
		}
	}
	return refused, nil
}

func (c *Canvas) placeLine(p *scene.Text, text string, row int, ink Token) (int, error) {
	text = terminalText(text)
	width, err := measure.CellWidth(text)
	if err != nil {
		return 0, err
	}
	col := lineStart(p.Align, int(p.Rect.X), int(p.Rect.W), int(width))
	return c.placeClusters(text, col, int(p.Rect.Y)+row, ink), nil
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
