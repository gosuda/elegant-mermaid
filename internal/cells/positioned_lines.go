package cells

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

// PositionedLine is one normalized line in cell coordinates. Rect includes
// spaces and has height one, even when the text item's declared height differs.
type PositionedLine struct {
	Text string
	Rect geom.Rect
}

// PositionedLines computes the exact spans used by cell text placement.
// Runs are joined before terminal controls are replaced and graphemes measured.
// Empty lines retain their row; callers reserving occupied cells skip width zero.
func PositionedLines(p *scene.Text) ([]PositionedLine, error) {
	lines := make([]PositionedLine, 0, len(p.Lines))
	for row, runs := range p.Lines {
		text, width, err := cellLine(runs)
		if err != nil {
			return nil, err
		}
		x := lineStart(p.Align, int64(p.Rect.X), int64(p.Rect.W), int64(width))
		point, err := checkedPoint(x, int64(p.Rect.Y)+int64(row))
		if err != nil {
			return nil, err
		}
		lines = append(lines, PositionedLine{Text: text, Rect: geom.Rect{X: point.X, Y: point.Y, W: width, H: 1}})
	}
	return lines, nil
}

func cellLine(runs []scene.Run) (string, int32, error) {
	var joined strings.Builder
	for _, run := range runs {
		joined.WriteString(run.Text)
	}
	text := terminalText(joined.String())
	width, err := measure.CellWidth(text)
	return text, width, err
}
