package svg

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

func validateText(opts Options) error {
	switch opts.Text {
	case TextFont:
		return nil
	case TextPaths:
		if opts.Outlines == nil || opts.Outlines[0].UnitsPerEm <= 0 || opts.Outlines[1].UnitsPerEm <= 0 {
			return &ConfigError{"text paths require glyph outlines"}
		}
		return nil
	default:
		return &ConfigError{"invalid text mode"}
	}
}

func (r *renderer) textPaths(t *scene.Text) (string, error) {
	if _, e := styleRow(t.Style); e != nil {
		return "", e
	}
	var d strings.Builder
	for k, line := range t.Lines {
		x := scenelink.TextLeft(t, r.outlines.LineWidth(t, line))
		for g, at := range r.outlines.Glyphs(t, line, x, scenelink.Baseline(t, k)) {
			appendGlyph(&d, g, at)
		}
	}
	if d.Len() == 0 {
		return "", nil
	}
	key := class(t.Style, t.Series)
	r.used[key] = true
	return "<path class='emd-s-" + key + "' d='" + d.String() + "'/>\n", nil
}

func appendGlyph(b *strings.Builder, g scenelink.Glyph, at scenelink.Placement) {
	open := false
	for _, c := range g.Commands {
		if c.Op == scenelink.OpMoveTo && open {
			b.WriteByte('Z')
		}
		b.WriteByte(commandLetter(c.Op))
		for i := range commandPoints(c.Op) {
			x, y := at.Point(c.Points[i][0], c.Points[i][1])
			if i > 0 {
				b.WriteByte(' ')
			}
			b.WriteString(number(x) + " " + number(y))
		}
		open = true
	}
	if open {
		b.WriteByte('Z')
	}
}

func commandLetter(op uint8) byte {
	switch op {
	case scenelink.OpMoveTo:
		return 'M'
	case scenelink.OpLineTo:
		return 'L'
	case scenelink.OpQuadTo:
		return 'Q'
	default:
		return 'C'
	}
}

func commandPoints(op uint8) int {
	switch op {
	case scenelink.OpMoveTo, scenelink.OpLineTo:
		return 1
	case scenelink.OpQuadTo:
		return 2
	default:
		return 3
	}
}
