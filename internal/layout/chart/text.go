package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type textStyle struct {
	profile scene.Profile
	role    measure.Role
	size    int32
}

func (s textStyle) lineHeight() int64 {
	if s.profile == scene.ProfileCell {
		return 1
	}
	return measure.RoundHalfUp(int64(s.size)*64*int64(s.role.LineHeightPx()), int64(s.role.SizePx()))
}

func (s textStyle) metric() measure.Metric {
	if s.profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.Metric{Profile: measure.ProfileVector, SizePx: s.size, Weight: s.role.Weight()}
}

func (s textStyle) measure(text string) (textBox, error) {
	lines, err := measure.StyledLines(text, geom.I32Max, s.metric())
	if err != nil {
		return textBox{}, err
	}
	var widest int64
	for _, line := range lines {
		widest = max(widest, int64(line.Width))
	}
	return textBox{lines: lines, w: widest, h: int64(len(lines)) * s.lineHeight()}, nil
}

func (t textBox) plain() []string {
	out := make([]string, len(t.lines))
	for i, line := range t.lines {
		out[i] = line.Text
	}
	return out
}

func (t textBox) runs() [][]scene.Run {
	out := make([][]scene.Run, len(t.lines))
	for i, line := range t.lines {
		for _, run := range line.Runs {
			out[i] = append(out[i], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return out
}

func (s textStyle) item(box textBox, at rect, align scene.Align) (*scene.Text, error) {
	g, err := at.geom()
	if err != nil {
		return nil, err
	}
	return &scene.Text{Rect: g, Role: textRole(s.role), Size: s.size, Align: align, Style: "text", Lines: box.runs()}, nil
}
