package measure

import (
	"strings"

	emath "github.com/gosuda/elegant-mermaid/internal/math"
)

const formulaPlaceholder = '\uE000'

type formulaMetrics struct{}

func formulaWeight(weight emath.Weight) Weight {
	if weight == emath.WeightBold {
		return WeightSemiBold
	}
	return WeightRegular
}

func (formulaMetrics) Upem(weight emath.Weight) (int32, error) {
	return Upem(formulaWeight(weight))
}

func (formulaMetrics) Advance(weight emath.Weight, codepoint rune) (int32, error) {
	return Advance(formulaWeight(weight), codepoint)
}

func (p *styledScanner) appendMath(literal string) {
	p.appendText(literal, styledToken{isMath: true, formula: literal[2 : len(literal)-2]})
}

func layoutFormulas(tokens []styledToken, metric Metric) error {
	if metric.Profile == ProfileCell {
		return nil
	}
	for i := range tokens {
		if !tokens[i].isMath {
			continue
		}
		box, err := formulaBox(tokens[i].formula, metric)
		if err != nil {
			return err
		}
		tokens[i].box = box
	}
	return nil
}

func formulaBox(formula string, metric Metric) (*emath.Box, error) {
	parsed := emath.Parse(formula)
	if len(parsed.Diagnostics) != 0 {
		return nil, nil
	}
	box, err := emath.Layout(parsed.Expression, formulaMetrics{}, metric.SizePx)
	if err != nil {
		return nil, err
	}
	return &box, nil
}

func (t styledToken) rendered() string {
	if t.box != nil {
		return string(formulaPlaceholder)
	}
	return t.text
}

func (t styledToken) advanceText(rendered string) string {
	if t.box != nil {
		return ""
	}
	return rendered
}

func (t styledToken) formulaWidth() int64 {
	if t.box != nil {
		return int64(t.box.W)
	}
	return 0
}

func (t styledToken) run(metric Metric, lo, hi int) (StyledRun, error) {
	if t.box != nil {
		return StyledRun{Text: t.text, Width: t.box.W, Math: t.box}, nil
	}
	text := t.text[lo:hi]
	width, err := styledMetric(metric, t).TextWidth(text)
	return StyledRun{Text: text, Bold: t.bold, Italic: t.italic, Width: width}, err
}

func runsText(runs []StyledRun) string {
	var text strings.Builder
	for _, run := range runs {
		text.WriteString(run.Text)
	}
	return text.String()
}
