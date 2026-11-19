package math_test

import (
	emmath "github.com/gosuda/elegant-mermaid/internal/math"
	"github.com/gosuda/elegant-mermaid/internal/measure"
)

type interMetrics struct{}

func measureWeight(weight emmath.Weight) measure.Weight {
	if weight == emmath.WeightBold {
		return measure.WeightSemiBold
	}
	return measure.WeightRegular
}

func (interMetrics) Upem(weight emmath.Weight) (int32, error) {
	return measure.Upem(measureWeight(weight))
}

func (interMetrics) Advance(weight emmath.Weight, codepoint rune) (int32, error) {
	return measure.Advance(measureWeight(weight), codepoint)
}

func ceilDiv(a, b int64) int64 {
	return measure.CeilDiv(a, b)
}
