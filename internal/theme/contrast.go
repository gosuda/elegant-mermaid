package theme

import "github.com/gosuda/elegant-mermaid/internal/gen"

func linearSum(c Colour) int64 {
	return 2126*int64(gen.Lin16[c.R]) + 7152*int64(gen.Lin16[c.G]) + 722*int64(gen.Lin16[c.B])
}

func Luminance(c Colour) int64 { return linearSum(c) / 10000 }
func IsDark(c Colour) bool     { return linearSum(c) < 327675000 }
func Contrast(a, b Colour, threshold10 int32) bool {
	hi, lo := Luminance(a), Luminance(b)
	return 10*(max(hi, lo)+3277) >= int64(threshold10)*(min(hi, lo)+3277)
}
