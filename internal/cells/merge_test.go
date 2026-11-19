package cells

import "testing"

func TestMergePermutations(t *testing.T) {
	writes := []Cell{{Mask: 1, Style: StyleDotted, Dots: 1, Ink: TokenLine}, {Mask: 2, Style: StyleRounded, Dots: 16, Symbol: 'x', Ink: TokenAccent}, {Mask: 4, Style: StyleDouble, Dots: 64, Symbol: '?', Ink: TokenBorder}, {Mask: 8, Style: StyleHeavy, Dots: 128, Ink: TokenSeries3}}
	var want Cell
	for _, v := range writes {
		want = MergeCell(want, v)
	}
	s := uint32(1)
	for range 200 {
		for i := len(writes) - 1; i > 0; i-- {
			s ^= s << 13
			s ^= s >> 17
			s ^= s << 5
			j := int(s % uint32(i+1))
			writes[i], writes[j] = writes[j], writes[i]
		}
		var got Cell
		for _, v := range writes {
			got = MergeCell(got, v)
		}
		if got != want {
			t.Fatal(got, want)
		}
	}
}
