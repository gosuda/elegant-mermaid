package measure

import (
	"sort"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

const (
	propCR                   uint8 = 1
	propLF                   uint8 = 2
	propControl              uint8 = 3
	propExtend               uint8 = 4
	propZWJ                  uint8 = 5
	propRegionalIndicator    uint8 = 6
	propPrepend              uint8 = 7
	propSpacingMark          uint8 = 8
	propL                    uint8 = 9
	propV                    uint8 = 10
	propT                    uint8 = 11
	propLV                   uint8 = 12
	propLVT                  uint8 = 13
	propExtendedPictographic uint8 = 14
)

const (
	incbLinker    uint8 = 1
	incbConsonant uint8 = 2
	incbExtend    uint8 = 3
)

const (
	presentationSelector rune = 0xFE0F
	combiningKeycap      rune = 0x20E3
)

func graphemeProp(cp rune) uint8 {
	index := sort.Search(len(gen.Graphemes), func(i int) bool {
		return gen.Graphemes[i].Hi >= uint32(cp)
	})
	if index < len(gen.Graphemes) && gen.Graphemes[index].Lo <= uint32(cp) {
		return gen.Graphemes[index].Prop
	}
	return 0
}

func incbProp(cp rune) uint8 {
	index := sort.Search(len(gen.Incb), func(i int) bool {
		return gen.Incb[i].Hi >= uint32(cp)
	})
	if index < len(gen.Incb) && gen.Incb[index].Lo <= uint32(cp) {
		return gen.Incb[index].Prop
	}
	return 0
}

func scalarWidth(cp rune) uint8 {
	index := sort.Search(len(gen.UnicodeWidth), func(i int) bool {
		return gen.UnicodeWidth[i].Hi >= uint32(cp)
	})
	if index < len(gen.UnicodeWidth) && gen.UnicodeWidth[index].Lo <= uint32(cp) {
		return gen.UnicodeWidth[index].Value
	}
	return 1
}

func isIdeographic(cp rune) bool {
	index := sort.Search(len(gen.Ideographic), func(i int) bool {
		return gen.Ideographic[i].Hi >= uint32(cp)
	})
	return index < len(gen.Ideographic) && gen.Ideographic[index].Lo <= uint32(cp)
}

func advanceUnits(weight uint8, cp rune) (uint16, bool) {
	key := advanceKey(weight, cp)
	index := sort.Search(len(gen.Advances), func(i int) bool {
		row := gen.Advances[i]
		return advanceKey(row.Weight, rune(row.CP)) >= key
	})
	if index < len(gen.Advances) {
		row := gen.Advances[index]
		if advanceKey(row.Weight, rune(row.CP)) == key {
			return row.Units, true
		}
	}
	return 0, false
}

func advanceKey(weight uint8, cp rune) uint64 {
	return uint64(weight)<<32 | uint64(uint32(cp))
}
