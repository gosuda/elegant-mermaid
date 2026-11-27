package scenelink

import (
	"sort"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const (
	EmojiFile          = "fonts/NotoEmoji-Regular.ttf"
	SansRegularFile    = "fonts/NotoSans-Regular.ttf"
	SansSemiBoldFile   = "fonts/NotoSans-SemiBold.ttf"
	SymbolsRegularFile = "fonts/NotoSansSymbols-Regular.ttf"
	SymbolsSemiFile    = "fonts/NotoSansSymbols-SemiBold.ttf"
	Symbols2File       = "fonts/NotoSansSymbols2-Regular.ttf"
	MathFile           = "fonts/NotoSansMath-Regular.ttf"
	CJKRegularFile     = "fonts/NotoSansCJKsc-Regular.ttf"
	CJKSemiBoldFile    = "fonts/NotoSansCJKsc-SemiBold.ttf"
	CopticFile         = "fonts/NotoSansCoptic-Regular.ttf"
)

func FallbackFiles(w int) []string {
	if w == 1 {
		return []string{EmojiFile, SansSemiBoldFile, SymbolsSemiFile, Symbols2File, MathFile, CJKSemiBoldFile, CopticFile}
	}
	return []string{EmojiFile, SansRegularFile, SymbolsRegularFile, Symbols2File, MathFile, CJKRegularFile, CopticFile}
}

func (f Font) hasInter(cp rune) (Glyph, bool) {
	i := sort.Search(len(f.Glyphs), func(i int) bool { return f.Glyphs[i].Rune >= cp })
	if i < len(f.Glyphs) && f.Glyphs[i].Rune == cp {
		return f.Glyphs[i], true
	}
	return Glyph{}, false
}

func isPresentation(cp rune) bool {
	v := uint32(cp)
	i := sort.Search(len(gen.EmojiPresentation), func(i int) bool { return gen.EmojiPresentation[i].Hi >= v })
	return i < len(gen.EmojiPresentation) && gen.EmojiPresentation[i].Lo <= v && gen.EmojiPresentation[i].Value == 1
}

func skipVS16(s []rune, pos int) int {
	for pos < len(s) && s[pos] == 0xFE0F {
		pos++
	}
	return pos
}

func matchScalars(scalars []uint32, s []rune, i int) (int, bool) {
	pos := i
	for _, want := range scalars {
		pos = skipVS16(s, pos)
		if pos >= len(s) {
			return 0, false
		}
		if uint32(s[pos]) != want {
			return 0, false
		}
		pos++
	}
	return skipVS16(s, pos), true
}

func findSequence(s []rune, i int) (int, uint16, bool) {
	if s[i] == 0xFE0F {
		return 0, 0, false
	}
	best := 0
	var gid uint16
	found := false
	for _, row := range gen.EmojiSequences {
		if len(row.Scalars) < 2 {
			continue
		}
		end, ok := matchScalars(row.Scalars, s, i)
		if !ok {
			continue
		}
		k := end - i
		if k < 2 || k > len(s)-i {
			continue
		}
		if k <= best {
			continue
		}
		best = k
		gid = row.Glyph
		found = true
	}
	return best, gid, found
}

func sceneRound(units int64, size int32, upem int64) int64 {
	return round(units*int64(size)*64, upem)
}

func fittedOrigin(x0, slot, nat int64) int64 {
	if nat < slot {
		return x0 + geom.FloorDiv(slot-nat, 2)
	}
	return x0
}
