package cells

import (
	"github.com/gosuda/elegant-mermaid/internal/gen"
)

const (
	glyphCharsetUnicode uint8 = 0
	glyphCharsetASCII   uint8 = 1
	glyphStylePlain     uint8 = 0
	glyphStyleDotted    uint8 = 1
	spaceRune                 = 0x0020
	brailleBase               = 0x2800
	asciiBrailleFill          = '#'
)

func Glyph(charset Charset, style Style, mask uint8) rune {
	mask &= 0x0F
	if charset == CharsetASCII {
		return asciiGlyph(style, mask)
	}
	return unicodeGlyph(style, mask)
}

func asciiGlyph(style Style, mask uint8) rune {
	rowStyle := glyphStylePlain
	if style == StyleDotted {
		rowStyle = glyphStyleDotted
	}
	if r, ok := lookupGlyph(glyphCharsetASCII, rowStyle, mask); ok {
		return r
	}
	return spaceRune
}

func unicodeGlyph(style Style, mask uint8) rune {
	rowStyle := uint8(style)
	if style == StyleNone {
		rowStyle = glyphStylePlain
	}
	if r, ok := lookupGlyph(glyphCharsetUnicode, rowStyle, mask); ok {
		return r
	}
	return spaceRune
}

func lookupGlyph(charset, style, mask uint8) (rune, bool) {
	lo, hi := 0, len(gen.GlyphJoin)
	for lo < hi {
		mid := int(uint(lo+hi) >> 1)
		row := gen.GlyphJoin[mid]
		switch {
		case glyphRowLess(row, charset, style, mask):
			lo = mid + 1
		case row.Charset == charset && row.Style == style && row.Mask == mask:
			return rune(row.Rune), true
		default:
			hi = mid
		}
	}
	return 0, false
}

func glyphRowLess(row gen.Glyph, charset, style, mask uint8) bool {
	if row.Charset != charset {
		return row.Charset < charset
	}
	if row.Style != style {
		return row.Style < style
	}
	return row.Mask < mask
}

func Symbol(charset Charset, name string) (rune, bool) {
	lo, hi := 0, len(gen.CellSymbols)
	for lo < hi {
		mid := int(uint(lo+hi) >> 1)
		row := gen.CellSymbols[mid]
		switch {
		case row.Name < name:
			lo = mid + 1
		case row.Name == name:
			return symbolRune(charset, row), true
		default:
			hi = mid
		}
	}
	return 0, false
}

func symbolRune(charset Charset, row gen.Symbol) rune {
	if charset == CharsetASCII {
		return rune(row.Ascii)
	}
	return rune(row.Unicode)
}

func BrailleGlyph(charset Charset, dots uint8) rune {
	if dots == 0 {
		return spaceRune
	}
	if charset == CharsetASCII {
		return asciiBrailleFill
	}
	return brailleBase + rune(dots)
}
