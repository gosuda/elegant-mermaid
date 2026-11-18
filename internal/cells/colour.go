package cells

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

type Token = theme.Token

const (
	TokenBG Token = iota
	TokenFG
	TokenLine
	TokenAccent
	TokenMuted
	TokenSurface
	TokenBorder
	TokenSeries0
	TokenSeries1
	TokenSeries2
	TokenSeries3
	TokenSeries4
	TokenSeries5
	TokenSeries6
	TokenSeries7
	TokenSeries8
	TokenSeries9
	TokenSeries10
	TokenSeries11
	TokenError
	TokenWarning
	TokenSuccess
)

type ColorMode uint8

const (
	ColorNone ColorMode = iota
	ColorANSI16
	ColorANSI256
	ColorTruecolor
)

type (
	RGB          = theme.Colour
	ColourLookup func(Token) RGB
)

func distance(a, b RGB) int {
	r := int(a.R) - int(b.R)
	g := int(a.G) - int(b.G)
	z := int(a.B) - int(b.B)
	return r*r + g*g + z*z
}

func cube(v uint8) int {
	if v < 48 {
		return 0
	}
	if v < 114 {
		return 1
	}
	return (int(v) - 35) / 40
}

func ANSI256(c RGB) int {
	levels := [6]uint8{0, 95, 135, 175, 215, 255}
	r, g, b := cube(c.R), cube(c.G), cube(c.B)
	index := 16 + 36*r + 6*g + b
	cc := RGB{R: levels[r], G: levels[g], B: levels[b]}
	if c == cc {
		return index
	}
	avg := (int64(c.R) + int64(c.G) + int64(c.B)) / 3
	gi := 23
	if avg <= 238 {
		gi = max(0, int(geom.FloorDiv(avg-3, 10)))
	}
	grey := uint8(8 + 10*gi)
	if distance(c, RGB{R: grey, G: grey, B: grey}) < distance(c, cc) {
		return 232 + gi
	}
	return index
}

func ANSI16(c RGB) int {
	raw := [16][3]uint8{{0, 0, 0}, {205, 0, 0}, {0, 205, 0}, {205, 205, 0}, {0, 0, 238}, {205, 0, 205}, {0, 205, 205}, {229, 229, 229}, {127, 127, 127}, {255, 0, 0}, {0, 255, 0}, {255, 255, 0}, {92, 92, 255}, {255, 0, 255}, {0, 255, 255}, {255, 255, 255}}
	var palette [16]RGB
	for i, c := range raw {
		palette[i] = RGB{R: c[0], G: c[1], B: c[2]}
	}
	best := 0
	for i := 1; i < len(palette); i++ {
		if distance(c, palette[i]) < distance(c, palette[best]) {
			best = i
		}
	}
	return best
}

func SGR(mode ColorMode, token Token, lookup ColourLookup) string {
	if token <= TokenFG {
		return "\x1b[39m"
	}
	c := lookup(token)
	switch mode {
	case ColorTruecolor:
		return "\x1b[38;2;" + strconv.Itoa(int(c.R)) + ";" + strconv.Itoa(int(c.G)) + ";" + strconv.Itoa(int(c.B)) + "m"
	case ColorANSI256:
		return "\x1b[38;5;" + strconv.Itoa(ANSI256(c)) + "m"
	case ColorANSI16:
		i := ANSI16(c)
		if i < 8 {
			return "\x1b[" + strconv.Itoa(30+i) + "m"
		}
		return "\x1b[" + strconv.Itoa(90+i-8) + "m"
	default:
		return ""
	}
}
