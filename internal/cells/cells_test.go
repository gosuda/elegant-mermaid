package cells

import (
	"os"
	"reflect"
	"regexp"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func canvas(t *testing.T, w, h int) *Canvas {
	t.Helper()
	c, e := New(w, h)
	if e != nil {
		t.Fatal(e)
	}
	return c
}

func rectangle(c *Canvas, s Style) {
	c.HSegment(0, 4, 0, s)
	c.HSegment(0, 4, 2, s)
	c.VSegment(0, 0, 2, s)
	c.VSegment(4, 0, 2, s)
}

func TestRectangles(t *testing.T) {
	rows := []struct {
		s    Style
		u, a string
	}{{StyleLight, "┌───┐\n│   │\n└───┘\n", "+---+\n|   |\n+---+\n"}, {StyleRounded, "╭───╮\n│   │\n╰───╯\n", "+---+\n|   |\n+---+\n"}, {StyleHeavy, "┏━━━┓\n┃   ┃\n┗━━━┛\n", "+---+\n|   |\n+---+\n"}, {StyleDouble, "╔═══╗\n║   ║\n╚═══╝\n", "+---+\n|   |\n+---+\n"}, {StyleDotted, "┌┄┄┄┐\n┆   ┆\n└┄┄┄┘\n", "+...+\n:   :\n+...+\n"}}
	for _, v := range rows {
		c := canvas(t, 5, 3)
		rectangle(c, v.s)
		if string(c.Serialise(CharsetUnicode, ColorNone, nil)) != v.u || string(c.Serialise(CharsetASCII, ColorNone, nil)) != v.a {
			t.Fatal(v.s)
		}
	}
}

func TestMasks(t *testing.T) {
	want := []string{" ╵╶└╷│┌├╴┘─┴┐┤┬┼", " ╹╺┗╻┃┏┣╸┛━┻┓┫┳╋", " ╵╶╚╷║╔╠╴╝═╩╗╣╦╬", " ╵╶╰╷│╭├╴╯─┴╮┤┬┼", " ╵╶└╷┆┌├╴┘┄┴┐┤┬┼"}
	styles := []Style{StyleLight, StyleHeavy, StyleDouble, StyleRounded, StyleDotted}
	for i, s := range styles {
		for m, r := range []rune(want[i]) {
			if Glyph(CharsetUnicode, s, uint8(m)) != r {
				t.Fatal(s, m)
			}
		}
	}
}

func TestLabelsAndJunctions(t *testing.T) {
	c := canvas(t, 5, 3)
	rectangle(c, StyleLight)
	if !c.PutLabel(1, 1, "界", 2, TokenFG) || c.PutLabel(0, 1, "x", 1, TokenFG) {
		t.Fatal("label guard")
	}
	if got := string(c.Serialise(CharsetASCII, ColorNone, nil)); got != "+---+\n|界 |\n+---+\n" {
		t.Fatal(got)
	}
	c = canvas(t, 5, 3)
	c.HSegment(0, 4, 1, StyleLight)
	c.VSegment(2, 0, 2, StyleLight)
	v, _ := c.Cell(2, 1)
	if Glyph(CharsetUnicode, v.Style, v.Mask) != '┼' {
		t.Fatal(v)
	}
	c = canvas(t, 5, 3)
	c.HSegment(0, 4, 1, StyleLight)
	c.VSegment(2, 0, 1, StyleLight)
	v, _ = c.Cell(2, 1)
	if Glyph(CharsetUnicode, v.Style, v.Mask) != '┴' {
		t.Fatal(v)
	}
}

func TestMergePermutation(t *testing.T) {
	s := uint32(1)
	for range 2000 {
		s ^= s << 13
		s ^= s >> 17
		s ^= s << 5
		a := Cell{Mask: uint8(s) & 15, Style: Style(s % 6), Dots: uint8(s >> 8), Symbol: rune(s % 1000), Ink: Token(s % 22)}
		b := Cell{Mask: uint8(s>>4) & 15, Style: Style(s % 5), Dots: uint8(s >> 16), Symbol: rune(s % 2000), Ink: Token(s % 21)}
		if MergeCell(a, b) != MergeCell(b, a) || MergeCell(a, a) != a || MergeCell(MergeCell(a, b), a) != MergeCell(a, b) {
			t.Fatal(s)
		}
	}
}

func dots(c *Canvas) []geom.Point {
	var out []geom.Point
	for y := range c.H * 4 {
		for x := range c.W * 2 {
			v, _ := c.Cell(x/2, y/4)
			if v.Dots&DotBit(x, y) != 0 {
				out = append(out, geom.Point{X: int32(x), Y: int32(y)})
			}
		}
	}
	return out
}

func TestBrailleStroke(t *testing.T) {
	want := []geom.Point{{X: 0, Y: 0}, {X: 1, Y: 0}, {X: 2, Y: 1}, {X: 3, Y: 1}, {X: 4, Y: 2}, {X: 5, Y: 2}, {X: 6, Y: 3}, {X: 7, Y: 3}}
	for _, p := range [][2]geom.Point{{{X: 0, Y: 0}, {X: 7, Y: 3}}, {{X: 7, Y: 3}, {X: 0, Y: 0}}} {
		c := canvas(t, 4, 1)
		if err := c.StrokeDots(p[0], p[1], TokenLine); err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(dots(c), want) {
			t.Fatal(dots(c))
		}
	}
	for i := range 256 {
		r := BrailleGlyph(CharsetUnicode, uint8(i))
		if i == 0 {
			if r != ' ' {
				t.Fatal(r)
			}
		} else if r != rune(0x2800+i) {
			t.Fatal(i)
		}
	}
}

func TestVertices(t *testing.T) {
	p, e := Ellipse(geom.Point{}, 10, 20)
	if e != nil || len(p) != 64 || p[0] != (geom.Point{X: 10}) || p[16] != (geom.Point{Y: -20}) {
		t.Fatal(p, e)
	}
}

func TestArcVertices(t *testing.T) {
	p, e := Arc(geom.Point{}, 10, 0, 16384)
	if e != nil || len(p) != 17 || p[0] != (geom.Point{X: 10}) || p[16] != (geom.Point{Y: 10}) {
		t.Fatal(p, e)
	}
}

func TestCubicVertices(t *testing.T) {
	p, e := Cubic([4]geom.Point{{}, {X: 16}, {X: 16, Y: 16}, {Y: 16}})
	if e != nil || len(p) != 17 || p[16] != (geom.Point{Y: 16}) {
		t.Fatal(p, e)
	}
}

func TestTextColour(t *testing.T) {
	c := canvas(t, 8, 1)
	c.AttachInk(0, 0, BitN|BitS, StyleLight, TokenBorder)
	c.AttachInk(7, 0, BitN|BitS, StyleLight, TokenBorder)
	c.PutLabel(3, 0, "H", 1, TokenFG)
	c.PutLabel(4, 0, "i", 1, TokenFG)
	lookup := func(Token) RGB { return RGB{R: 139, G: 141, B: 152} }
	want := "\x1b[38;2;139;141;152m│  \x1b[39mHi  \x1b[38;2;139;141;152m│\x1b[39m\n"
	if got := string(c.Serialise(CharsetUnicode, ColorTruecolor, lookup)); got != want {
		t.Fatalf("%q", got)
	}
	if ANSI256(lookup(TokenBorder)) != 246 || ANSI16(RGB{R: 230}) != 1 {
		t.Fatal("quantisation")
	}
	strip := regexp.MustCompile("\x1b\\[[0-9;]*m")
	for _, m := range []ColorMode{ColorANSI16, ColorANSI256, ColorTruecolor} {
		if string(strip.ReplaceAll(c.Serialise(CharsetUnicode, m, lookup), nil)) != string(c.Serialise(CharsetUnicode, ColorNone, nil)) {
			t.Fatal(m)
		}
	}
}

func TestColourGoldens(t *testing.T) {
	c := canvas(t, 8, 1)
	c.AttachInk(0, 0, BitN|BitS, StyleLight, TokenBorder)
	c.AttachInk(7, 0, BitN|BitS, StyleLight, TokenBorder)
	c.PutLabel(3, 0, "H", 1, TokenFG)
	c.PutLabel(4, 0, "i", 1, TokenFG)
	lookup := func(Token) RGB { return RGB{R: 139, G: 141, B: 152} }
	for i, name := range []string{"none", "ansi16", "ansi256", "truecolor"} {
		want, err := os.ReadFile("testdata/colour/" + name + ".txt")
		if err != nil {
			t.Fatal(err)
		}
		if got := c.Serialise(CharsetUnicode, ColorMode(i), lookup); string(got) != string(want) {
			t.Fatalf("%s: %q != %q", name, got, want)
		}
	}
}
