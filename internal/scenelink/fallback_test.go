package scenelink

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func triangle() []Command {
	return []Command{
		{Op: OpMoveTo, Points: [3][2]int32{{0, 0}}},
		{Op: OpLineTo, Points: [3][2]int32{{100, 0}}},
		{Op: OpLineTo, Points: [3][2]int32{{50, 80}}},
	}
}

func runeFace(name string, upem, adv int32, cps ...rune) FallbackFace {
	return FallbackFace{
		Name:       name,
		UnitsPerEm: upem,
		GlyphByRune: func(cp rune) (Glyph, bool) {
			for _, want := range cps {
				if cp == want {
					return Glyph{Rune: cp, Advance: adv, Commands: triangle(), Face: name}, true
				}
			}
			return Glyph{}, false
		},
		GlyphByID: func(uint16) (Glyph, bool) {
			return Glyph{}, false
		},
	}
}

func emojiFace() FallbackFace {
	cmds := triangle()
	return FallbackFace{
		Name:       EmojiFile,
		UnitsPerEm: 1024,
		GlyphByRune: func(cp rune) (Glyph, bool) {
			if cp != 0x2764 {
				return Glyph{}, false
			}
			return Glyph{Rune: cp, Advance: 1280, Commands: cmds, Face: EmojiFile}, true
		},
		GlyphByID: func(uint16) (Glyph, bool) {
			return Glyph{Advance: 1280, Commands: cmds, Face: EmojiFile}, true
		},
	}
}

func testOutlines() Outlines {
	inter := Font{UnitsPerEm: 2048, Glyphs: []Glyph{
		{Rune: 0x23, Advance: 800, Commands: triangle()},
		{Rune: 0x41, Advance: 1024, Commands: triangle()},
		{Rune: 0x200D, Advance: 0, Commands: triangle()},
		{Rune: 0x20E3, Advance: 320, Commands: triangle()},
		{Rune: 0x2642, Advance: 1024, Commands: triangle()},
		{Rune: 0x2764, Advance: 1024, Commands: triangle()},
		{Rune: 0xFE0F, Advance: 256, Commands: triangle()},
		{Rune: 0x1F937, Advance: 1280, Commands: triangle()},
	}}
	emo := emojiFace()
	regular := inter
	regular.Fallback = []FallbackFace{
		emo,
		runeFace(SansRegularFile, 1000, 900, 0xA66E),
		runeFace(SymbolsRegularFile, 1000, 864, 0x2697),
		runeFace(Symbols2File, 1000, 0),
		runeFace(MathFile, 1000, 628, 0x1D518),
		runeFace(CJKRegularFile, 1000, 1000, 0x4E2D),
		runeFace(CopticFile, 1000, 545, 0x3E7),
	}
	semi := Font{UnitsPerEm: 2048}
	semi.Fallback = []FallbackFace{
		emo,
		runeFace(SansSemiBoldFile, 1000, 900, 0xA66E),
		runeFace(SymbolsSemiFile, 1000, 864, 0x2697),
		runeFace(Symbols2File, 1000, 0),
		runeFace(MathFile, 1000, 628, 0x1D518),
		runeFace(CJKSemiBoldFile, 1000, 1000, 0x4E2D),
		runeFace(CopticFile, 1000, 545, 0x3E7),
	}
	return Outlines{regular, semi}
}

func collectOne(t *testing.T, o Outlines, role scene.TextRole, text string) (Glyph, Placement, int64, int64) {
	t.Helper()
	txt := &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 12800, H: 1280}, Role: role, Size: 10, Align: scene.AlignStart, Style: "text", Lines: [][]scene.Run{{{Text: text}}}}
	line := txt.Lines[0]
	w := o.LineWidth(txt, line)
	x := TextLeft(txt, w)
	y := Baseline(txt, 0)
	var gs []Glyph
	var ps []Placement
	for g, at := range o.Glyphs(txt, line, x, y) {
		gs = append(gs, g)
		ps = append(ps, at)
	}
	if len(gs) != 1 || len(ps) != 1 {
		t.Fatalf("want one glyph for %q, got %d", text, len(gs))
	}
	return gs[0], ps[0], x, y
}

func checkFallback(t *testing.T, text string, g Glyph, face string) {
	t.Helper()
	if g.Face != face {
		t.Fatalf("%q face: got %q want %q", text, g.Face, face)
	}
	if len(g.Commands) == 0 {
		t.Fatalf("%q has no outline", text)
	}
}

func checkInter(t *testing.T, text string, g Glyph, want rune) {
	t.Helper()
	if g.Face != "" || g.Rune != want {
		t.Fatalf("%q inter: %+v", text, g)
	}
	if len(g.Commands) == 0 {
		t.Fatalf("%q has no outline", text)
	}
}

func checkPlacement(t *testing.T, text string, at Placement, x, slot, nat, dx int64) {
	t.Helper()
	if at.Slot != slot || at.Natural != nat {
		t.Fatalf("%q placement: got slot %d natural %d, want %d %d", text, at.Slot, at.Natural, slot, nat)
	}
	if at.X != x+dx {
		t.Fatalf("%q origin: got %d want %d", text, at.X, x+dx)
	}
}

func requireNoSequenceStarting(t *testing.T, cp uint32) {
	t.Helper()
	for _, row := range gen.EmojiSequences {
		if len(row.Scalars) > 0 && row.Scalars[0] == cp {
			t.Fatalf("U+%04X starts an emoji sequence", cp)
		}
	}
}

func TestFallbackInterWins(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "A")
	checkInter(t, "A", g, 'A')
	checkPlacement(t, "A", at, x, 0, 0, 0)
	if at.UnitsPerEm != 2048 {
		t.Fatalf("inter upem: %+v", at)
	}
}

func TestFallbackCJK(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "中")
	checkFallback(t, "中", g, CJKRegularFile)
	checkPlacement(t, "中", at, x, 640, 640, 0)
}

func TestFallbackSymbols(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "⚗")
	checkFallback(t, "⚗", g, SymbolsRegularFile)
	checkPlacement(t, "⚗", at, x, 384, 553, 0)
}

func TestFallbackMath(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "𝔘")
	checkFallback(t, "𝔘", g, MathFile)
	checkPlacement(t, "𝔘", at, x, 384, 402, 0)
}

func TestFallbackCoptic(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "ϧ")
	checkFallback(t, "ϧ", g, CopticFile)
	checkPlacement(t, "ϧ", at, x, 384, 349, 17)
}

func TestFallbackSans(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "ꙮ")
	checkFallback(t, "ꙮ", g, SansRegularFile)
	checkPlacement(t, "ꙮ", at, x, 384, 576, 0)
}

func TestFallbackFlagSequence(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "🇯🇵")
	checkFallback(t, "flag", g, EmojiFile)
	checkPlacement(t, "flag", at, x, 1280, 800, 240)
}

func TestFallbackEmojiSingleWithFE0F(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "❤\uFE0F")
	checkFallback(t, "emoji", g, EmojiFile)
	if g.Rune != 0x2764 {
		t.Fatalf("emoji rune: %+v", g)
	}
	checkPlacement(t, "emoji", at, x, 400, 800, 0)
}

func TestFallbackHeartAloneIsInter(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "❤")
	checkInter(t, "heart", g, 0x2764)
	checkPlacement(t, "heart", at, x, 0, 0, 0)
}

func TestFallbackWideScaledPoint(t *testing.T) {
	o := testOutlines()
	g, at, x, y := collectOne(t, o, scene.TextRoleBody, "⚗")
	checkFallback(t, "⚗", g, SymbolsRegularFile)
	checkPlacement(t, "⚗", at, x, 384, 553, 0)
	sx, sy := at.Point(100, 0)
	if sx != x+round(100*10*64*384, 1000*553) {
		t.Fatalf("scaled point x: got %d", sx)
	}
	if sy != y {
		t.Fatalf("scaled point y: got %d want %d", sy, y)
	}
}

func TestFallbackSemiboldCJK(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleLabel, "中")
	checkFallback(t, "semibold cjk", g, CJKSemiBoldFile)
	checkPlacement(t, "semibold cjk", at, x, 640, 640, 0)
}

func TestFallbackKeycapSkipsFE0F(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "#\uFE0F\u20E3")
	checkFallback(t, "keycap", g, EmojiFile)
	checkPlacement(t, "keycap", at, x, 430, 800, 0)
}

func TestFallbackShrugTrailingFE0F(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "🤷\u200D\u2642\uFE0F")
	checkFallback(t, "shrug", g, EmojiFile)
	checkPlacement(t, "shrug", at, x, 800, 800, 0)
}

func TestFallbackHeartWithVS16TakesTheEmojiGlyph(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "❤\uFE0F")
	checkFallback(t, "heart vs16", g, EmojiFile)
	if g.Rune != 0x2764 {
		t.Fatalf("heart vs16 rune: %+v", g)
	}
	checkPlacement(t, "heart vs16", at, x, 400, 800, 0)
}

func TestFallbackInterPairTakesBothSlots(t *testing.T) {
	o := testOutlines()
	g, at, x, _ := collectOne(t, o, scene.TextRoleBody, "A\uFE0F")
	checkInter(t, "inter vs16", g, 'A')
	checkPlacement(t, "inter vs16", at, x, 400, 320, 40)
}

func TestFallbackInterVS16Preconditions(t *testing.T) {
	o := testOutlines()
	requireNoSequenceStarting(t, 65)
	if isPresentation(65) {
		t.Fatal("U+0041 has Emoji_Presentation")
	}
	if _, ok := o[0].Fallback[0].GlyphByRune(65); ok {
		t.Fatal("Noto Emoji has U+0041")
	}
	g, ok := o[0].hasInter(65)
	if !ok {
		t.Fatal("Inter lacks U+0041")
	}
	if len(g.Commands) == 0 {
		t.Fatal("Inter U+0041 has no outline")
	}
}
