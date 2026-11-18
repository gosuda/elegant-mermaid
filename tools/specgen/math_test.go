package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/image/font/sfnt"
)

func mathFont(t *testing.T) ([]byte, func(uint32) bool) {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(dataRoot(t), "spec", "data", "fonts", "Inter-Regular.ttf"))
	if err != nil {
		t.Fatal(err)
	}
	font, err := sfnt.Parse(data)
	if err != nil {
		t.Fatal(err)
	}
	return data, func(cp uint32) bool {
		t.Helper()
		index, err := font.GlyphIndex(nil, rune(cp))
		if err != nil {
			t.Fatalf("independent cmap lookup U+%04X: %v", cp, err)
		}
		return index != 0
	}
}

func TestMathGreekFontMapping(t *testing.T) {
	data, hasGlyph := mathFont(t)
	advances, _, err := buildAdvances(data, nil)
	if err != nil {
		t.Fatal(err)
	}
	for i := range advances {
		advances[i].Units = 0
	}
	tbl, err := mathGreekTable(regularMathGlyphs(advances))
	if err != nil {
		t.Fatal(err)
	}
	mapped := assertMathGreekFontCoverage(t, tbl, hasGlyph)
	for _, tc := range []struct {
		name              string
		primary, fallback uint32
	}{
		{"epsilon", 0x03F5, 0x03B5}, {"vartheta", 0x03D1, 0x03B8}, {"phi", 0x03D5, 0x03C6},
	} {
		want := tc.primary
		if !hasGlyph(want) {
			want = tc.fallback
		}
		if mapped[tc.name] != want {
			t.Fatalf("%s maps to U+%04X; independent cmap requires U+%04X", tc.name, mapped[tc.name], want)
		}
		t.Logf("font-backed %s: U+%04X", tc.name, want)
	}
	for _, name := range []string{"omicron", "varpi", "varrho", "varsigma"} {
		if _, ok := mapped[name]; ok {
			t.Fatalf("unsupported Greek command %s was generated", name)
		}
	}
}

func assertMathGreekFontCoverage(t *testing.T, tbl *table, hasGlyph func(uint32) bool) map[string]uint32 {
	t.Helper()
	previous := ""
	mapped := make(map[string]uint32)
	for _, row := range tbl.rows {
		name := row[0].(string)
		cp := row[1].(uint32)
		if name <= previous || !hasGlyph(cp) {
			t.Fatalf("mapping %q U+%04X is unordered or absent from cmap", name, cp)
		}
		previous = name
		mapped[name] = cp
	}
	return mapped
}

func TestMathGreekFallback(t *testing.T) {
	_, hasGlyph := mathFont(t)
	for _, tc := range []struct {
		name              string
		primary, fallback uint32
	}{
		{"epsilon", 0x03F5, 0x03B5}, {"vartheta", 0x03D1, 0x03B8}, {"phi", 0x03D5, 0x03C6},
	} {
		if !hasGlyph(tc.fallback) {
			t.Fatalf("font lacks permitted fallback U+%04X", tc.fallback)
		}
		tbl, err := mathGreekTable(func(cp uint32) bool { return cp != tc.primary && hasGlyph(cp) })
		if err != nil {
			t.Fatal(err)
		}
		for _, row := range tbl.rows {
			if row[0] == tc.name && row[1] != tc.fallback {
				t.Fatalf("missing primary must select U+%04X, got %v", tc.fallback, row[1])
			}
		}
	}
}

func TestMathGreekRequiredGlyphs(t *testing.T) {
	_, hasGlyph := mathFont(t)
	for _, missing := range []uint32{0x03B1, 0x03B5} {
		_, err := mathGreekTable(func(cp uint32) bool { return cp != missing && hasGlyph(cp) })
		if err == nil || !strings.Contains(err.Error(), fmt.Sprintf("U+%04X", missing)) {
			t.Fatalf("missing required Greek glyph must fail informatively: %v", err)
		}
	}
	if _, err := mathGreekTable(regularMathGlyphs(nil)); err == nil {
		t.Fatal("missing regular font must not generate an unvalidated mapping")
	}
}

func TestMathRequiredSymbolGlyphs(t *testing.T) {
	_, hasGlyph := mathFont(t)
	for _, missing := range []uint32{0x2211, 0x21D4, 'A', '0', '$'} {
		_, err := mathGlyphTable(func(cp uint32) bool { return cp != missing && hasGlyph(cp) })
		if err == nil || !strings.Contains(err.Error(), fmt.Sprintf("U+%04X", missing)) {
			t.Fatalf("missing required symbol must fail informatively: %v", err)
		}
	}
}

func TestMathGlyphMapping(t *testing.T) {
	data, hasGlyph := mathFont(t)
	advances, _, advanceErr := buildAdvances(data, nil)
	if advanceErr != nil {
		t.Fatal(advanceErr)
	}
	for i := range advances {
		advances[i].Units = 0
	}
	tbl, err := mathGlyphTable(regularMathGlyphs(advances))
	if err != nil {
		t.Fatal(err)
	}
	assertMathGlyphSubstitutions(t, tbl, hasGlyph)
	if !hasGlyph(0x22C5) && len(tbl.rows) == 0 {
		t.Fatal("missing logical dot must generate the approved font substitution")
	}
}

func assertMathGlyphSubstitutions(t *testing.T, tbl *table, hasGlyph func(uint32) bool) {
	t.Helper()
	for _, row := range tbl.rows {
		logical, physical := row[0].(uint32), row[1].(uint32)
		if logical != 0x22C5 || physical != 0x00B7 || hasGlyph(logical) || !hasGlyph(physical) {
			t.Fatalf("unapproved or unnecessary font substitution: U+%04X -> U+%04X", logical, physical)
		}
	}
}

func TestMathGlyphPrimaryPreferred(t *testing.T) {
	_, hasGlyph := mathFont(t)
	tbl, err := mathGlyphTable(func(cp uint32) bool { return cp == 0x22C5 || hasGlyph(cp) })
	if err != nil {
		t.Fatal(err)
	}
	if len(tbl.rows) != 0 {
		t.Fatal("present primary dot must not generate a substitution")
	}
}

func TestMathGlyphApprovedSubstitution(t *testing.T) {
	_, hasGlyph := mathFont(t)
	if !hasGlyph(0x00B7) {
		t.Fatal("actual font must supply the approved middle dot")
	}
	tbl, err := mathGlyphTable(func(cp uint32) bool { return cp != 0x22C5 && hasGlyph(cp) })
	if err != nil {
		t.Fatal(err)
	}
	if len(tbl.rows) != 1 || tbl.rows[0][0] != uint32(0x22C5) || tbl.rows[0][1] != uint32(0x00B7) {
		t.Fatalf("logical dot must select the approved physical middle dot: %v", tbl.rows)
	}
}

func TestMathGlyphBothDotsMissing(t *testing.T) {
	_, hasGlyph := mathFont(t)
	_, err := mathGlyphTable(func(cp uint32) bool { return cp != 0x22C5 && cp != 0x00B7 && hasGlyph(cp) })
	if err == nil || !strings.Contains(err.Error(), "U+22C5") || !strings.Contains(err.Error(), "U+00B7") {
		t.Fatalf("missing logical and physical dots must fail informatively: %v", err)
	}
}
