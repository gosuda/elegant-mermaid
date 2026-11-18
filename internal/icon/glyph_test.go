package icon_test

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"github.com/gosuda/elegant-mermaid/raster"
)

func TestUnknownGlyphMatchesInterQuestionMark(t *testing.T) {
	fonts, ok := scenelink.OutlinesOf(raster.InterOutlines())
	if !ok {
		t.Fatal("no embedded outlines")
	}
	regular := fonts[0]
	var glyph *scenelink.Glyph
	for i := range regular.Glyphs {
		if regular.Glyphs[i].Rune == '?' {
			glyph = &regular.Glyphs[i]
		}
	}
	if glyph == nil || regular.UnitsPerEm != 2048 {
		t.Fatalf("question mark glyph %v, units per em %d", glyph, regular.UnitsPerEm)
	}
	rows := icon.UnknownGlyphRows()
	if len(rows) != len(glyph.Commands) {
		t.Fatalf("%d rows, Inter has %d segments", len(rows), len(glyph.Commands))
	}
	for i, c := range glyph.Commands {
		want := [5]int32{int32(c.Op), c.Points[0][0], c.Points[0][1], 0, 0}
		if c.Op == 2 {
			want[3], want[4] = c.Points[1][0], c.Points[1][1]
		}
		if rows[i] != want {
			t.Errorf("row %d = %v, want %v", i, rows[i], want)
		}
	}
}
