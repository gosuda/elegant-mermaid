package raster

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"golang.org/x/image/font"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
)

func fallbackFace(name string, data []byte) scenelink.FallbackFace {
	parsed, upem := parseFallback(data)
	if parsed == nil {
		return scenelink.FallbackFace{Name: name, GlyphByRune: missRune, GlyphByID: missID}
	}
	return scenelink.FallbackFace{
		Name:        name,
		UnitsPerEm:  upem,
		GlyphByRune: runeLookup(parsed, name, upem),
		GlyphByID:   idLookup(parsed, name, upem),
	}
}

func missRune(rune) (scenelink.Glyph, bool) { return scenelink.Glyph{}, false }

func missID(uint16) (scenelink.Glyph, bool) { return scenelink.Glyph{}, false }

func parseFallback(data []byte) (*sfnt.Font, int32) {
	if len(data) == 0 {
		return nil, 0
	}
	parsed, err := sfnt.Parse(data)
	if err != nil {
		return nil, 0
	}
	upem := int32(parsed.UnitsPerEm())
	if upem <= 0 {
		return nil, 0
	}
	return parsed, upem
}

func runeLookup(f *sfnt.Font, name string, upem int32) func(rune) (scenelink.Glyph, bool) {
	return func(cp rune) (scenelink.Glyph, bool) {
		var b sfnt.Buffer
		idx, err := f.GlyphIndex(&b, cp)
		if err != nil || idx == 0 {
			return scenelink.Glyph{}, false
		}
		g, ok := indexedGlyph(f, name, upem, idx)
		if !ok {
			return scenelink.Glyph{}, false
		}
		g.Rune = cp
		return g, true
	}
}

func idLookup(f *sfnt.Font, name string, upem int32) func(uint16) (scenelink.Glyph, bool) {
	return func(id uint16) (scenelink.Glyph, bool) {
		return indexedGlyph(f, name, upem, sfnt.GlyphIndex(id))
	}
}

func indexedGlyph(f *sfnt.Font, name string, upem int32, idx sfnt.GlyphIndex) (scenelink.Glyph, bool) {
	var b sfnt.Buffer
	ppem := fixed.I(int(upem))
	adv, err := f.GlyphAdvance(&b, idx, ppem, font.HintingNone)
	if err != nil {
		return scenelink.Glyph{}, false
	}
	segs, err := f.LoadGlyph(&b, idx, ppem, nil)
	if err != nil {
		return scenelink.Glyph{}, false
	}
	cmds, ok := convertOutline(segs)
	if !ok {
		return scenelink.Glyph{}, false
	}
	return scenelink.Glyph{Advance: int32(int64(adv) / 64), Commands: cmds, Face: name}, true
}

func convertOutline(segs []sfnt.Segment) ([]scenelink.Command, bool) {
	out := make([]scenelink.Command, 0, len(segs))
	for _, s := range segs {
		c, ok := convertSegment(s)
		if !ok {
			return nil, false
		}
		out = append(out, c)
	}
	if len(out) == 0 {
		return nil, false
	}
	return out, true
}

func convertSegment(s sfnt.Segment) (scenelink.Command, bool) {
	var c scenelink.Command
	if s.Op == sfnt.SegmentOpCubeTo {
		return c, false
	}
	c.Op = uint8(s.Op)
	for idx, p := range s.Args {
		q, ok := quantizePair(int64(p.X), int64(p.Y))
		if !ok {
			return scenelink.Command{}, false
		}
		c.Points[idx] = q
	}
	return c, true
}

func quantizePair(x, y int64) ([2]int32, bool) {
	qx, ok := quantize(x)
	if !ok {
		return [2]int32{}, false
	}
	qy, ok := quantize(y)
	if !ok {
		return [2]int32{}, false
	}
	return [2]int32{qx, -qy}, true
}

func quantize(v int64) (int32, bool) {
	if v%32 != 0 {
		return 0, false
	}
	q := geom.FloorDiv(v+32, 64)
	if q < -2147483648 || q > 2147483647 {
		return 0, false
	}
	return int32(q), true
}
