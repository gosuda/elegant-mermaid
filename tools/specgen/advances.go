package main

import (
	"cmp"
	"errors"
	"fmt"
	"math"
	"slices"

	"golang.org/x/image/font"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
)

type advanceRow struct {
	Weight uint8
	CP     uint32
	Units  uint16
}

func buildAdvances(regular, semibold []byte) ([]advanceRow, [2]int32, error) {
	var upems [2]int32
	sources := []struct {
		weight uint8
		data   []byte
	}{{0, regular}, {1, semibold}}
	var rows []advanceRow
	for _, src := range sources {
		if len(src.data) == 0 {
			continue
		}
		f, err := sfnt.Parse(src.data)
		if err != nil {
			return nil, upems, fmt.Errorf("parse font weight %d: %w", src.weight, err)
		}
		upem := f.UnitsPerEm()
		if upem <= 0 {
			return nil, upems, fmt.Errorf("font weight %d has units per em %d", src.weight, upem)
		}
		upems[src.weight] = int32(upem)
		fontRows, err := advancesForFont(f, src.weight, uint16(upem))
		if err != nil {
			return nil, upems, err
		}
		rows = append(rows, fontRows...)
	}
	slices.SortStableFunc(rows, func(a, b advanceRow) int {
		return cmp.Or(cmp.Compare(a.Weight, b.Weight), cmp.Compare(a.CP, b.CP))
	})
	return rows, upems, nil
}

func advancesForFont(f *sfnt.Font, weight uint8, upem uint16) ([]advanceRow, error) {
	ppem := fixed.Int26_6(upem)
	rows := make([]advanceRow, 0, 3000)
	for cp := rune(0); cp <= 0x10FFFF; cp++ {
		if cp >= 0xD800 && cp <= 0xDFFF {
			continue
		}
		idx, err := f.GlyphIndex(nil, cp)
		if err != nil {
			return nil, fmt.Errorf("cmap lookup U+%04X: %w", cp, err)
		}
		if idx == 0 {
			continue
		}
		adv, err := f.GlyphAdvance(nil, idx, ppem, font.HintingNone)
		if err != nil {
			return nil, fmt.Errorf("hmtx lookup U+%04X: %w", cp, err)
		}
		units := int32(adv)
		if units < 0 || units > math.MaxUint16 {
			return nil, fmt.Errorf("advance of U+%04X is %d font units", cp, units)
		}
		rows = append(rows, advanceRow{Weight: weight, CP: uint32(cp), Units: uint16(units)})
	}
	if len(rows) == 0 {
		return nil, errors.New("font maps no code points")
	}
	return rows, nil
}
