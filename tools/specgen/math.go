package main

import (
	"cmp"
	"fmt"
	"slices"
)

type mathGreekCommand struct {
	name      string
	codepoint uint32
	fallback  uint32
}

func regularMathGlyphs(advances []advanceRow) func(uint32) bool {
	present := make(map[uint32]bool)
	for _, row := range advances {
		if row.Weight == 0 {
			present[row.CP] = true
		}
	}
	return func(cp uint32) bool { return present[cp] }
}

func mathGreekTable(hasGlyph func(uint32) bool) (*table, error) {
	commands := []mathGreekCommand{
		{"alpha", 0x03B1, 0},
		{"beta", 0x03B2, 0},
		{"gamma", 0x03B3, 0},
		{"delta", 0x03B4, 0},
		{"epsilon", 0x03F5, 0x03B5},
		{"varepsilon", 0x03B5, 0},
		{"zeta", 0x03B6, 0},
		{"eta", 0x03B7, 0},
		{"theta", 0x03B8, 0},
		{"vartheta", 0x03D1, 0x03B8},
		{"iota", 0x03B9, 0},
		{"kappa", 0x03BA, 0},
		{"lambda", 0x03BB, 0},
		{"mu", 0x03BC, 0},
		{"nu", 0x03BD, 0},
		{"xi", 0x03BE, 0},
		{"pi", 0x03C0, 0},
		{"rho", 0x03C1, 0},
		{"sigma", 0x03C3, 0},
		{"tau", 0x03C4, 0},
		{"upsilon", 0x03C5, 0},
		{"phi", 0x03D5, 0x03C6},
		{"varphi", 0x03C6, 0},
		{"chi", 0x03C7, 0},
		{"psi", 0x03C8, 0},
		{"omega", 0x03C9, 0},
		{"Gamma", 0x0393, 0},
		{"Delta", 0x0394, 0},
		{"Theta", 0x0398, 0},
		{"Lambda", 0x039B, 0},
		{"Xi", 0x039E, 0},
		{"Pi", 0x03A0, 0},
		{"Sigma", 0x03A3, 0},
		{"Upsilon", 0x03A5, 0},
		{"Phi", 0x03A6, 0},
		{"Psi", 0x03A8, 0},
		{"Omega", 0x03A9, 0},
	}
	slices.SortFunc(commands, func(a, b mathGreekCommand) int { return cmp.Compare(a.name, b.name) })
	rows := make([]rowValues, 0, len(commands))
	for _, command := range commands {
		cp := command.codepoint
		if !hasGlyph(cp) && command.fallback != 0 {
			cp = command.fallback
		}
		if !hasGlyph(cp) {
			return nil, fmt.Errorf("math command \\%s requires Inter-Regular cmap glyph U+%04X", command.name, cp)
		}
		rows = append(rows, rowValues{command.name, cp})
	}
	return &table{
		name: "mathgreek", goName: "MathGreekTable", rsName: "MATH_GREEK", leanName: "mathgreek",
		goType: "MathGreek", rsType: "MathGreek", leanType: "MathGreek", rustPublicStatic: true,
		cols: []col{{goName: "Name", rsName: "name", leanName: "name", kind: colString}, {goName: "Codepoint", rsName: "codepoint", leanName: "codepoint", kind: colU32}},
		rows: rows,
	}, nil
}

func mathGlyphTable(hasGlyph func(uint32) bool) (*table, error) {
	var rows []rowValues
	for _, cp := range " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~∑∏∫∞±×÷⋅≤≥≠≈→←⇒⇔" {
		physical := uint32(cp)
		if cp == 0x22C5 && !hasGlyph(physical) {
			physical = 0x00B7
		}
		if !hasGlyph(physical) {
			return nil, fmt.Errorf("math logical glyph U+%04X requires Inter-Regular cmap glyph U+%04X", cp, physical)
		}
		if physical != uint32(cp) {
			rows = append(rows, rowValues{uint32(cp), physical})
		}
	}
	slices.SortFunc(rows, func(a, b rowValues) int { return cmp.Compare(a[0].(uint32), b[0].(uint32)) })
	return &table{
		name: "mathglyph", goName: "MathGlyphMappings", rsName: "MATH_GLYPH_MAPPINGS", leanName: "mathGlyphMappings",
		goType: "MathGlyphMapping", rsType: "MathGlyphMapping", leanType: "MathGlyphMapping", rustPublicStatic: true,
		cols: []col{{goName: "Codepoint", rsName: "codepoint", leanName: "codepoint", kind: colU32}, {goName: "FontCodepoint", rsName: "font_codepoint", leanName: "fontCodepoint", kind: colU32}},
		rows: rows,
	}, nil
}
