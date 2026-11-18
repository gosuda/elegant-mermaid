package main

import "fmt"

func buildGeneratedTables(in *inputs) ([]renderable, error) {
	computed, err := computeStartingTables(in)
	if err != nil {
		return nil, err
	}
	specTables, err := buildRegistryTables(in, computed.lin16)
	if err != nil {
		return nil, err
	}
	tables := []renderable{
		computed.kinds,
		computed.advances,
		computed.upem,
		computed.mathGreek,
		computed.mathGlyph,
		computed.width,
		computed.graphemes,
		computed.incb,
		computed.ideographic,
		computed.alphanumeric,
	}
	tables = append(tables, specTables...)
	return append(tables, computed.sine, computed.lin16Table), nil
}

type computedTables struct {
	kinds        *table
	advances     *table
	mathGreek    *table
	mathGlyph    *table
	upem         *arrayTable
	width        *table
	graphemes    *table
	incb         *table
	ideographic  *table
	alphanumeric *table
	sine         *arrayTable
	lin16        [lin16Entries]uint16
	lin16Table   *arrayTable
}

func computeStartingTables(in *inputs) (*computedTables, error) {
	sine, sineErr := sineTable()
	if sineErr != nil {
		return nil, fmt.Errorf("sine table: %w", sineErr)
	}
	lin16, lin16Err := lin16Table()
	if lin16Err != nil {
		return nil, fmt.Errorf("lin16 table: %w", lin16Err)
	}
	advances, upems, advanceErr := buildAdvances(in.regularTTF, in.semiboldTTF)
	if advanceErr != nil {
		return nil, fmt.Errorf("advances: %w", advanceErr)
	}
	mathGreek, mathGlyph, mathErr := buildMathTables(advances)
	if mathErr != nil {
		return nil, mathErr
	}
	computed := &computedTables{
		advances:   buildAdvancesTable(advances),
		mathGreek:  mathGreek,
		mathGlyph:  mathGlyph,
		upem:       &arrayTable{name: "advancesupem", goName: "AdvancesUpem", rsName: "ADVANCES_UPEM", leanName: "advancesUpem", goElem: "int32", rsElem: "i32", leanElem: "Int", values: upemValues(upems)},
		sine:       &arrayTable{name: "sine", goName: "SineTable", rsName: "SINE_TABLE", leanName: "sineTable", goElem: "int32", rsElem: "i32", leanElem: "Int", values: sineValues(sine)},
		lin16:      lin16,
		lin16Table: &arrayTable{name: "lin16", goName: "Lin16", rsName: "LIN16", leanName: "lin16", goElem: "uint16", rsElem: "u16", leanElem: "Nat", values: lin16Values(lin16)},
	}
	if err := computed.buildUnicodeTables(in); err != nil {
		return nil, err
	}
	kinds, kindErr := buildKindTable(in.kinds)
	if kindErr != nil {
		return nil, kindErr
	}
	computed.kinds = kinds
	return computed, nil
}

func (computed *computedTables) buildUnicodeTables(in *inputs) error {
	widths, widthErr := buildUnicodeWidth(map[string][]byte{
		"EastAsianWidth.txt":        in.eaw,
		"emoji-data.txt":            in.emoji,
		"GraphemeBreakProperty.txt": in.gbp,
	})
	if widthErr != nil {
		return widthErr
	}
	graphemes, graphemeErr := buildGraphemes(in.gbp, in.emoji)
	if graphemeErr != nil {
		return graphemeErr
	}
	incb, incbErr := buildIncb(in.derived)
	if incbErr != nil {
		return incbErr
	}
	ideographic, ideographicErr := buildIdeographic(in.propList)
	if ideographicErr != nil {
		return ideographicErr
	}
	alphanumeric, alphanumericErr := buildAlphanumeric(in.derived, in.generalCategory)
	if alphanumericErr != nil {
		return alphanumericErr
	}
	computed.width = buildWidthTable(widths)
	computed.graphemes = buildGraphemeTable(graphemes)
	computed.incb = buildIncbTable(incb)
	computed.ideographic = buildIdeographicTable(ideographic)
	computed.alphanumeric = buildAlphanumericTable(alphanumeric)
	return nil
}

func buildMathTables(advances []advanceRow) (*table, *table, error) {
	hasMathGlyph := regularMathGlyphs(advances)
	greek, err := mathGreekTable(hasMathGlyph)
	if err != nil {
		return nil, nil, err
	}
	glyph, err := mathGlyphTable(hasMathGlyph)
	if err != nil {
		return nil, nil, err
	}
	return greek, glyph, nil
}

func buildRegistryTables(in *inputs, lin16 [lin16Entries]uint16) ([]renderable, error) {
	type builder func() (renderable, error)
	builders := []builder{
		func() (renderable, error) { return buildGlyphJoinTable(in.glyphJoin) },
		func() (renderable, error) { return buildLayoutConstTable(in.layoutConst), nil },
		func() (renderable, error) { return buildScriptsTable(in.scripts) },
		func() (renderable, error) { return buildDiagnosticsTable(in.diagnostics) },
		func() (renderable, error) { return buildLintRulesTable(in.lintRules) },
		func() (renderable, error) { return buildShapesTable(in.shapes) },
		func() (renderable, error) { return buildMarkersTable(in.markers) },
		func() (renderable, error) { return buildThemesTable(in.themes), nil },
		func() (renderable, error) { return buildConfigKeysTable(in.configKeys), nil },
		func() (renderable, error) { return buildStylesTable(in.styles) },
		func() (renderable, error) { return buildCellSymbolsTable(in.cellSymbols) },
		func() (renderable, error) { return buildSeriesTextTable(in.themes, lin16) },
		func() (renderable, error) { return buildStrokeOkTable(in.themes, lin16) },
		func() (renderable, error) { return buildEntitiesTable(in.entities), nil },
	}
	tables := make([]renderable, 0, len(builders))
	for _, build := range builders {
		tbl, err := build()
		if err != nil {
			return nil, err
		}
		tables = append(tables, tbl)
	}
	return tables, nil
}

func upemValues(upems [2]int32) []int64 {
	return []int64{int64(upems[0]), int64(upems[1])}
}

func sineValues(table [sineEntries]int32) []int64 {
	values := make([]int64, 0, len(table))
	for _, v := range table {
		values = append(values, int64(v))
	}
	return values
}

func lin16Values(table [lin16Entries]uint16) []int64 {
	values := make([]int64, 0, len(table))
	for _, v := range table {
		values = append(values, int64(v))
	}
	return values
}
