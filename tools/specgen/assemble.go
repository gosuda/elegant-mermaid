package main

import "fmt"

type arraySpec struct {
	name     string
	goName   string
	rsName   string
	leanName string
	goElem   string
	rsElem   string
	leanElem string
	values   []int64
}

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
		computed.width,
		computed.graphemes,
		computed.incb,
		computed.ideographic,
	}
	tables = append(tables, specTables...)
	return append(tables, computed.sine, computed.lin16Table), nil
}

type computedTables struct {
	kinds       *table
	advances    *table
	upem        *arrayTable
	width       *table
	graphemes   *table
	incb        *table
	ideographic *table
	sine        *arrayTable
	lin16       [lin16Entries]uint16
	lin16Table  *arrayTable
}

func computeStartingTables(in *inputs) (*computedTables, error) {
	sine, err := sineTable()
	if err != nil {
		return nil, fmt.Errorf("sine table: %w", err)
	}
	lin16, err := lin16Table()
	if err != nil {
		return nil, fmt.Errorf("lin16 table: %w", err)
	}
	advances, upems, err := buildAdvances(in.regularTTF, in.semiboldTTF)
	if err != nil {
		return nil, fmt.Errorf("advances: %w", err)
	}
	widths, err := buildUnicodeWidth(map[string][]byte{
		"EastAsianWidth.txt":        in.eaw,
		"emoji-data.txt":            in.emoji,
		"GraphemeBreakProperty.txt": in.gbp,
	})
	if err != nil {
		return nil, err
	}
	graphemes, err := buildGraphemes(in.gbp, in.emoji)
	if err != nil {
		return nil, err
	}
	incb, err := buildIncb(in.derived)
	if err != nil {
		return nil, err
	}
	ideographic, err := buildIdeographic(in.propList)
	if err != nil {
		return nil, err
	}
	kinds, err := buildKindTable(in.kinds)
	if err != nil {
		return nil, err
	}
	return &computedTables{
		kinds:       kinds,
		advances:    buildAdvancesTable(advances),
		upem:        newArrayTable(arraySpec{name: "advancesupem", goName: "AdvancesUpem", rsName: "ADVANCES_UPEM", leanName: "advancesUpem", goElem: "int32", rsElem: "i32", leanElem: "Int", values: upemValues(upems)}),
		width:       buildWidthTable(widths),
		graphemes:   buildGraphemeTable(graphemes),
		incb:        buildIncbTable(incb),
		ideographic: buildIdeographicTable(ideographic),
		sine:        newArrayTable(arraySpec{name: "sine", goName: "SineTable", rsName: "SINE_TABLE", leanName: "sineTable", goElem: "int32", rsElem: "i32", leanElem: "Int", values: sineValues(sine)}),
		lin16:       lin16,
		lin16Table:  newArrayTable(arraySpec{name: "lin16", goName: "Lin16", rsName: "LIN16", leanName: "lin16", goElem: "uint16", rsElem: "u16", leanElem: "Nat", values: lin16Values(lin16)}),
	}, nil
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
