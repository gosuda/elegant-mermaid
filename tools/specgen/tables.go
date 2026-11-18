package main

import (
	"cmp"
	"fmt"
	"maps"
	"slices"
	"strings"
)

var (
	kindCols = []col{
		{goName: "ID", rsName: "id", leanName: "id", kind: colString},
		{goName: "Headers", rsName: "headers", leanName: "headers", kind: colRecordList, subName: "KindHeader", sub: []col{
			{goName: "Text", rsName: "text", leanName: "text", kind: colString},
			{goName: "Insensitive", rsName: "insensitive", leanName: "insensitive", kind: colBool},
		}},
		{goName: "UpstreamIDs", rsName: "upstream_ids", leanName: "upstreamIds", kind: colStringList},
	}
	advanceCols = []col{
		{goName: "Weight", rsName: "weight", leanName: "weight", kind: colU8},
		{goName: "CP", rsName: "cp", leanName: "cp", kind: colU32},
		{goName: "Units", rsName: "units", leanName: "units", kind: colU16},
	}
	valueRangeCols = []col{
		{goName: "Lo", rsName: "lo", leanName: "lo", kind: colU32},
		{goName: "Hi", rsName: "hi", leanName: "hi", kind: colU32},
		{goName: "Value", rsName: "value", leanName: "value", kind: colU8},
	}
	propRangeCols = []col{
		{goName: "Lo", rsName: "lo", leanName: "lo", kind: colU32},
		{goName: "Hi", rsName: "hi", leanName: "hi", kind: colU32},
		{goName: "Prop", rsName: "prop", leanName: "prop", kind: colU8},
	}
	idRangeCols = []col{
		{goName: "Lo", rsName: "lo", leanName: "lo", kind: colU32},
		{goName: "Hi", rsName: "hi", leanName: "hi", kind: colU32},
	}
	glyphCols = []col{
		{goName: "Charset", rsName: "charset", leanName: "charset", kind: colU8},
		{goName: "Style", rsName: "style", leanName: "style", kind: colU8},
		{goName: "Mask", rsName: "mask", leanName: "mask", kind: colU8},
		{goName: "Rune", rsName: "rune", leanName: "rune", kind: colU32},
	}
	layoutConstCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "Value", rsName: "value", leanName: "value", kind: colI32},
	}
	scriptCols = []col{
		{goName: "Base", rsName: "base", leanName: "base", kind: colU32},
		{goName: "Sup", rsName: "sup", leanName: "sup", kind: colU32},
		{goName: "Sub", rsName: "sub", leanName: "sub", kind: colU32},
	}
	registryCols = []col{
		{goName: "Code", rsName: "code", leanName: "code", kind: colString},
		{goName: "Severity", rsName: "severity", leanName: "severity", kind: colString},
		{goName: "Summary", rsName: "summary", leanName: "summary", kind: colString},
		{goName: "Help", rsName: "help", leanName: "help", kind: colString},
		{goName: "Rationale", rsName: "rationale", leanName: "rationale", kind: colString},
		{goName: "FixSafety", rsName: "fix_safety", leanName: "fixSafety", kind: colString},
		{goName: "Aliases", rsName: "aliases", leanName: "aliases", kind: colStringList},
	}
	lintRuleCols = append(slices.Clone(registryCols),
		col{goName: "Source", rsName: "source", leanName: "source", kind: colString},
		col{goName: "Status", rsName: "status", leanName: "status", kind: colString},
		col{goName: "Reason", rsName: "reason", leanName: "reason", kind: colString},
	)
	shapeCols = []col{
		{goName: "ID", rsName: "id", leanName: "id", kind: colString},
		{goName: "Family", rsName: "family", leanName: "family", kind: colString},
		{goName: "Corner", rsName: "corner", leanName: "corner", kind: colU8},
		{goName: "Aliases", rsName: "aliases", leanName: "aliases", kind: colStringList},
	}
	markerCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "Paint", rsName: "paint", leanName: "paint", kind: colString},
		{goName: "Cell", rsName: "cell", leanName: "cell", kind: colU32List},
		{goName: "Ascii", rsName: "ascii", leanName: "ascii", kind: colU32List},
		{goName: "Points", rsName: "points", leanName: "points", kind: colPointList},
		{goName: "Ref", rsName: "anchor", leanName: "ref", kind: colPoint},
		{goName: "Breaks", rsName: "breaks", leanName: "breaks", kind: colU32List},
	}
	styleCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "Class", rsName: "class", leanName: "class", kind: colU8},
		{goName: "Fill", rsName: "fill", leanName: "fill", kind: colString},
		{goName: "Stroke", rsName: "stroke", leanName: "stroke", kind: colString},
		{goName: "Tint", rsName: "tint", leanName: "tint", kind: colU8},
		{goName: "Cell", rsName: "cell", leanName: "cell", kind: colU8},
	}
	seriesTextCols = []col{
		{goName: "Theme", rsName: "theme", leanName: "theme", kind: colString},
		{goName: "Series", rsName: "series", leanName: "series", kind: colU8},
		{goName: "Choice", rsName: "choice", leanName: "choice", kind: colU8},
	}
	strokeOkCols = []col{
		{goName: "Theme", rsName: "theme", leanName: "theme", kind: colString},
		{goName: "Token", rsName: "token", leanName: "token", kind: colString},
		{goName: "OK", rsName: "ok", leanName: "ok", kind: colU8},
	}
	symbolCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "Unicode", rsName: "unicode", leanName: "unicode", kind: colU32},
		{goName: "Ascii", rsName: "ascii", leanName: "ascii", kind: colU32},
	}
	themeCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "Tokens", rsName: "tokens", leanName: "tokens", kind: colRecordList, subName: "Token", sub: []col{
			{goName: "Token", rsName: "token", leanName: "token", kind: colString},
			{goName: "Value", rsName: "value", leanName: "value", kind: colString},
		}},
	}
	configKeyCols = []col{
		{goName: "Kind", rsName: "kind", leanName: "kind", kind: colString},
		{goName: "Key", rsName: "key", leanName: "key", kind: colString},
		{goName: "Class", rsName: "class", leanName: "class", kind: colString},
	}
	entityCols = []col{
		{goName: "Name", rsName: "name", leanName: "name", kind: colString},
		{goName: "CPS", rsName: "cps", leanName: "cps", kind: colU32List},
	}
)

var glyphStyles = []struct {
	code  uint8
	field func(glyphJoinInput) string
}{
	{1, func(g glyphJoinInput) string { return g.Dotted }},
	{2, func(g glyphJoinInput) string { return g.Rounded }},
	{3, func(g glyphJoinInput) string { return g.Light }},
	{4, func(g glyphJoinInput) string { return g.Heavy }},
	{5, func(g glyphJoinInput) string { return g.Double }},
}

func buildKindTable(kinds []kindInput) (*table, error) {
	sorted := slices.Clone(kinds)
	slices.SortStableFunc(sorted, func(a, b kindInput) int { return cmp.Compare(a.ID, b.ID) })
	rows := make([]rowValues, 0, len(sorted))
	for _, k := range sorted {
		headers := make([][]any, 0, len(k.Keywords))
		for _, kw := range k.Keywords {
			insensitive, err := keywordInsensitive(kw.Case)
			if err != nil {
				return nil, fmt.Errorf("kind %q keyword %q: %w", k.ID, kw.Text, err)
			}
			headers = append(headers, []any{kw.Text, insensitive})
		}
		rows = append(rows, rowValues{k.ID, headers, slices.Clone(k.Aliases)})
	}
	return &table{name: "kinds", goName: "Kinds", rsName: "KINDS", leanName: "kinds", goType: "Kind", rsType: "Kind", leanType: "Kind", cols: kindCols, rows: rows}, nil
}

func keywordInsensitive(cs string) (bool, error) {
	switch cs {
	case "sensitive":
		return false, nil
	case "insensitive":
		return true, nil
	}
	return false, fmt.Errorf("unknown case rule %q", cs)
}

func buildAdvancesTable(rows []advanceRow) *table {
	values := make([]rowValues, 0, len(rows))
	for _, r := range rows {
		values = append(values, rowValues{r.Weight, r.CP, r.Units})
	}
	return &table{name: "advances", goName: "Advances", rsName: "ADVANCES", leanName: "advances", goType: "Advance", rsType: "Advance", leanType: "Advance", cols: advanceCols, rows: values}
}

func buildWidthTable(ranges []tableRange) *table {
	return &table{name: "unicodewidth", goName: "UnicodeWidth", rsName: "UNICODE_WIDTH", leanName: "unicodewidth", goType: "WidthRange", rsType: "WidthRange", leanType: "WidthRange", cols: valueRangeCols, rows: valueRows(ranges)}
}

func buildGraphemeTable(ranges []tableRange) *table {
	return &table{name: "graphemes", goName: "Graphemes", rsName: "GRAPHEMES", leanName: "graphemes", goType: "GraphemeRange", rsType: "GraphemeRange", leanType: "GraphemeRange", cols: propRangeCols, rows: valueRows(ranges)}
}

func buildIncbTable(ranges []tableRange) *table {
	return &table{name: "incb", goName: "Incb", rsName: "INCB", leanName: "incb", goType: "IncbRange", rsType: "IncbRange", leanType: "IncbRange", cols: propRangeCols, rows: valueRows(ranges)}
}

func buildIdeographicTable(ranges []tableRange) *table {
	return &table{name: "ideographic", goName: "Ideographic", rsName: "IDEOGRAPHIC", leanName: "ideographic", goType: "IdRange", rsType: "IdRange", leanType: "IdRange", cols: idRangeCols, rows: idRows(ranges)}
}

func buildAlphanumericTable(ranges []tableRange) *table {
	return &table{name: "alphanumeric", goName: "Alphanumeric", rsName: "ALPHANUMERIC", leanName: "alphanumeric", goType: "AlphanumericRange", rsType: "AlphanumericRange", leanType: "AlphanumericRange", cols: idRangeCols, rows: idRows(ranges)}
}

func valueRows(ranges []tableRange) []rowValues {
	rows := make([]rowValues, 0, len(ranges))
	for _, r := range ranges {
		rows = append(rows, rowValues{r.Lo, r.Hi, r.Val})
	}
	return rows
}

func idRows(ranges []tableRange) []rowValues {
	rows := make([]rowValues, 0, len(ranges))
	for _, r := range ranges {
		rows = append(rows, rowValues{r.Lo, r.Hi})
	}
	return rows
}

func buildGlyphJoinTable(glyphs []glyphJoinInput) (*table, error) {
	if len(glyphs) == 0 {
		return &table{name: "glyphjoin", goName: "GlyphJoin", rsName: "GLYPH_JOIN", leanName: "glyphjoin", goType: "Glyph", rsType: "Glyph", leanType: "Glyph", cols: glyphCols, rows: []rowValues{}}, nil
	}
	byMask, err := indexGlyphs(glyphs)
	if err != nil {
		return nil, err
	}
	rows, err := glyphJoinRows(byMask)
	if err != nil {
		return nil, err
	}
	return &table{name: "glyphjoin", goName: "GlyphJoin", rsName: "GLYPH_JOIN", leanName: "glyphjoin", goType: "Glyph", rsType: "Glyph", leanType: "Glyph", cols: glyphCols, rows: rows}, nil
}

func glyphJoinRows(byMask map[uint8]glyphJoinInput) ([]rowValues, error) {
	rows := make([]rowValues, 0, 1+len(glyphStyles)*16+32)
	first, err := parseGlyphRune(byMask[0].Light)
	if err != nil {
		return nil, fmt.Errorf("glyph join mask 0 light: %w", err)
	}
	rows = append(rows, rowValues{uint8(0), uint8(0), uint8(0), first})
	rows, err = appendGlyphStyles(rows, byMask)
	if err != nil {
		return nil, err
	}
	rows, err = appendAsciiGlyphs(rows, byMask, 0, func(g glyphJoinInput) string { return g.Ascii })
	if err != nil {
		return nil, err
	}
	return appendAsciiGlyphs(rows, byMask, 1, func(g glyphJoinInput) string { return g.AsciiDotted })
}

func appendGlyphStyles(rows []rowValues, byMask map[uint8]glyphJoinInput) ([]rowValues, error) {
	for _, style := range glyphStyles {
		for mask := range 16 {
			r, err := parseGlyphRune(style.field(byMask[uint8(mask)]))
			if err != nil {
				return nil, fmt.Errorf("glyph join mask %d style %d: %w", mask, style.code, err)
			}
			rows = append(rows, rowValues{uint8(0), style.code, uint8(mask), r})
		}
	}
	return rows, nil
}

func appendAsciiGlyphs(rows []rowValues, byMask map[uint8]glyphJoinInput, styleCode uint8, pick func(glyphJoinInput) string) ([]rowValues, error) {
	for mask := range 16 {
		r, err := parseGlyphRune(pick(byMask[uint8(mask)]))
		if err != nil {
			return nil, fmt.Errorf("glyph join mask %d style %d: %w", mask, styleCode, err)
		}
		rows = append(rows, rowValues{uint8(1), styleCode, uint8(mask), r})
	}
	return rows, nil
}

func indexGlyphs(glyphs []glyphJoinInput) (map[uint8]glyphJoinInput, error) {
	if len(glyphs) != 16 {
		return nil, fmt.Errorf("glyph-join.json has %d rows, want 16", len(glyphs))
	}
	byMask := make(map[uint8]glyphJoinInput, len(glyphs))
	for _, g := range glyphs {
		if g.Mask > 15 {
			return nil, fmt.Errorf("glyph join mask %d is above 15", g.Mask)
		}
		if _, dup := byMask[g.Mask]; dup {
			return nil, fmt.Errorf("glyph join mask %d repeats", g.Mask)
		}
		byMask[g.Mask] = g
	}
	for mask := range 16 {
		if _, ok := byMask[uint8(mask)]; !ok {
			return nil, fmt.Errorf("glyph join mask %d is missing", mask)
		}
	}
	return byMask, nil
}

func parseGlyphRune(s string) (uint32, error) {
	return parseUPlus(s)
}

func parseUPlus(s string) (uint32, error) {
	t := strings.TrimSpace(s)
	lower := strings.ToLower(t)
	if !strings.HasPrefix(lower, "u+") {
		return 0, fmt.Errorf("bad code point %q", s)
	}
	return parseHexCodePoint(t[2:])
}

func buildLayoutConstTable(consts []layoutConstInput) *layoutConstTable {
	rows := make([]rowValues, 0, 2*len(consts))
	for _, c := range consts {
		rows = append(rows, rowValues{"vector." + c.Name, c.Vector})
		rows = append(rows, rowValues{"cell." + c.Name, c.Cell})
	}
	slices.SortStableFunc(rows, func(a, b rowValues) int {
		return cmp.Compare(a[0].(string), b[0].(string))
	})
	tbl := &table{name: "layoutconst", goName: "LayoutConst", rsName: "LAYOUT_CONST", leanName: "layoutconst", goType: "Const", rsType: "Const", leanType: "Const", leanOpaque: true, cols: layoutConstCols, rows: rows}
	return &layoutConstTable{table: tbl, consts: consts}
}

func buildScriptsTable(scripts []scriptInput) (*table, error) {
	rows := make([]rowValues, 0, len(scripts))
	for _, s := range scripts {
		base, err := parseGlyphRune(s.Base)
		if err != nil {
			return nil, fmt.Errorf("script base: %w", err)
		}
		sup, err := parseGlyphRune(s.Sup)
		if err != nil {
			return nil, fmt.Errorf("script sup: %w", err)
		}
		sub, err := parseGlyphRune(s.Sub)
		if err != nil {
			return nil, fmt.Errorf("script sub: %w", err)
		}
		rows = append(rows, rowValues{base, sup, sub})
	}
	slices.SortStableFunc(rows, func(a, b rowValues) int {
		return cmp.Compare(a[0].(uint32), b[0].(uint32))
	})
	return &table{name: "scripts", goName: "Scripts", rsName: "SCRIPTS", leanName: "scripts", goType: "Script", rsType: "Script", leanType: "Script", cols: scriptCols, rows: rows}, nil
}

func buildDiagnosticsTable(rows []registryRow) (*table, error) {
	values, err := diagnosticValues(rows)
	if err != nil {
		return nil, err
	}
	return &table{name: "diagnostics", goName: "Diagnostics", rsName: "DIAGNOSTICS", leanName: "diagnostics", goType: "Diagnostic", rsType: "Diagnostic", leanType: "Diagnostic", cols: registryCols, rows: values}, nil
}

func buildLintRulesTable(rows []registryRow) (*table, error) {
	values, err := lintRuleValues(rows)
	if err != nil {
		return nil, err
	}
	return &table{name: "lintrules", goName: "LintRules", rsName: "LINT_RULES", leanName: "lintrules", goType: "LintRule", rsType: "LintRule", leanType: "LintRule", cols: lintRuleCols, rows: values}, nil
}

func diagnosticValues(rows []registryRow) ([]rowValues, error) {
	values := make([]rowValues, 0, len(rows))
	for _, r := range rows {
		if err := validateDiagnosticRow(r); err != nil {
			return nil, fmt.Errorf("%s: %w", r.Code, err)
		}
		values = append(values, rowValues{r.Code, r.Severity, r.Summary, r.Help, r.Rationale, r.FixSafety, slices.Clone(r.Aliases)})
	}
	return values, nil
}

func lintRuleValues(rows []registryRow) ([]rowValues, error) {
	values := make([]rowValues, 0, len(rows))
	for _, r := range rows {
		if err := validateLintRuleRow(r); err != nil {
			return nil, fmt.Errorf("%s: %w", r.Code, err)
		}
		values = append(values, rowValues{r.Code, r.Severity, r.Summary, r.Help, r.Rationale, r.FixSafety, slices.Clone(r.Aliases), r.Source, r.Status, r.Reason})
	}
	return values, nil
}

func validateDiagnosticRow(r registryRow) error {
	if err := validateCommonRow(r); err != nil {
		return err
	}
	if !slices.Contains([]string{"error", "warning", "info"}, r.Severity) {
		return fmt.Errorf("unknown severity %q", r.Severity)
	}
	return nil
}

func validateLintRuleRow(r registryRow) error {
	if err := validateCommonRow(r); err != nil {
		return err
	}
	if !slices.Contains([]string{"error", "warning", "info", "off"}, r.Severity) {
		return fmt.Errorf("unknown severity %q", r.Severity)
	}
	if !slices.Contains([]string{"adopted", "rejected", ""}, r.Status) {
		return fmt.Errorf("unknown status %q", r.Status)
	}
	if r.Status == "rejected" && r.Reason == "" {
		return fmt.Errorf("rejected rule has no reason")
	}
	return nil
}

func validateCommonRow(r registryRow) error {
	if r.Code == "" {
		return fmt.Errorf("row has no code")
	}
	if !slices.Contains([]string{"none", "safe", "unsafe"}, r.FixSafety) {
		return fmt.Errorf("unknown fix_safety %q", r.FixSafety)
	}
	return nil
}

func buildShapesTable(shapes []shapeInput) (*table, error) {
	sorted := slices.Clone(shapes)
	slices.SortStableFunc(sorted, func(a, b shapeInput) int { return cmp.Compare(a.ID, b.ID) })
	rows := make([]rowValues, 0, len(sorted))
	for _, s := range sorted {
		corner, err := shapeCorner(s.Corner)
		if err != nil {
			return nil, fmt.Errorf("shape %q: %w", s.ID, err)
		}
		rows = append(rows, rowValues{s.ID, s.Family, corner, slices.Clone(s.Aliases)})
	}
	return &table{name: "shapes", goName: "Shapes", rsName: "SHAPES", leanName: "shapes", goType: "Shape", rsType: "Shape", leanType: "Shape", cols: shapeCols, rows: rows}, nil
}

func shapeCorner(corner string) (uint8, error) {
	switch corner {
	case "square":
		return 0, nil
	case "rounded":
		return 1, nil
	case "double":
		return 2, nil
	}
	return 0, fmt.Errorf("unknown corner %q", corner)
}

func buildMarkersTable(markers []markerInput) (*table, error) {
	sorted := slices.Clone(markers)
	slices.SortStableFunc(sorted, func(a, b markerInput) int { return cmp.Compare(a.Name, b.Name) })
	rows := make([]rowValues, 0, len(sorted))
	for _, m := range sorted {
		if err := validateMarkerOutline(m); err != nil {
			return nil, err
		}
		cell, err := parseUPlusList(m.Cell)
		if err != nil {
			return nil, fmt.Errorf("marker %q cell: %w", m.Name, err)
		}
		ascii, err := parseUPlusList(m.Ascii)
		if err != nil {
			return nil, fmt.Errorf("marker %q ascii: %w", m.Name, err)
		}
		rows = append(rows, rowValues{m.Name, m.Paint, cell, ascii, m.Points, m.Ref, m.Breaks})
	}
	return &table{name: "markers", goName: "Markers", rsName: "MARKERS", leanName: "markers", goType: "Marker", rsType: "Marker", leanType: "Marker", cols: markerCols, rows: rows}, nil
}

func parseUPlusList(items []string) ([]uint32, error) {
	out := make([]uint32, 0, len(items))
	for _, item := range items {
		v, err := parseGlyphRune(item)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}

func buildStylesTable(styles stylesInput) (*table, error) {
	rows := make([]rowValues, 0, len(styles.Shape)+len(styles.Text))
	for _, s := range styles.Shape {
		tint, err := styleTint(s.Tint)
		if err != nil {
			return nil, fmt.Errorf("style %q: %w", s.Name, err)
		}
		cell, err := styleCell(s.Cell)
		if err != nil {
			return nil, fmt.Errorf("style %q: %w", s.Name, err)
		}
		rows = append(rows, rowValues{s.Name, uint8(0), s.Fill, s.Stroke, tint, cell})
	}
	for _, s := range styles.Text {
		rows = append(rows, rowValues{s.Name, uint8(1), s.Colour, "none", uint8(0), uint8(0)})
	}
	slices.SortStableFunc(rows, func(a, b rowValues) int {
		return cmp.Compare(a[0].(string), b[0].(string))
	})
	return &table{name: "styles", goName: "Styles", rsName: "STYLES", leanName: "styles", goType: "Style", rsType: "Style", leanType: "Style", cols: styleCols, rows: rows}, nil
}

func styleTint(tint string) (uint8, error) {
	switch tint {
	case "none":
		return 0, nil
	case "fill":
		return 1, nil
	case "stroke":
		return 2, nil
	}
	return 0, fmt.Errorf("unknown tint %q", tint)
}

func styleCell(cell string) (uint8, error) {
	switch cell {
	case "none":
		return 0, nil
	case "line":
		return 1, nil
	case "fill":
		return 2, nil
	}
	return 0, fmt.Errorf("unknown cell rule %q", cell)
}

var strokeTokens = []string{
	"error", "warning", "success",
	"series0", "series1", "series2", "series3", "series4", "series5",
	"series6", "series7", "series8", "series9", "series10", "series11",
}

func buildSeriesTextTable(themes []themeInput, lin16 [lin16Entries]uint16) (*table, error) {
	rows := make([]rowValues, 0, len(themes)*12)
	for _, theme := range sortedThemes(themes) {
		fg, err := luminance(theme.Tokens["fg"], lin16)
		if err != nil {
			return nil, fmt.Errorf("theme %q fg: %w", theme.Name, err)
		}
		bg, err := luminance(theme.Tokens["bg"], lin16)
		if err != nil {
			return nil, fmt.Errorf("theme %q bg: %w", theme.Name, err)
		}
		for series := range 12 {
			hex, ok := theme.Tokens[fmt.Sprintf("series%d", series)]
			if !ok {
				return nil, fmt.Errorf("theme %q has no series%d token", theme.Name, series)
			}
			fill, err := luminance(hex, lin16)
			if err != nil {
				return nil, fmt.Errorf("theme %q series%d: %w", theme.Name, series, err)
			}
			rows = append(rows, rowValues{theme.Name, uint8(series), chooseSeriesText(fg, bg, fill)})
		}
	}
	return &table{name: "seriestext", goName: "SeriesText", rsName: "SERIES_TEXT", leanName: "seriestext", goType: "SeriesTextRow", rsType: "SeriesTextRow", leanType: "SeriesTextRow", cols: seriesTextCols, rows: rows}, nil
}

func chooseSeriesText(fg, bg, fill int64) uint8 {
	if contrastReaches(fg, fill, 45) && contrastCompare(fg, bg, fill) > 0 {
		return 0
	}
	if contrastReaches(bg, fill, 45) && contrastCompare(bg, fg, fill) > 0 {
		return 1
	}
	return 2
}

func buildStrokeOkTable(themes []themeInput, lin16 [lin16Entries]uint16) (*table, error) {
	tokens := slices.Clone(strokeTokens)
	slices.Sort(tokens)
	rows := make([]rowValues, 0, len(themes)*len(tokens))
	for _, theme := range sortedThemes(themes) {
		themeRows, err := strokeOkRows(theme, tokens, lin16)
		if err != nil {
			return nil, err
		}
		rows = append(rows, themeRows...)
	}
	return &table{name: "strokeok", goName: "StrokeOk", rsName: "STROKE_OK", leanName: "strokeok", goType: "StrokeOkRow", rsType: "StrokeOkRow", leanType: "StrokeOkRow", cols: strokeOkCols, rows: rows}, nil
}

func strokeOkRows(theme themeInput, tokens []string, lin16 [lin16Entries]uint16) ([]rowValues, error) {
	bg, err := luminance(theme.Tokens["bg"], lin16)
	if err != nil {
		return nil, fmt.Errorf("theme %q bg: %w", theme.Name, err)
	}
	surface, err := luminance(theme.Tokens["surface"], lin16)
	if err != nil {
		return nil, fmt.Errorf("theme %q surface: %w", theme.Name, err)
	}
	rows := make([]rowValues, 0, len(tokens))
	for _, token := range tokens {
		okValue, err := strokeOkValue(theme, token, bg, surface, lin16)
		if err != nil {
			return nil, err
		}
		rows = append(rows, rowValues{theme.Name, token, okValue})
	}
	return rows, nil
}

func strokeOkValue(theme themeInput, token string, bg, surface int64, lin16 [lin16Entries]uint16) (uint8, error) {
	hex, ok := theme.Tokens[token]
	if !ok {
		return 0, fmt.Errorf("theme %q has no %q token", theme.Name, token)
	}
	y, err := luminance(hex, lin16)
	if err != nil {
		return 0, fmt.Errorf("theme %q token %q: %w", theme.Name, token, err)
	}
	if contrastReaches(y, bg, 30) && contrastReaches(y, surface, 30) {
		return 1, nil
	}
	return 0, nil
}

func sortedThemes(themes []themeInput) []themeInput {
	out := slices.Clone(themes)
	slices.SortStableFunc(out, func(a, b themeInput) int { return cmp.Compare(a.Name, b.Name) })
	return out
}

func buildCellSymbolsTable(symbols []cellSymbolInput) (*table, error) {
	sorted := slices.Clone(symbols)
	slices.SortStableFunc(sorted, func(a, b cellSymbolInput) int { return cmp.Compare(a.Name, b.Name) })
	rows := make([]rowValues, 0, len(sorted))
	for _, s := range sorted {
		unicode, err := parseGlyphRune(s.Unicode)
		if err != nil {
			return nil, fmt.Errorf("symbol %q unicode: %w", s.Name, err)
		}
		ascii, err := parseGlyphRune(s.Ascii)
		if err != nil {
			return nil, fmt.Errorf("symbol %q ascii: %w", s.Name, err)
		}
		rows = append(rows, rowValues{s.Name, unicode, ascii})
	}
	return &table{name: "cellsymbols", goName: "CellSymbols", rsName: "CELL_SYMBOLS", leanName: "cellsymbols", goType: "Symbol", rsType: "Symbol", leanType: "Symbol", cols: symbolCols, rows: rows}, nil
}

func buildThemesTable(themes []themeInput) *table {
	rows := make([]rowValues, 0, len(themes))
	for _, theme := range sortedThemes(themes) {
		names := slices.Sorted(maps.Keys(theme.Tokens))
		tokens := make([][]any, 0, len(names))
		for _, name := range names {
			tokens = append(tokens, []any{name, theme.Tokens[name]})
		}
		rows = append(rows, rowValues{theme.Name, tokens})
	}
	return &table{name: "themes", goName: "Themes", rsName: "THEMES", leanName: "themes", goType: "Theme", rsType: "Theme", leanType: "Theme", cols: themeCols, rows: rows}
}

func buildConfigKeysTable(keys []configKeyInput) *table {
	sorted := slices.Clone(keys)
	slices.SortStableFunc(sorted, func(a, b configKeyInput) int {
		return cmp.Or(cmp.Compare(a.Kind, b.Kind), cmp.Compare(a.Key, b.Key))
	})
	rows := make([]rowValues, 0, len(sorted))
	for _, k := range sorted {
		rows = append(rows, rowValues{k.Kind, k.Key, k.Class})
	}
	return &table{name: "configkeys", goName: "ConfigKeys", rsName: "CONFIG_KEYS", leanName: "configkeys", goType: "ConfigKey", rsType: "ConfigKey", leanType: "ConfigKey", cols: configKeyCols, rows: rows}
}

func buildEntitiesTable(entities []entityRow) *table {
	rows := make([]rowValues, 0, len(entities))
	for _, e := range entities {
		rows = append(rows, rowValues{e.Name, e.CPS})
	}
	return &table{name: "entities", goName: "Entities", rsName: "ENTITIES", leanName: "entities", goType: "Entity", rsType: "Entity", leanType: "Entity", cols: entityCols, rows: rows}
}
