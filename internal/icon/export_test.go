package icon

func UnknownGlyphRows() [][5]int32 {
	rows := make([][5]int32, len(unknownGlyph))
	for i, c := range unknownGlyph {
		rows[i] = [5]int32{int32(c.op), c.x1, c.y1, c.x2, c.y2}
	}
	return rows
}
