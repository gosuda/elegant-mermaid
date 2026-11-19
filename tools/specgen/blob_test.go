package main

import (
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func decodeBlob(t *testing.T, tbl *table, blob string) []rowValues {
	t.Helper()
	var rows []rowValues
	for line := range strings.SplitSeq(blob, string(leanRowSep)) {
		fields := strings.Split(line, string(leanFieldSep))
		require.Len(t, fields, len(tbl.cols), "field count in %q", line)
		row := make(rowValues, len(tbl.cols))
		for i, c := range tbl.cols {
			row[i] = decodeBlobCell(t, c, fields[i])
		}
		rows = append(rows, row)
	}
	return rows
}

func decodeBlobCell(t *testing.T, c col, cell string) any {
	t.Helper()
	switch c.kind {
	case colString:
		return unescapeBlobField(t, cell)
	case colU8:
		n, err := strconv.ParseUint(cell, 10, 8)
		require.NoError(t, err)
		return uint8(n)
	case colU16:
		n, err := strconv.ParseUint(cell, 10, 16)
		require.NoError(t, err)
		return uint16(n)
	case colU32:
		n, err := strconv.ParseUint(cell, 10, 32)
		require.NoError(t, err)
		return uint32(n)
	case colI32:
		n, err := strconv.ParseInt(cell, 10, 32)
		require.NoError(t, err)
		return int32(n)
	case colBool:
		return cell == "true"
	case colU32List:
		parsed := []uint32{}
		for item := range strings.SplitSeq(cell, string(leanItemSep)) {
			if item == "" {
				continue
			}
			n, err := strconv.ParseUint(item, 10, 32)
			require.NoError(t, err)
			parsed = append(parsed, uint32(n))
		}
		return parsed
	}
	t.Fatalf("column kind %d is not decodable from text", c.kind)
	return nil
}

func unescapeBlobField(t *testing.T, s string) string {
	t.Helper()
	var b strings.Builder
	for i := 0; i < len(s); i++ {
		if s[i] != '%' {
			b.WriteByte(s[i])
			continue
		}
		require.LessOrEqual(t, i+3, len(s), "truncated percent escape in %q", s)
		value, err := strconv.ParseUint(s[i+1:i+3], 16, 8)
		require.NoError(t, err, "bad percent escape in %q", s)
		b.WriteByte(byte(value))
		i += 2
	}
	return b.String()
}

func TestLeanTextBlobRoundTrips(t *testing.T) {
	cases := []*table{
		{name: "advance", leanName: "advances", goType: "Advance", cols: advanceCols, rows: []rowValues{
			{uint8(0), uint32(32), uint16(1413)},
			{uint8(1), uint32(32), uint16(1490)},
		}},
		{name: "entities", leanName: "entities", goType: "Entity", cols: entityCols, rows: []rowValues{
			{"amp;", []uint32{38}},
			{"NotEqualTilde;", []uint32{8770, 824}},
		}},
		{name: "tricky", leanName: "tricky", goType: "Tricky", cols: []col{
			{leanName: "text", kind: colString},
			{leanName: "items", kind: colU32List},
		}, rows: []rowValues{
			{"a|b;c,d% \\e\nf\tg", []uint32{1, 2, 3}},
			{"😀 日本", []uint32{}},
			{"", []uint32{}},
		}},
	}
	for _, tbl := range cases {
		require.True(t, tbl.leanDecodable(), tbl.name)
		blob, err := tbl.leanTextBlob()
		require.NoError(t, err, tbl.name)
		require.Equal(t, tbl.rows, decodeBlob(t, tbl, blob), tbl.name)
	}
}
