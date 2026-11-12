package main

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
)

func dataRoot(t *testing.T) string {
	t.Helper()
	root, err := filepath.Abs(filepath.Join("..", ".."))
	require.NoError(t, err)
	if _, err := os.Stat(filepath.Join(root, "spec", "data")); err != nil {
		t.Skipf("spec/data is absent: %v", err)
	}
	return root
}

func loadUCDBytes(t *testing.T, root, name string) []byte {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(root, "spec", "data", "unicode", name))
	if err != nil {
		t.Skipf("%s is absent: %v", name, err)
	}
	return data
}

func naiveWidth(t *testing.T, eaw, emoji, gbp []byte) func(uint32) uint8 {
	t.Helper()
	widths := newScalarArray(1)
	for _, line := range mustUCD(t, eaw) {
		if isWideEastAsian(line.field(1)) {
			assignRange(widths, line.lo, line.hi, 2)
		}
	}
	for _, line := range mustUCD(t, emoji) {
		if line.field(1) == "Emoji_Presentation" {
			assignRange(widths, line.lo, line.hi, 2)
		}
	}
	for _, line := range mustUCD(t, gbp) {
		if prop, ok := graphemeProps[line.field(1)]; ok && (prop == propExtend || prop == propZWJ) {
			assignRange(widths, line.lo, line.hi, 0)
		}
	}
	return func(cp uint32) uint8 { return widths[cp] }
}

func mustUCD(t *testing.T, data []byte) []ucdLine {
	t.Helper()
	lines, err := parseUCD(data)
	require.NoError(t, err)
	return lines
}

func TestUnicodeWidthMatchesNaiveExpansion(t *testing.T) {
	root := dataRoot(t)
	eaw := loadUCDBytes(t, root, "EastAsianWidth.txt")
	emoji := loadUCDBytes(t, root, "emoji-data.txt")
	gbp := loadUCDBytes(t, root, "GraphemeBreakProperty.txt")
	merged, err := buildUnicodeWidth(map[string][]byte{
		"EastAsianWidth.txt":        eaw,
		"emoji-data.txt":            emoji,
		"GraphemeBreakProperty.txt": gbp,
	})
	require.NoError(t, err)
	naive := naiveWidth(t, eaw, emoji, gbp)
	require.Equal(t, uint8(1), lookupRange(merged, 0x41))
	require.Equal(t, uint8(2), lookupRange(merged, 0x4E00))
	require.Equal(t, uint8(0), lookupRange(merged, 0x0301))
	for cp := uint32(0); cp <= maxScalar; cp += 37 {
		require.Equal(t, naive(cp), lookupRange(merged, cp), "scalar U+%04X", cp)
	}
}

func TestRangesAreDisjointAndMerged(t *testing.T) {
	root := dataRoot(t)
	merged, err := buildUnicodeWidth(map[string][]byte{
		"EastAsianWidth.txt":        loadUCDBytes(t, root, "EastAsianWidth.txt"),
		"emoji-data.txt":            loadUCDBytes(t, root, "emoji-data.txt"),
		"GraphemeBreakProperty.txt": loadUCDBytes(t, root, "GraphemeBreakProperty.txt"),
	})
	require.NoError(t, err)
	require.Equal(t, uint32(0), merged[0].Lo)
	require.Equal(t, uint32(maxScalar), merged[len(merged)-1].Hi)
	for i := 1; i < len(merged); i++ {
		require.Equal(t, merged[i-1].Hi+1, merged[i].Lo, "gap or overlap at %d", i)
		require.NotEqual(t, merged[i-1].Val, merged[i].Val, "unmerged pair at %d", i)
	}
}

func TestGraphemesSparseAndDisjoint(t *testing.T) {
	root := dataRoot(t)
	ranges, err := buildGraphemes(loadUCDBytes(t, root, "GraphemeBreakProperty.txt"), loadUCDBytes(t, root, "emoji-data.txt"))
	require.NoError(t, err)
	require.NotEmpty(t, ranges)
	for i, r := range ranges {
		require.NotEqual(t, uint8(0), r.Val, "row %d has the implicit zero value", i)
	}
	for i := 1; i < len(ranges); i++ {
		previous, current := ranges[i-1], ranges[i]
		require.Greater(t, current.Lo, previous.Hi, "overlap at %d", i)
		if current.Lo == previous.Hi+1 {
			require.NotEqual(t, previous.Val, current.Val, "unmerged adjacent pair at %d", i)
		}
	}
	require.Equal(t, uint8(propExtendedPictograph), lookupRange(ranges, 0x00A9))
	require.Equal(t, uint8(propExtend), lookupRange(ranges, 0x0301))
	require.Equal(t, uint8(0), lookupRange(ranges, 'A'))
}

func TestIncbAndIdeographic(t *testing.T) {
	root := dataRoot(t)
	incb, err := buildIncb(loadUCDBytes(t, root, "DerivedCoreProperties.txt"))
	require.NoError(t, err)
	require.Equal(t, uint8(1), lookupRange(incb, 0x094D))
	ideographic, err := buildIdeographic(loadUCDBytes(t, root, "PropList.txt"))
	require.NoError(t, err)
	require.Equal(t, uint8(1), lookupRange(ideographic, 0x4E00))
	require.Equal(t, uint8(0), lookupRange(ideographic, 'A'))
}
