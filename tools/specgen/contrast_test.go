package main

import (
	"math"
	"testing"

	"github.com/stretchr/testify/require"
)

const slate1 = "#fcfcfd"

func lin16Float(channel int) uint16 {
	u := float64(channel) / 255
	f := u / 12.92
	if u > 0.04045 {
		f = math.Pow((u+0.055)/1.055, 2.4)
	}
	return uint16(math.Floor(65535*f + 0.5))
}

func TestLin16Endpoints(t *testing.T) {
	table, err := lin16Table()
	require.NoError(t, err)
	require.Equal(t, uint16(0), table[0])
	require.Equal(t, uint16(65535), table[255])
}

func TestLin16MonotoneAndCloseToFloat(t *testing.T) {
	table, err := lin16Table()
	require.NoError(t, err)
	for c := 1; c < len(table); c++ {
		require.LessOrEqual(t, table[c-1], table[c], "channel %d", c)
	}
	for c := range table {
		want := lin16Float(c)
		require.InDelta(t, float64(want), float64(table[c]), 1, "channel %d", c)
	}
}

func TestLuminanceAndContrastOnPublishedRatios(t *testing.T) {
	table, err := lin16Table()
	require.NoError(t, err)
	background, err := luminance(slate1, table)
	require.NoError(t, err)
	errorColour, err := luminance("#ca244d", table)
	require.NoError(t, err)
	require.True(t, contrastReaches(errorColour, background, 45), "ruby11 on slate1 must reach 4.5:1")
	warningColour, err := luminance("#ab6400", table)
	require.NoError(t, err)
	require.False(t, contrastReaches(warningColour, background, 45), "amber11 on slate1 must miss 4.5:1")
	require.True(t, contrastReaches(warningColour, background, 30), "amber11 on slate1 must reach 3:1")
}

func TestContrastReachesMatchesFloatRatio(t *testing.T) {
	table, err := lin16Table()
	require.NoError(t, err)
	pairs := [][2]string{
		{"#ca244d", slate1},
		{"#ab6400", slate1},
		{"#2a7e3b", slate1},
		{"#fbfdff", "#1d1d1d"},
		{"#ffca16", "#1d1d1d"},
	}
	for _, pair := range pairs {
		a, err := luminance(pair[0], table)
		require.NoError(t, err)
		b, err := luminance(pair[1], table)
		require.NoError(t, err)
		ratio := float64(max(a, b)+3277) / float64(min(a, b)+3277)
		for _, tenths := range []float64{30, 45} {
			want := ratio >= tenths/10
			require.Equal(t, want, contrastReaches(a, b, int64(tenths)), "%s on %s at %.1f", pair[0], pair[1], tenths/10)
		}
	}
}

func TestSeriesTextChoice(t *testing.T) {
	require.Equal(t, uint8(2), chooseSeriesText(100, 100, 40000), "neither label reaches 4.5:1 on a dark fill")
	require.Equal(t, uint8(1), chooseSeriesText(60000, 1000, 30000), "bg wins when both reach and bg contrasts more")
	require.Equal(t, uint8(0), chooseSeriesText(1000, 60000, 30000), "fg wins when both reach and fg contrasts more")
	require.Equal(t, uint8(0), chooseSeriesText(100, 60000, 30000), "fg wins when only fg reaches")
	require.Equal(t, uint8(2), chooseSeriesText(60000, 60000, 1000), "tied labels fall to plate")
}

func TestRhoQ30(t *testing.T) {
	rho := rhoQ30()
	require.Equal(t, int64(1737350766), rho)
}
