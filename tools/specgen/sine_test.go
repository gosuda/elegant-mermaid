package main

import (
	"math"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSineTableAnchors(t *testing.T) {
	table, err := sineTable()
	require.NoError(t, err)
	require.Equal(t, int32(0), table[0])
	require.Equal(t, int32(32768), table[1024])
	require.Equal(t, int32(23170), table[512])
}

func TestSineTableMonotone(t *testing.T) {
	table, err := sineTable()
	require.NoError(t, err)
	for i := 1; i < len(table); i++ {
		require.LessOrEqual(t, table[i-1], table[i], "entry %d", i)
	}
}

func TestSineTableAgainstMathSin(t *testing.T) {
	table, err := sineTable()
	require.NoError(t, err)
	for i := range table {
		angle := math.Pi * float64(i) / 2048
		want := 32768 * math.Sin(angle)
		require.InDelta(t, want, float64(table[i]), 1.0, "entry %d", i)
	}
}
