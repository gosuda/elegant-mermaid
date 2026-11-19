package main

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestPiConstantMatchesMachin(t *testing.T) {
	require.Equal(t, machinPi(60), piSixtyDigits)
}

func TestPiConstantHasSixtyDecimals(t *testing.T) {
	require.Len(t, piSixtyDigits, 61)
	require.Equal(t, byte('3'), piSixtyDigits[0])
}

func machinPi(digits int) string {
	one := pow10(digits + 20)
	pi := new(big.Int).Mul(atanInverse(5, one), big.NewInt(16))
	pi.Sub(pi, new(big.Int).Mul(atanInverse(239, one), big.NewInt(4)))
	return new(big.Int).Quo(pi, pow10(20)).String()
}

func atanInverse(x int64, one *big.Int) *big.Int {
	bigX := big.NewInt(x)
	term := new(big.Int).Quo(one, bigX)
	total := new(big.Int).Set(term)
	xSquared := new(big.Int).Mul(bigX, bigX)
	divisor := big.NewInt(1)
	negative := true
	for term.Sign() != 0 {
		term.Quo(term, xSquared)
		divisor.Add(divisor, big.NewInt(2))
		contribution := new(big.Int).Quo(new(big.Int).Set(term), divisor)
		if negative {
			total.Sub(total, contribution)
		} else {
			total.Add(total, contribution)
		}
		negative = !negative
	}
	return total
}

func TestRoundHalfUpDivRejectsHalfInteger(t *testing.T) {
	scale := pow10(6)
	half := new(big.Int).Mul(big.NewInt(5), pow10(5))
	_, err := roundHalfUpDiv(half, scale)
	require.ErrorIs(t, err, errSineAmbiguous)
	clearOfHalf := new(big.Int).Add(half, pow10(4))
	got, err := roundHalfUpDiv(clearOfHalf, scale)
	require.NoError(t, err)
	require.Equal(t, int64(1), got.Int64())
}
