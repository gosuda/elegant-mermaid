package main

import (
	"errors"
	"fmt"
	"math/big"
)

const sineEntries = 1025

const sineScaleDigits = 60

const piSixtyDigits = "3141592653589793238462643383279502884197169399375105820974944"

const sineHalfToleranceDigits = 30

var errSineAmbiguous = errors.New("sine value within 1e-30 of a half-integer")

func sineTable() ([sineEntries]int32, error) {
	var table [sineEntries]int32
	scale := pow10(sineScaleDigits)
	scaleSquared := new(big.Int).Mul(scale, scale)
	pi, ok := new(big.Int).SetString(piSixtyDigits, 10)
	if !ok {
		return table, errors.New("pi constant is not an integer")
	}
	for i := range sineEntries {
		v, err := sineEntry(pi, scale, scaleSquared, i)
		if err != nil {
			return table, err
		}
		table[i] = v
	}
	return table, nil
}

func sineEntry(pi, scale, scaleSquared *big.Int, index int) (int32, error) {
	arg := new(big.Int).Mul(pi, big.NewInt(int64(index)))
	arg.Quo(arg, big.NewInt(2048))
	sin := taylorSine(arg, scaleSquared)
	scaled := new(big.Int).Mul(sin, big.NewInt(32768))
	rounded, err := roundHalfUpDiv(scaled, scale)
	if err != nil {
		return 0, fmt.Errorf("entry %d: %w", index, err)
	}
	if !rounded.IsInt64() || rounded.Int64() > 32768 || rounded.Int64() < -32768 {
		return 0, fmt.Errorf("entry %d out of range: %s", index, rounded)
	}
	return int32(rounded.Int64()), nil
}

func taylorSine(x, scaleSquared *big.Int) *big.Int {
	sum := new(big.Int).Set(x)
	xSquared := new(big.Int).Mul(x, x)
	term := new(big.Int).Set(x)
	for k := 1; ; k++ {
		term = nextSineTerm(term, xSquared, scaleSquared, k)
		if term.Sign() == 0 {
			return sum
		}
		if k%2 == 1 {
			sum.Sub(sum, term)
		} else {
			sum.Add(sum, term)
		}
	}
}

func nextSineTerm(term, xSquared, scaleSquared *big.Int, k int) *big.Int {
	next := new(big.Int).Mul(term, xSquared)
	next.Quo(next, scaleSquared)
	next.Quo(next, big.NewInt(int64(2*k*(2*k+1))))
	return next
}

func roundHalfUpDiv(value, scale *big.Int) (*big.Int, error) {
	half := new(big.Int).Rsh(scale, 1)
	frac := new(big.Int).Rem(new(big.Int).Abs(value), scale)
	spread := new(big.Int).Sub(frac, half)
	spread.Abs(spread)
	scaled := new(big.Int).Mul(spread, pow10(sineHalfToleranceDigits))
	if scaled.Cmp(scale) < 0 {
		return nil, errSineAmbiguous
	}
	shifted := new(big.Int).Add(value, half)
	return shifted.Quo(shifted, scale), nil
}

func pow10(digits int) *big.Int {
	return new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(digits)), nil)
}
