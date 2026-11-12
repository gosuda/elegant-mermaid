package main

import (
	"cmp"
	"fmt"
	"math/big"
)

const lin16Entries = 256

const lin16ScaleDigits = 40

const gammaExponentDigits = lin16ScaleDigits * 12 / 5

const gammaResultDigits = gammaExponentDigits - lin16ScaleDigits

func lin16Table() ([lin16Entries]uint16, error) {
	var table [lin16Entries]uint16
	scale := pow10(lin16ScaleDigits)
	for c := range lin16Entries {
		v, err := lin16Entry(c, scale)
		if err != nil {
			return table, err
		}
		table[c] = v
	}
	return table, nil
}

func lin16Entry(channel int, scale *big.Int) (uint16, error) {
	u := new(big.Int).Quo(new(big.Int).Mul(big.NewInt(int64(channel)), scale), big.NewInt(255))
	f := linearise(u, scale)
	scaled := new(big.Int).Mul(f, big.NewInt(65535))
	rounded := roundHalfUp(scaled, scale)
	if !rounded.IsUint64() || rounded.Uint64() > 65535 {
		return 0, fmt.Errorf("channel %d out of range: %s", channel, rounded)
	}
	return uint16(rounded.Uint64()), nil
}

func linearise(u, scale *big.Int) *big.Int {
	threshold := new(big.Int).Quo(new(big.Int).Mul(big.NewInt(4045), scale), big.NewInt(100000))
	if u.Cmp(threshold) <= 0 {
		return new(big.Int).Quo(new(big.Int).Mul(u, big.NewInt(100)), big.NewInt(1292))
	}
	offset := new(big.Int).Quo(new(big.Int).Mul(big.NewInt(55), scale), big.NewInt(1000))
	t := new(big.Int).Add(u, offset)
	t.Mul(t, big.NewInt(1000))
	t.Quo(t, big.NewInt(1055))
	return powTwelveFifths(t)
}

func powTwelveFifths(t *big.Int) *big.Int {
	root := integerRoot(new(big.Int).Exp(t, big.NewInt(12), nil), 5)
	return root.Quo(root, pow10(gammaResultDigits))
}

func integerRoot(n *big.Int, k int) *big.Int {
	if n.Sign() == 0 {
		return big.NewInt(0)
	}
	lo := big.NewInt(0)
	hi := new(big.Int).Lsh(big.NewInt(1), uint((n.BitLen()+k-1)/k+1))
	exponent := big.NewInt(int64(k))
	mid := new(big.Int)
	pow := new(big.Int)
	for lo.Cmp(hi) < 0 {
		mid.Add(lo, hi)
		mid.Add(mid, big.NewInt(1))
		mid.Rsh(mid, 1)
		pow.Exp(mid, exponent, nil)
		if pow.Cmp(n) <= 0 {
			lo.Set(mid)
		} else {
			hi.Set(mid)
			hi.Sub(hi, big.NewInt(1))
		}
	}
	return lo
}

func roundHalfUp(value, scale *big.Int) *big.Int {
	half := new(big.Int).Rsh(scale, 1)
	shifted := new(big.Int).Add(value, half)
	return shifted.Quo(shifted, scale)
}

func hexToLin16(hex string, table [lin16Entries]uint16) ([3]int64, error) {
	var rgb [3]int64
	if len(hex) != 7 || hex[0] != '#' {
		return rgb, fmt.Errorf("bad colour %q", hex)
	}
	for i := range 3 {
		v, err := parseHexByte(hex[1+2*i : 3+2*i])
		if err != nil {
			return rgb, err
		}
		rgb[i] = int64(table[v])
	}
	return rgb, nil
}

func parseHexByte(s string) (int, error) {
	v, err := parseHexCodePoint(s)
	if err != nil || v > 0xFF {
		return 0, fmt.Errorf("bad hex byte %q", s)
	}
	return int(v), nil
}

func luminance(hex string, table [lin16Entries]uint16) (int64, error) {
	rgb, err := hexToLin16(hex, table)
	if err != nil {
		return 0, err
	}
	return (2126*rgb[0] + 7152*rgb[1] + 722*rgb[2]) / 10000, nil
}

func contrastReaches(a, b, tenths int64) bool {
	hi, lo := max(a, b), min(a, b)
	return 10*(hi+3277) >= tenths*(lo+3277)
}

func contrastCompare(a, b, fill int64) int {
	numA, denA := ratioAround(a, fill)
	numB, denB := ratioAround(b, fill)
	return cmp.Compare(numA*denB, numB*denA)
}

func ratioAround(x, fill int64) (int64, int64) {
	return max(x, fill) + 3277, min(x, fill) + 3277
}
