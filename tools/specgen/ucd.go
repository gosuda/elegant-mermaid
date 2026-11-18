package main

import (
	"bytes"
	"fmt"
	"slices"
	"strconv"
	"strings"
)

const maxScalar = 0x10FFFF

type ucdLine struct {
	lo     uint32
	hi     uint32
	fields []string
}

func (l ucdLine) field(i int) string {
	if i < len(l.fields) {
		return l.fields[i]
	}
	return ""
}

func parseUCD(data []byte) ([]ucdLine, error) {
	lines := make([]ucdLine, 0, 4096)
	for raw := range strings.SplitSeq(string(data), "\n") {
		if idx := strings.IndexByte(raw, '#'); idx >= 0 {
			raw = raw[:idx]
		}
		raw = strings.TrimSpace(raw)
		if raw == "" {
			continue
		}
		fields := strings.Split(raw, ";")
		for i := range fields {
			fields[i] = strings.TrimSpace(fields[i])
		}
		lo, hi, err := parseUCDRange(fields[0])
		if err != nil {
			return nil, err
		}
		lines = append(lines, ucdLine{lo: lo, hi: hi, fields: fields})
	}
	return lines, nil
}

func parseUCDRange(s string) (uint32, uint32, error) {
	loStr, hiStr, found := strings.Cut(s, "..")
	lo, err := parseHexCodePoint(loStr)
	if err != nil {
		return 0, 0, err
	}
	if !found {
		return lo, lo, nil
	}
	hi, err := parseHexCodePoint(hiStr)
	if err != nil {
		return 0, 0, err
	}
	if hi < lo {
		return 0, 0, fmt.Errorf("inverted range %q", s)
	}
	return lo, hi, nil
}

func parseHexCodePoint(s string) (uint32, error) {
	v, err := strconv.ParseUint(strings.TrimSpace(s), 16, 32)
	if err != nil {
		return 0, fmt.Errorf("bad code point %q: %w", s, err)
	}
	if v > maxScalar {
		return 0, fmt.Errorf("code point %q above U+10FFFF", s)
	}
	return uint32(v), nil
}

type tableRange struct {
	Lo  uint32
	Hi  uint32
	Val uint8
}

func newScalarArray(v uint8) []uint8 {
	vals := make([]uint8, maxScalar+1)
	if v != 0 {
		for i := range vals {
			vals[i] = v
		}
	}
	return vals
}

func assignRange(vals []uint8, lo, hi uint32, v uint8) {
	for i := lo; i <= hi && i <= maxScalar; i++ {
		vals[i] = v
	}
}

func compressFull(vals []uint8) []tableRange {
	ranges := make([]tableRange, 0, 512)
	start := uint32(0)
	for i := uint32(1); i <= maxScalar; i++ {
		if vals[i] == vals[start] {
			continue
		}
		ranges = append(ranges, tableRange{Lo: start, Hi: i - 1, Val: vals[start]})
		start = i
	}
	return append(ranges, tableRange{Lo: start, Hi: maxScalar, Val: vals[start]})
}

func compressSparse(vals []uint8) []tableRange {
	ranges := make([]tableRange, 0, 512)
	i := uint32(0)
	for i <= maxScalar {
		if vals[i] == 0 {
			i++
			continue
		}
		start := i
		for i <= maxScalar && vals[i] == vals[start] {
			i++
		}
		ranges = append(ranges, tableRange{Lo: start, Hi: i - 1, Val: vals[start]})
	}
	return ranges
}

var graphemeProps = map[string]uint8{
	"CR": 1, "LF": 2, "Control": 3, "Extend": 4, "ZWJ": 5,
	"Regional_Indicator": 6, "Prepend": 7, "SpacingMark": 8,
	"L": 9, "V": 10, "T": 11, "LV": 12, "LVT": 13,
}

const (
	propExtend             = uint8(4)
	propZWJ                = uint8(5)
	propExtendedPictograph = uint8(14)
)

var incbProps = map[string]uint8{"Linker": 1, "Consonant": 2, "Extend": 3}

type widthPass struct {
	file  string
	value uint8
	match func(field string) bool
}

var widthPasses = []widthPass{
	{"EastAsianWidth.txt", 2, isWideEastAsian},
	{"emoji-data.txt", 2, func(field string) bool { return field == "Emoji_Presentation" }},
	{"GraphemeBreakProperty.txt", 0, isZeroWidthGrapheme},
}

func isZeroWidthGrapheme(field string) bool {
	prop, ok := graphemeProps[field]
	return ok && (prop == propExtend || prop == propZWJ)
}

func buildUnicodeWidth(files map[string][]byte) ([]tableRange, error) {
	vals := newScalarArray(1)
	for _, pass := range widthPasses {
		if err := applyWidthPass(vals, pass, files[pass.file]); err != nil {
			return nil, err
		}
	}
	return compressFull(vals), nil
}

func applyWidthPass(vals []uint8, pass widthPass, data []byte) error {
	lines, err := parseUCD(data)
	if err != nil {
		return fmt.Errorf("%s: %w", pass.file, err)
	}
	for _, line := range lines {
		if pass.match(line.field(1)) {
			assignRange(vals, line.lo, line.hi, pass.value)
		}
	}
	return nil
}

func isWideEastAsian(s string) bool {
	return s == "W" || s == "F"
}

func buildGraphemes(gbp, emoji []byte) ([]tableRange, error) {
	vals := newScalarArray(0)
	gbpLines, err := parseUCD(gbp)
	if err != nil {
		return nil, fmt.Errorf("GraphemeBreakProperty.txt: %w", err)
	}
	for _, line := range gbpLines {
		prop, ok := graphemeProps[line.field(1)]
		if !ok {
			return nil, fmt.Errorf("unknown Grapheme_Cluster_Break value %q", line.field(1))
		}
		if err := assignGrapheme(vals, line.lo, line.hi, prop); err != nil {
			return nil, err
		}
	}
	emojiLines, err := parseUCD(emoji)
	if err != nil {
		return nil, fmt.Errorf("emoji-data.txt: %w", err)
	}
	for _, line := range emojiLines {
		if line.field(1) != "Extended_Pictographic" {
			continue
		}
		if err := assignGrapheme(vals, line.lo, line.hi, propExtendedPictograph); err != nil {
			return nil, err
		}
	}
	return compressSparse(vals), nil
}

func assignGrapheme(vals []uint8, lo, hi uint32, prop uint8) error {
	for i := lo; i <= hi && i <= maxScalar; i++ {
		if vals[i] != 0 && vals[i] != prop {
			return fmt.Errorf("scalar U+%04X carries two grapheme classes", i)
		}
		vals[i] = prop
	}
	return nil
}

func buildIncb(derived []byte) ([]tableRange, error) {
	vals := newScalarArray(0)
	lines, err := parseUCD(derived)
	if err != nil {
		return nil, fmt.Errorf("DerivedCoreProperties.txt: %w", err)
	}
	for _, line := range lines {
		if line.field(1) != "InCB" {
			continue
		}
		prop, ok := incbProps[line.field(2)]
		if !ok {
			return nil, fmt.Errorf("unknown InCB value %q", line.field(2))
		}
		assignRange(vals, line.lo, line.hi, prop)
	}
	return compressSparse(vals), nil
}

func buildIdeographic(propList []byte) ([]tableRange, error) {
	vals := newScalarArray(0)
	lines, err := parseUCD(propList)
	if err != nil {
		return nil, fmt.Errorf("PropList.txt: %w", err)
	}
	for _, line := range lines {
		if line.field(1) == "Ideographic" {
			assignRange(vals, line.lo, line.hi, 1)
		}
	}
	return compressSparse(vals), nil
}

func buildAlphanumeric(derived, generalCategory []byte) ([]tableRange, error) {
	if len(bytes.TrimSpace(derived)) == 0 {
		return nil, fmt.Errorf("DerivedCoreProperties.txt: required source is missing or empty")
	}
	if len(bytes.TrimSpace(generalCategory)) == 0 {
		return nil, fmt.Errorf("DerivedGeneralCategory.txt: required source is missing or empty")
	}
	vals := newScalarArray(0)
	if err := assignAlphanumeric(vals, derived, "DerivedCoreProperties.txt", []string{"Alphabetic"}); err != nil {
		return nil, err
	}
	if err := assignAlphanumeric(vals, generalCategory, "DerivedGeneralCategory.txt", []string{"Nd", "Nl", "No"}); err != nil {
		return nil, err
	}
	return compressSparse(vals), nil
}

func assignAlphanumeric(vals []uint8, data []byte, name string, properties []string) error {
	lines, err := parseUCD(data)
	if err != nil {
		return fmt.Errorf("%s: %w", name, err)
	}
	for _, line := range lines {
		if slices.Contains(properties, line.field(1)) {
			assignRange(vals, line.lo, line.hi, 1)
		}
	}
	return nil
}

func lookupRange(ranges []tableRange, cp uint32) uint8 {
	idx, found := slices.BinarySearchFunc(ranges, cp, func(r tableRange, target uint32) int {
		switch {
		case r.Hi < target:
			return -1
		case r.Lo > target:
			return 1
		}
		return 0
	})
	if !found {
		return 0
	}
	return ranges[idx].Val
}
