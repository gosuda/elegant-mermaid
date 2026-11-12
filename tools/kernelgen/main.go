package main

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
)

const (
	coordLow  int32 = -1000
	coordHigh int32 = 1000
	sizeLow   int32 = -5
	sizeHigh  int32 = 500
	gapLow    int32 = -5
	gapHigh   int32 = 50
	deltaLow  int32 = -300
	deltaHigh int32 = 300
	angleLow  int32 = -200000
	angleHigh int32 = 200000
	valueLow  int32 = -50
	valueHigh int32 = 50
	countLow  int32 = -5
	countHigh int32 = 100000

	casesPerOperation = 1000
	discardedDraws    = 8
	listLengthModulus = 7
)

var boundaryValues = [5]int32{-2147483648, -1, 0, 1, 2147483647}

type rect struct {
	x int32
	y int32
	w int32
	h int32
}

type point struct {
	x int32
	y int32
}

type size struct {
	w int32
	h int32
}

type segment struct {
	x1 int32
	y1 int32
	x2 int32
	y2 int32
}

type stream struct {
	state uint32
}

type operation struct {
	name   string
	result string
	draw   func(*stream) string
}

func (s *stream) next() uint32 {
	s.state ^= s.state << 13
	s.state ^= s.state >> 17
	s.state ^= s.state << 5
	return s.state
}

func (s *stream) value(low, high int32) int32 {
	if s.next()%16 == 0 {
		return boundaryValues[s.next()%5]
	}
	span := uint32(high - low + 1)
	return low + int32(s.next()%span)
}

func newStream(caseIndex int) *stream {
	s := &stream{state: uint32(caseIndex + 1)}
	for range discardedDraws {
		s.next()
	}
	return s
}

func drawRect(s *stream) rect {
	return rect{
		x: s.value(coordLow, coordHigh),
		y: s.value(coordLow, coordHigh),
		w: s.value(sizeLow, sizeHigh),
		h: s.value(sizeLow, sizeHigh),
	}
}

func drawSize(s *stream) size {
	return size{w: s.value(sizeLow, sizeHigh), h: s.value(sizeLow, sizeHigh)}
}

func drawSegment(s *stream) segment {
	x1 := s.value(coordLow, coordHigh)
	y1 := s.value(coordLow, coordHigh)
	if s.next()%2 == 0 {
		return segment{x1: x1, y1: y1, x2: s.value(coordLow, coordHigh), y2: y1}
	}
	return segment{x1: x1, y1: y1, x2: x1, y2: s.value(coordLow, coordHigh)}
}

func drawAxis(s *stream) string {
	if s.next()%2 == 0 {
		return "X"
	}
	return "Y"
}

func drawListLength(s *stream) int {
	return int(s.next() % listLengthModulus)
}

func formatInt(v int32) string {
	return strconv.FormatInt(int64(v), 10)
}

func formatRect(r rect) string {
	return "(" + formatInt(r.x) + "," + formatInt(r.y) + "," + formatInt(r.w) + "," + formatInt(r.h) + ")"
}

func formatPoint(p point) string {
	return "(" + formatInt(p.x) + "," + formatInt(p.y) + ")"
}

func formatSize(s size) string {
	return "(" + formatInt(s.w) + "," + formatInt(s.h) + ")"
}

func formatSegment(s segment) string {
	return "(" + formatInt(s.x1) + "," + formatInt(s.y1) + "," + formatInt(s.x2) + "," + formatInt(s.y2) + ")"
}

func formatList[T any](items []T, format func(T) string) string {
	parts := make([]string, len(items))
	for i, item := range items {
		parts[i] = format(item)
	}
	return "[" + strings.Join(parts, ",") + "]"
}

func drawPointList(s *stream) string {
	items := make([]point, drawListLength(s))
	for i := range items {
		items[i] = point{x: s.value(coordLow, coordHigh), y: s.value(coordLow, coordHigh)}
	}
	return formatList(items, formatPoint)
}

func drawValueList(s *stream) string {
	items := make([]int32, drawListLength(s))
	for i := range items {
		items[i] = s.value(valueLow, valueHigh)
	}
	return formatList(items, formatInt)
}

func drawTranslate(s *stream) string {
	return formatRect(drawRect(s)) + " " +
		formatInt(s.value(deltaLow, deltaHigh)) + " " +
		formatInt(s.value(deltaLow, deltaHigh))
}

func drawInflate(s *stream) string {
	return formatRect(drawRect(s)) + " " + formatInt(s.value(deltaLow, deltaHigh))
}

func drawRectPair(s *stream) string {
	return formatRect(drawRect(s)) + " " + formatRect(drawRect(s))
}

func drawPlaceAfter(s *stream) string {
	return drawAxis(s) + " " + formatRect(drawRect(s)) + " " +
		formatInt(s.value(gapLow, gapHigh)) + " " + formatSize(drawSize(s))
}

func drawCompact(s *stream) string {
	axis := drawAxis(s)
	gap := formatInt(s.value(gapLow, gapHigh))
	items := make([]rect, drawListLength(s))
	for i := range items {
		items[i] = drawRect(s)
	}
	return axis + " " + gap + " " + formatList(items, formatRect)
}

func drawSegmentPair(s *stream) string {
	return formatSegment(drawSegment(s)) + " " + formatSegment(drawSegment(s))
}

func drawPolylineHitsRect(s *stream) string {
	return drawPointList(s) + " " + formatRect(drawRect(s))
}

func drawScalar(s *stream) string {
	return formatInt(s.value(countLow, countHigh))
}

func drawAngle(s *stream) string {
	return formatInt(s.value(angleLow, angleHigh))
}

var operations = []operation{
	{name: "translate", result: "(0,0,0,0)", draw: drawTranslate},
	{name: "inflate", result: "(0,0,0,0)", draw: drawInflate},
	{name: "union", result: "(0,0,0,0)", draw: drawRectPair},
	{name: "intersects", result: "false", draw: drawRectPair},
	{name: "contains", result: "false", draw: drawRectPair},
	{name: "place_after", result: "(0,0,0,0)", draw: drawPlaceAfter},
	{name: "compact", result: "[]", draw: drawCompact},
	{name: "segments_cross", result: "false", draw: drawSegmentPair},
	{name: "is_orthogonal", result: "false", draw: drawPointList},
	{name: "polyline_hits_rect", result: "false", draw: drawPolylineHitsRect},
	{name: "count_inversions", result: "0", draw: drawValueList},
	{name: "isqrt", result: "0", draw: drawScalar},
	{name: "sin_q15", result: "0", draw: drawAngle},
	{name: "cos_q15", result: "0", draw: drawAngle},
}

func generate(w io.Writer) error {
	out := bufio.NewWriter(w)
	for _, op := range operations {
		for caseIndex := range casesPerOperation {
			caseStream := newStream(caseIndex)
			if _, err := fmt.Fprintf(out, "%s %s -> %s\n", op.name, op.draw(caseStream), op.result); err != nil {
				return err
			}
		}
	}
	return out.Flush()
}

func main() {
	if err := generate(os.Stdout); err != nil {
		fmt.Fprintf(os.Stderr, "kernelgen: %v\n", err)
		os.Exit(1)
	}
}
