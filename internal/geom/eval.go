package geom

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
)

type CaseError struct {
	Line int
}

func (e *CaseError) Error() string {
	return fmt.Sprintf("bad case line %d", e.Line)
}

type operandKind uint8

const (
	kindInt operandKind = iota
	kindAxis
	kindTuple2
	kindTuple4
	kindIntList
	kindTuple2List
	kindTuple4List
)

type operand struct {
	kind operandKind
	val  int64
	axis Axis
	tup  []int64
	list []operand
}

type opEntry struct {
	args  [4]operandKind
	arity int
	fn    func(*[4]operand) string
}

func operation(name string) (opEntry, bool) {
	switch name {
	case "translate":
		return opEntry{[4]operandKind{kindTuple4, kindInt, kindInt}, 3, evalTranslate}, true
	case "inflate":
		return opEntry{[4]operandKind{kindTuple4, kindInt}, 2, evalInflate}, true
	case "union":
		return opEntry{[4]operandKind{kindTuple4, kindTuple4}, 2, evalUnion}, true
	case "intersects":
		return opEntry{[4]operandKind{kindTuple4, kindTuple4}, 2, evalIntersects}, true
	case "contains":
		return opEntry{[4]operandKind{kindTuple4, kindTuple4}, 2, evalContains}, true
	case "place_after":
		return opEntry{[4]operandKind{kindAxis, kindTuple4, kindInt, kindTuple2}, 4, evalPlaceAfter}, true
	}
	return collectionOperation(name)
}

func collectionOperation(name string) (opEntry, bool) {
	switch name {
	case "compact":
		return opEntry{[4]operandKind{kindAxis, kindInt, kindTuple4List}, 3, evalCompact}, true
	case "segments_cross":
		return opEntry{[4]operandKind{kindTuple4, kindTuple4}, 2, evalSegmentsCross}, true
	case "is_orthogonal":
		return opEntry{[4]operandKind{kindTuple2List}, 1, evalIsOrthogonal}, true
	case "polyline_hits_rect":
		return opEntry{[4]operandKind{kindTuple2List, kindTuple4}, 2, evalPolylineHitsRect}, true
	case "count_inversions":
		return opEntry{[4]operandKind{kindIntList}, 1, evalCountInversions}, true
	}
	return scalarOperation(name)
}

func scalarOperation(name string) (opEntry, bool) {
	switch name {
	case "isqrt":
		return opEntry{[4]operandKind{kindInt}, 1, evalIsqrt}, true
	case "sin_q15":
		return opEntry{[4]operandKind{kindInt}, 1, evalSinQ15}, true
	case "cos_q15":
		return opEntry{[4]operandKind{kindInt}, 1, evalCosQ15}, true
	}
	return opEntry{}, false
}

func Eval(r io.Reader, w io.Writer) error {
	br := bufio.NewReaderSize(r, 1<<16)
	line := 0
	for {
		text, err := br.ReadString('\n')
		if len(text) == 0 && err != nil {
			if err == io.EOF {
				return nil
			}
			return err
		}
		line++
		if !strings.HasSuffix(text, "\n") {
			return &CaseError{Line: line}
		}
		res, ok := evalLine(strings.TrimSuffix(text, "\n"))
		if !ok {
			return &CaseError{Line: line}
		}
		if _, err := w.Write([]byte(res)); err != nil {
			return err
		}
	}
}

func evalLine(line string) (string, bool) {
	fields := strings.Split(line, " ")
	arrow := arrowIndex(fields)
	if arrow < 1 || arrow != len(fields)-2 {
		return "", false
	}
	entry, ok := operation(fields[0])
	if !ok || entry.arity != arrow-1 {
		return "", false
	}
	var args [4]operand
	ok = parseArgs(fields[1:arrow], entry.args, &args)
	if !ok || !validResult(fields[arrow+1]) {
		return "", false
	}
	return entry.fn(&args) + "\n", true
}

func parseArgs(tokens []string, kinds [4]operandKind, args *[4]operand) bool {
	for i := range tokens {
		arg, ok := parseOperand(tokens[i], kinds[i])
		if !ok {
			return false
		}
		args[i] = arg
	}
	return true
}

func arrowIndex(fields []string) int {
	for i, f := range fields {
		if f == "->" {
			return i
		}
	}
	return -1
}

func parseOperand(s string, kind operandKind) (operand, bool) {
	switch kind {
	case kindInt:
		v, ok := parseCaseInt(s)
		return operand{kind: kindInt, val: v}, ok
	case kindAxis:
		return parseAxis(s)
	case kindTuple2, kindTuple4:
		t, ok := parseTuple(s, tupleSize(kind))
		return operand{kind: kind, tup: t}, ok
	default:
		l, ok := parseList(s, listElementKind(kind))
		return operand{kind: kind, list: l}, ok
	}
}

func parseAxis(s string) (operand, bool) {
	switch s {
	case "X":
		return operand{kind: kindAxis, axis: AxisX}, true
	case "Y":
		return operand{kind: kindAxis, axis: AxisY}, true
	}
	return operand{}, false
}

func tupleSize(kind operandKind) int {
	if kind == kindTuple4 {
		return 4
	}
	return 2
}

func listElementKind(kind operandKind) operandKind {
	switch kind {
	case kindIntList:
		return kindInt
	case kindTuple4List:
		return kindTuple4
	default:
		return kindTuple2
	}
}

func parseTuple(s string, size int) ([]int64, bool) {
	if len(s) < 2 || s[0] != '(' || s[len(s)-1] != ')' {
		return nil, false
	}
	parts := strings.Split(s[1:len(s)-1], ",")
	if len(parts) != size {
		return nil, false
	}
	vals := make([]int64, size)
	for i, p := range parts {
		v, ok := parseCaseInt(p)
		if !ok {
			return nil, false
		}
		vals[i] = v
	}
	return vals, true
}

func parseList(s string, itemKind operandKind) ([]operand, bool) {
	if len(s) < 2 || s[0] != '[' || s[len(s)-1] != ']' {
		return nil, false
	}
	inner := s[1 : len(s)-1]
	if inner == "" {
		return []operand{}, true
	}
	items := []operand{}
	for _, tok := range splitTopLevel(inner) {
		o, ok := parseOperand(tok, itemKind)
		if !ok {
			return nil, false
		}
		items = append(items, o)
	}
	return items, true
}

func splitTopLevel(s string) []string {
	parts := []string{}
	depth, start := 0, 0
	for i := range len(s) {
		switch s[i] {
		case '(':
			depth++
		case ')':
			depth--
		case ',':
			if depth == 0 {
				parts = append(parts, s[start:i])
				start = i + 1
			}
		}
	}
	return append(parts, s[start:])
}

func parseCaseInt(s string) (int64, bool) {
	body, neg, ok := splitSign(s)
	if !ok {
		return 0, false
	}
	v, ok := scanDigits(body)
	if !ok {
		return 0, false
	}
	if neg {
		if body == "0" {
			return 0, false
		}
		v = -v
	}
	if v < int64(I32Min) || v > int64(I32Max) {
		return 0, false
	}
	return v, true
}

func splitSign(s string) (string, bool, bool) {
	if s == "" {
		return "", false, false
	}
	if s[0] == '-' {
		if len(s) == 1 {
			return "", false, false
		}
		return s[1:], true, true
	}
	return s, false, true
}

func scanDigits(body string) (int64, bool) {
	if body == "" || (len(body) > 1 && body[0] == '0') {
		return 0, false
	}
	v := int64(0)
	for i := range body {
		c := body[i]
		if c < '0' || c > '9' {
			return 0, false
		}
		v = v*10 + int64(c-'0')
		if v > 4294967296 {
			return 0, false
		}
	}
	return v, true
}

func validResult(s string) bool {
	switch s {
	case "true", "false", "overflow", "domain":
		return true
	}
	if _, ok := parseCaseInt(s); ok {
		return true
	}
	if isTupleToken(s) {
		return true
	}
	return isListToken(s)
}

func isTupleToken(s string) bool {
	if len(s) < 2 || s[0] != '(' || s[len(s)-1] != ')' {
		return false
	}
	parts := strings.Split(s[1:len(s)-1], ",")
	if len(parts) != 2 && len(parts) != 4 {
		return false
	}
	for _, p := range parts {
		if _, ok := parseCaseInt(p); !ok {
			return false
		}
	}
	return true
}

func isListToken(s string) bool {
	if len(s) < 2 || s[0] != '[' || s[len(s)-1] != ']' {
		return false
	}
	inner := s[1 : len(s)-1]
	if inner == "" {
		return true
	}
	for _, item := range splitTopLevel(inner) {
		if _, ok := parseCaseInt(item); ok {
			continue
		}
		if !isTupleToken(item) {
			return false
		}
	}
	return true
}

func evalTranslate(args *[4]operand) string {
	r, err := Translate(rectOf(args[0]), int32(args[1].val), int32(args[2].val))
	return rectToken(r, err)
}

func evalInflate(args *[4]operand) string {
	r, err := Inflate(rectOf(args[0]), int32(args[1].val))
	return rectToken(r, err)
}

func evalUnion(args *[4]operand) string {
	r, err := Union(rectOf(args[0]), rectOf(args[1]))
	return rectToken(r, err)
}

func evalIntersects(args *[4]operand) string {
	v, err := Intersects(rectOf(args[0]), rectOf(args[1]))
	return boolToken(v, err)
}

func evalContains(args *[4]operand) string {
	v, err := Contains(rectOf(args[0]), rectOf(args[1]))
	return boolToken(v, err)
}

func evalPlaceAfter(args *[4]operand) string {
	r, err := PlaceAfter(args[0].axis, rectOf(args[1]), int32(args[2].val), sizeOf(args[3]))
	return rectToken(r, err)
}

func evalCompact(args *[4]operand) string {
	items := make([]Rect, len(args[2].list))
	for i, o := range args[2].list {
		items[i] = rectOf(o)
	}
	out, err := Compact(args[0].axis, int32(args[1].val), items)
	if err != nil {
		return errToken(err)
	}
	return rectListToken(out)
}

func evalSegmentsCross(args *[4]operand) string {
	v, err := SegmentsCross(segOf(args[0]), segOf(args[1]))
	return boolToken(v, err)
}

func evalIsOrthogonal(args *[4]operand) string {
	return boolToken(IsOrthogonal(pointsOf(args[0].list)), nil)
}

func evalPolylineHitsRect(args *[4]operand) string {
	v, err := PolylineHitsRect(pointsOf(args[0].list), rectOf(args[1]))
	return boolToken(v, err)
}

func evalCountInversions(args *[4]operand) string {
	xs := make([]int32, len(args[0].list))
	for i, o := range args[0].list {
		xs[i] = int32(o.val)
	}
	n, err := CountInversions(xs)
	return intToken(int64(n), err)
}

func evalIsqrt(args *[4]operand) string {
	v, err := Isqrt(args[0].val)
	return intToken(v, err)
}

func evalSinQ15(args *[4]operand) string {
	return intToken(int64(SinQ15(int32(args[0].val))), nil)
}

func evalCosQ15(args *[4]operand) string {
	return intToken(int64(CosQ15(int32(args[0].val))), nil)
}

func rectOf(o operand) Rect {
	return Rect{X: int32(o.tup[0]), Y: int32(o.tup[1]), W: int32(o.tup[2]), H: int32(o.tup[3])}
}

func sizeOf(o operand) Size {
	return Size{W: int32(o.tup[0]), H: int32(o.tup[1])}
}

func segOf(o operand) Segment {
	return Segment{
		A: Point{X: int32(o.tup[0]), Y: int32(o.tup[1])},
		B: Point{X: int32(o.tup[2]), Y: int32(o.tup[3])},
	}
}

func pointsOf(list []operand) []Point {
	ps := make([]Point, len(list))
	for i, o := range list {
		ps[i] = Point{X: int32(o.tup[0]), Y: int32(o.tup[1])}
	}
	return ps
}

func errToken(err error) string {
	if errors.Is(err, ErrDomain) {
		return "domain"
	}
	return "overflow"
}

func rectToken(r Rect, err error) string {
	if err != nil {
		return errToken(err)
	}
	return fmt.Sprintf("(%d,%d,%d,%d)", r.X, r.Y, r.W, r.H)
}

func boolToken(v bool, err error) string {
	if err != nil {
		return errToken(err)
	}
	return strconv.FormatBool(v)
}

func intToken(v int64, err error) string {
	if err != nil {
		return errToken(err)
	}
	return strconv.FormatInt(v, 10)
}

func rectListToken(rs []Rect) string {
	parts := make([]string, len(rs))
	for i, r := range rs {
		parts[i] = fmt.Sprintf("(%d,%d,%d,%d)", r.X, r.Y, r.W, r.H)
	}
	return "[" + strings.Join(parts, ",") + "]"
}
