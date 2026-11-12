package main

import (
	"bytes"
	"fmt"
	"strings"
	"testing"
)

var expectedResultTokens = map[string]string{
	"translate":          "(0,0,0,0)",
	"inflate":            "(0,0,0,0)",
	"union":              "(0,0,0,0)",
	"intersects":         "false",
	"contains":           "false",
	"place_after":        "(0,0,0,0)",
	"compact":            "[]",
	"segments_cross":     "false",
	"is_orthogonal":      "false",
	"polyline_hits_rect": "false",
	"count_inversions":   "0",
	"isqrt":              "0",
	"sin_q15":            "0",
	"cos_q15":            "0",
}

var expectedOperationOrder = []string{
	"translate",
	"inflate",
	"union",
	"intersects",
	"contains",
	"place_after",
	"compact",
	"segments_cross",
	"is_orthogonal",
	"polyline_hits_rect",
	"count_inversions",
	"isqrt",
	"sin_q15",
	"cos_q15",
}

var refBoundary = []int32{-2147483648, -1, 0, 1, 2147483647}

type refSource struct {
	x uint32
}

func newRefSource(caseIndex int) *refSource {
	src := &refSource{x: uint32(caseIndex) + 1}
	for range 8 {
		src.advance()
	}
	return src
}

func (s *refSource) advance() uint32 {
	s.x = s.x ^ (s.x << 13)
	s.x = s.x ^ (s.x >> 17)
	s.x = s.x ^ (s.x << 5)
	return s.x
}

func (s *refSource) pick(lo, hi int32) int32 {
	salt := s.advance()
	if salt%16 == 0 {
		return refBoundary[s.advance()%5]
	}
	width := uint32(hi-lo) + 1
	return lo + int32(s.advance()%width)
}

func (s *refSource) count() int {
	return int(s.advance() % 7)
}

func (s *refSource) coord() int32 {
	return s.pick(-1000, 1000)
}

func (s *refSource) ext() int32 {
	return s.pick(-5, 500)
}

func (s *refSource) rectToken() string {
	x := s.coord()
	y := s.coord()
	w := s.ext()
	h := s.ext()
	return fmt.Sprintf("(%d,%d,%d,%d)", x, y, w, h)
}

func (s *refSource) sizeToken() string {
	return fmt.Sprintf("(%d,%d)", s.ext(), s.ext())
}

func (s *refSource) axisToken() string {
	if s.advance()%2 == 0 {
		return "X"
	}
	return "Y"
}

func (s *refSource) segmentToken() string {
	x1 := s.coord()
	y1 := s.coord()
	slope := s.advance() % 2
	if slope == 0 {
		return fmt.Sprintf("(%d,%d,%d,%d)", x1, y1, s.coord(), y1)
	}
	return fmt.Sprintf("(%d,%d,%d,%d)", x1, y1, x1, s.coord())
}

func (s *refSource) pointListToken() string {
	tokens := make([]string, s.count())
	for i := range tokens {
		tokens[i] = fmt.Sprintf("(%d,%d)", s.coord(), s.coord())
	}
	return "[" + strings.Join(tokens, ",") + "]"
}

func (s *refSource) valueListToken() string {
	tokens := make([]string, s.count())
	for i := range tokens {
		tokens[i] = fmt.Sprintf("%d", s.pick(-50, 50))
	}
	return "[" + strings.Join(tokens, ",") + "]"
}

func (s *refSource) rectListToken() string {
	tokens := make([]string, s.count())
	for i := range tokens {
		tokens[i] = s.rectToken()
	}
	return "[" + strings.Join(tokens, ",") + "]"
}

var refOperandBuilders = map[string]func(*refSource) []string{
	"translate": func(s *refSource) []string {
		return []string{s.rectToken(), fmt.Sprintf("%d", s.pick(-300, 300)), fmt.Sprintf("%d", s.pick(-300, 300))}
	},
	"inflate": func(s *refSource) []string {
		return []string{s.rectToken(), fmt.Sprintf("%d", s.pick(-300, 300))}
	},
	"union": func(s *refSource) []string {
		return []string{s.rectToken(), s.rectToken()}
	},
	"intersects": func(s *refSource) []string {
		return []string{s.rectToken(), s.rectToken()}
	},
	"contains": func(s *refSource) []string {
		return []string{s.rectToken(), s.rectToken()}
	},
	"place_after": func(s *refSource) []string {
		return []string{s.axisToken(), s.rectToken(), fmt.Sprintf("%d", s.pick(-5, 50)), s.sizeToken()}
	},
	"compact": func(s *refSource) []string {
		return []string{s.axisToken(), fmt.Sprintf("%d", s.pick(-5, 50)), s.rectListToken()}
	},
	"segments_cross": func(s *refSource) []string {
		return []string{s.segmentToken(), s.segmentToken()}
	},
	"is_orthogonal": func(s *refSource) []string {
		return []string{s.pointListToken()}
	},
	"polyline_hits_rect": func(s *refSource) []string {
		return []string{s.pointListToken(), s.rectToken()}
	},
	"count_inversions": func(s *refSource) []string {
		return []string{s.valueListToken()}
	},
	"isqrt": func(s *refSource) []string {
		return []string{fmt.Sprintf("%d", s.pick(-5, 100000))}
	},
	"sin_q15": func(s *refSource) []string {
		return []string{fmt.Sprintf("%d", s.pick(-200000, 200000))}
	},
	"cos_q15": func(s *refSource) []string {
		return []string{fmt.Sprintf("%d", s.pick(-200000, 200000))}
	},
}

func referenceLine(op string, caseIndex int) string {
	src := newRefSource(caseIndex)
	operands := strings.Join(refOperandBuilders[op](src), " ")
	return op + " " + operands + " -> " + expectedResultTokens[op]
}

func referenceOutput() []string {
	lines := make([]string, 0, len(expectedOperationOrder)*1000)
	for _, op := range expectedOperationOrder {
		for caseIndex := range 1000 {
			lines = append(lines, referenceLine(op, caseIndex))
		}
	}
	return lines
}

func generatedLines(t *testing.T) []string {
	t.Helper()
	var buffer bytes.Buffer
	if err := generate(&buffer); err != nil {
		t.Fatalf("generate: %v", err)
	}
	text, found := strings.CutSuffix(buffer.String(), "\n")
	if !found {
		t.Fatalf("output does not end in a line feed")
	}
	return strings.Split(text, "\n")
}

func TestCaseCountAndOrder(t *testing.T) {
	lines := generatedLines(t)
	if len(lines) != 14000 {
		t.Fatalf("line count = %d, want 14000", len(lines))
	}
	if len(operations) != 14 {
		t.Fatalf("operation count = %d, want 14", len(operations))
	}
	for index, op := range operations {
		if op.name != expectedOperationOrder[index] {
			t.Fatalf("operation %d = %q, want %q", index, op.name, expectedOperationOrder[index])
		}
		for caseIndex := range 1000 {
			line := lines[index*1000+caseIndex]
			fields := strings.Fields(line)
			if fields[0] != op.name {
				t.Fatalf("line %d starts with %q, want %q", index*1000+caseIndex+1, fields[0], op.name)
			}
		}
	}
}

func TestFirstCases(t *testing.T) {
	wantTranslate := "translate (612,-206,281,220) -110 -35 -> " + expectedResultTokens["translate"]
	if got := referenceLine("translate", 0); got != wantTranslate {
		t.Fatalf("reference translate case 0 = %q, want %q", got, wantTranslate)
	}
	wantIsqrt := "isqrt 23973 -> " + expectedResultTokens["isqrt"]
	if got := referenceLine("isqrt", 0); got != wantIsqrt {
		t.Fatalf("reference isqrt case 0 = %q, want %q", got, wantIsqrt)
	}
	lines := generatedLines(t)
	if lines[0] != wantTranslate {
		t.Fatalf("generated translate case 0 = %q, want %q", lines[0], wantTranslate)
	}
	isqrtOffset := 11 * 1000
	if lines[isqrtOffset] != wantIsqrt {
		t.Fatalf("generated isqrt case 0 = %q, want %q", lines[isqrtOffset], wantIsqrt)
	}
}

func TestMatchesReference(t *testing.T) {
	lines := generatedLines(t)
	want := referenceOutput()
	if len(want) != len(lines) {
		t.Fatalf("reference produced %d lines, generated %d", len(want), len(lines))
	}
	for index, expected := range want {
		if lines[index] != expected {
			t.Fatalf("line %d = %q, want %q", index+1, lines[index], expected)
		}
	}
}

func TestDeterministic(t *testing.T) {
	first := strings.Join(generatedLines(t), "\n")
	second := strings.Join(generatedLines(t), "\n")
	if first != second {
		t.Fatalf("two runs differ")
	}
}
