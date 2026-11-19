package cells

import (
	"errors"
	"math"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func TestBounds(t *testing.T) {
	if _, e := New(-1, 1); !errors.Is(e, ErrNegativeSize) {
		t.Fatal(e)
	}
	if _, e := NewBraille(-1, 1); !errors.Is(e, ErrNegativeSize) {
		t.Fatal(e)
	}
	if _, e := New(math.MaxInt, 2); !errors.Is(e, geom.ErrOverflow) {
		t.Fatal(e)
	}
	c := canvas(t, 2, 0)
	if len(c.Serialise(CharsetUnicode, ColorNone, nil)) != 0 {
		t.Fatal("empty canvas")
	}
	c = canvas(t, 2, 1)
	c.PutDot(-1, 0, TokenLine)
	c.PutSymbol(2, 0, 'x')
	if c.PutLabel(1, 0, "界", 2, TokenFG) {
		t.Fatal("outside label")
	}
	if string(c.Serialise(CharsetUnicode, ColorNone, nil)) != "\n" {
		t.Fatal("outside write")
	}
}

func TestASCIIAllMasks(t *testing.T) {
	for s := StyleNone; s <= StyleDouble; s++ {
		expected := " |-+||++-+-+++++"
		if s == StyleDotted {
			expected = " :.+::++.+.+++++"
		}
		for mask, r := range []rune(expected) {
			if Glyph(CharsetASCII, s, uint8(mask)) != r {
				t.Fatal(s, mask)
			}
		}
	}
}

func TestCheckedProducts(t *testing.T) {
	for _, p := range [][2]int64{{math.MaxInt64, 2}, {math.MinInt64, -1}, {-1, math.MinInt64}} {
		if _, err := multiply(p[0], p[1]); !errors.Is(err, geom.ErrOverflow) {
			t.Fatal(p, err)
		}
	}
	if _, err := CellDot(geom.Point{X: math.MaxInt32}); !errors.Is(err, geom.ErrOverflow) {
		t.Fatal(err)
	}
	if _, err := Ellipse(geom.Point{X: math.MaxInt32}, 1, 1); !errors.Is(err, geom.ErrOverflow) {
		t.Fatal(err)
	}
}
