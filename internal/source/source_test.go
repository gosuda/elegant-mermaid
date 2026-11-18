package source

import (
	"testing"
	"unicode/utf8"
)

var textTokens = [][]byte{
	[]byte("a"),
	[]byte("Z"),
	[]byte("\n"),
	[]byte("\r\n"),
	[]byte("\r"),
	[]byte("é"),
	[]byte("世"),
	[]byte("😀"),
	[]byte(" "),
	[]byte("~"),
}

type xorshift32 struct {
	state uint32
}

func (x *xorshift32) next() uint32 {
	x.state ^= x.state << 13
	x.state ^= x.state >> 17
	x.state ^= x.state << 5
	return x.state
}

func (x *xorshift32) draw(limit int) int {
	return int(x.next() % uint32(limit))
}

func randomText(x *xorshift32) []byte {
	out := make([]byte, 0, 32)
	for range 1 + x.draw(24) {
		out = append(out, textTokens[x.draw(len(textTokens))]...)
	}
	return out
}

func naivePosition(src []byte, offset int) Position {
	target := min(max(0, offset), len(src))
	for target > 0 && target < len(src) && src[target]&0xC0 == 0x80 {
		target--
	}
	line, lineStart := 1, 0
	for at := 0; at < len(src); {
		end := lineEnd(src, at)
		if end == len(src) {
			return Position{Line: line, Column: 1 + utf8.RuneCount(src[lineStart:target])}
		}
		next := afterEnding(src, end)
		if target < next {
			return Position{Line: line, Column: 1 + utf8.RuneCount(src[lineStart:target])}
		}
		line, lineStart, at = line+1, next, next
	}
	return Position{Line: line, Column: 1 + utf8.RuneCount(src[lineStart:target])}
}

func lineEnd(src []byte, at int) int {
	for at < len(src) && src[at] != '\n' && src[at] != '\r' {
		at++
	}
	return at
}

func afterEnding(src []byte, at int) int {
	if at < len(src) && src[at] == '\r' && at+1 < len(src) && src[at+1] == '\n' {
		return at + 2
	}
	if at < len(src) {
		return at + 1
	}
	return at
}

func TestPositionMatchesNaiveScan(t *testing.T) {
	for index := range 500 {
		x := xorshift32{state: uint32(index + 1)}
		src := randomText(&x)
		ix := NewIndex(src)
		for offset := -3; offset <= len(src)+3; offset++ {
			want := naivePosition(src, offset)
			if got := ix.Position(offset); got != want {
				t.Fatalf("case %d offset %d src %q: got %+v want %+v", index, offset, src, got, want)
			}
		}
	}
}

func TestPositionCountsScalarsNotBytes(t *testing.T) {
	cases := []struct {
		name   string
		src    string
		offset int
		want   Position
	}{
		{"scalar after multibyte text", "é世😀x", 9, Position{Line: 1, Column: 4}},
		{"offset inside a sequence maps to its start", "é世😀x", 8, Position{Line: 1, Column: 3}},
		{"lone cr ends a line", "ab\rcd", 3, Position{Line: 2, Column: 1}},
		{"crlf is one ending", "ab\r\ncd", 4, Position{Line: 2, Column: 1}},
		{"cr of crlf stays on its line", "ab\r\ncd", 2, Position{Line: 1, Column: 3}},
		{"lf ends a line", "ab\ncd", 3, Position{Line: 2, Column: 1}},
		{"clamps below zero", "abc", -9, Position{Line: 1, Column: 1}},
		{"clamps past the end", "abc", 9, Position{Line: 1, Column: 4}},
		{"ending lf opens an empty line", "abc\n", 4, Position{Line: 2, Column: 1}},
		{"empty source", "", 0, Position{Line: 1, Column: 1}},
	}
	for _, c := range cases {
		ix := NewIndex([]byte(c.src))
		if got := ix.Position(c.offset); got != c.want {
			t.Errorf("%s: got %+v want %+v", c.name, got, c.want)
		}
	}
}

func TestUTF16ColumnCountsSurrogates(t *testing.T) {
	ix := NewIndex([]byte("a😀b\ncd"))
	cases := []struct {
		offset int
		want   int
	}{
		{0, 1},
		{1, 2},
		{5, 4},
		{6, 5},
		{7, 1},
		{9, 3},
	}
	for _, c := range cases {
		if got := ix.UTF16Column(c.offset); got != c.want {
			t.Errorf("offset %d: got %d want %d", c.offset, got, c.want)
		}
	}
}

func TestLineContentExcludesLineEnding(t *testing.T) {
	ix := NewIndex([]byte("ab\r\ncd\ref"))
	want := []Span{{Start: 0, End: 2}, {Start: 4, End: 6}, {Start: 7, End: 9}}
	for i, w := range want {
		if got := ix.LineContent(i + 1); got != w {
			t.Errorf("line %d: got %+v want %+v", i+1, got, w)
		}
	}
}

func TestRepairUTF8AcceptsValidInput(t *testing.T) {
	src := []byte("plain é 世 😀\n")
	out, first := RepairUTF8(src)
	if first != -1 {
		t.Fatalf("first bad byte: got %d want -1", first)
	}
	if string(out) != string(src) || &out[0] != &src[0] {
		t.Fatal("valid input was not returned unchanged")
	}
}

func TestRepairUTF8FollowsMaximalSubpart(t *testing.T) {
	cases := []struct {
		name  string
		src   []byte
		want  string
		first int
	}{
		{"truncated four byte sequence", []byte{0xF0, 0x9F, 0x98}, "\uFFFD", 0},
		{"overlong two byte sequence", []byte{0xC0, 0x80}, "\uFFFD\uFFFD", 0},
		{"bad third byte", []byte{0xE2, 0x28, 0xA1}, "\uFFFD(\uFFFD", 0},
		{"lone continuation byte", []byte{'a', 0x80, 'b'}, "a\uFFFDb", 1},
		{"surrogate half", []byte{0xED, 0xA0, 0x80}, "\uFFFD\uFFFD\uFFFD", 0},
		{"above the unicode maximum", []byte{0xF4, 0x90, 0x80, 0x80}, "\uFFFD\uFFFD\uFFFD\uFFFD", 0},
		{"truncated after one continuation", []byte{'x', 0xE3, 0x81}, "x\uFFFD", 1},
		{"valid pair then bad byte", []byte{0xC3, 0xA9, 0xFF}, "é\uFFFD", 2},
		{"empty input", nil, "", -1},
	}
	for _, c := range cases {
		out, first := RepairUTF8(c.src)
		if string(out) != c.want {
			t.Errorf("%s: got %q want %q", c.name, out, c.want)
		}
		if first != c.first {
			t.Errorf("%s: first bad byte %d want %d", c.name, first, c.first)
		}
	}
}

func TestRepairUTF8OwnsItsRepairedCopy(t *testing.T) {
	src := []byte{'a', 0xFF, 'b'}
	out, _ := RepairUTF8(src)
	src[0] = 'z'
	if out[0] != 'a' {
		t.Fatal("repaired copy aliases the input")
	}
}
