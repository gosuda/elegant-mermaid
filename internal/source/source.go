package source

import "unicode/utf8"

type Span struct {
	Start int
	End   int
}

type Position struct {
	Line   int
	Column int
}

type Index struct {
	src    []byte
	starts []int
}

func NewIndex(src []byte) *Index {
	return &Index{src: src, starts: lineStarts(src)}
}

func (ix *Index) Position(offset int) Position {
	at := ix.align(offset)
	line := ix.lineOf(at)
	return Position{Line: line + 1, Column: 1 + scalarCount(ix.src[ix.starts[line]:at])}
}

func (ix *Index) UTF16Column(offset int) int {
	at := ix.align(offset)
	line := ix.lineOf(at)
	return 1 + utf16Units(ix.src[ix.starts[line]:at])
}

func (ix *Index) LineContent(line int) Span {
	if line < 1 {
		line = 1
	}
	if line > len(ix.starts) {
		line = len(ix.starts)
	}
	start := ix.starts[line-1]
	if line == len(ix.starts) {
		return Span{Start: start, End: len(ix.src)}
	}
	return Span{Start: start, End: contentEnd(ix.src, ix.starts[line])}
}

func (ix *Index) align(offset int) int {
	at := clampOffset(offset, len(ix.src))
	for at > 0 && at < len(ix.src) && ix.src[at]&0xC0 == 0x80 {
		at--
	}
	return at
}

func (ix *Index) lineOf(offset int) int {
	low, high := 0, len(ix.starts)
	for low+1 < high {
		middle := (low + high) / 2
		if ix.starts[middle] <= offset {
			low = middle
		} else {
			high = middle
		}
	}
	return low
}

func lineStarts(src []byte) []int {
	starts := make([]int, 1, 1+len(src)/24)
	starts[0] = 0
	for at := 0; at < len(src); {
		switch src[at] {
		case '\r':
			at = skipCarriageReturn(src, at)
			starts = append(starts, at)
		case '\n':
			at++
			starts = append(starts, at)
		default:
			at++
		}
	}
	return starts
}

func skipCarriageReturn(src []byte, at int) int {
	if at+1 < len(src) && src[at+1] == '\n' {
		return at + 2
	}
	return at + 1
}

func contentEnd(src []byte, next int) int {
	if next >= 2 && src[next-2] == '\r' && src[next-1] == '\n' {
		return next - 2
	}
	return next - 1
}

func clampOffset(offset, limit int) int {
	if offset < 0 {
		return 0
	}
	if offset > limit {
		return limit
	}
	return offset
}

func scalarCount(b []byte) int {
	count := 0
	for _, c := range b {
		if c&0xC0 != 0x80 {
			count++
		}
	}
	return count
}

func utf16Units(b []byte) int {
	units := 0
	for _, c := range b {
		switch {
		case c&0xC0 == 0x80:
		case c&0xF8 == 0xF0:
			units += 2
		default:
			units++
		}
	}
	return units
}

func RepairUTF8(src []byte) ([]byte, int) {
	d := &utf8Decoder{src: src, first: -1, lower: 0x80, upper: 0xBF}
	for d.pos < len(src) && d.need == 0 {
		d.lead()
		for d.need != 0 && d.pos < len(src) {
			d.continuation()
		}
	}
	if d.need != 0 {
		d.reject(d.seqStart)
	}
	if d.out == nil {
		return src, -1
	}
	return d.out, d.first
}

type utf8Decoder struct {
	src      []byte
	out      []byte
	first    int
	need     int
	lower    int
	upper    int
	code     int
	seqStart int
	pos      int
}

func (d *utf8Decoder) lead() {
	b := d.src[d.pos]
	d.seqStart = d.pos
	d.pos++
	switch {
	case b < 0x80:
		d.emit(rune(b))
	case b >= 0xC2 && b <= 0xDF:
		d.begin(1, b&0x1F, [2]int{0x80, 0xBF})
	case b >= 0xE0 && b <= 0xEF:
		d.begin(2, b&0x0F, continuationBounds(b))
	case b >= 0xF0 && b <= 0xF4:
		d.begin(3, b&0x07, continuationBounds(b))
	default:
		d.reject(d.seqStart)
	}
}

func (d *utf8Decoder) continuation() {
	b := int(d.src[d.pos])
	if b < d.lower || b > d.upper {
		d.reject(d.seqStart)
		d.need = 0
		d.lower = 0x80
		d.upper = 0xBF
		return
	}
	d.code = d.code<<6 | (b & 0x3F)
	d.need--
	d.lower = 0x80
	d.upper = 0xBF
	d.pos++
	if d.need == 0 {
		d.emit(rune(d.code))
	}
}

func (d *utf8Decoder) begin(need int, mask byte, bounds [2]int) {
	d.need = need
	d.code = int(mask)
	d.lower = bounds[0]
	d.upper = bounds[1]
}

func (d *utf8Decoder) emit(r rune) {
	if d.out != nil {
		d.out = utf8.AppendRune(d.out, r)
	}
}

func (d *utf8Decoder) reject(offset int) {
	if d.first < 0 {
		d.first = offset
	}
	if d.out == nil {
		d.out = make([]byte, offset, len(d.src))
		copy(d.out, d.src[:offset])
	}
	d.out = utf8.AppendRune(d.out, utf8.RuneError)
}

func continuationBounds(lead byte) [2]int {
	switch lead {
	case 0xE0:
		return [2]int{0xA0, 0xBF}
	case 0xED:
		return [2]int{0x80, 0x9F}
	case 0xF0:
		return [2]int{0x90, 0xBF}
	case 0xF4:
		return [2]int{0x80, 0x8F}
	}
	return [2]int{0x80, 0xBF}
}
