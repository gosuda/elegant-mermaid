package markdown

import "github.com/gosuda/elegant-mermaid/internal/source"

const (
	maxIndent    = 3
	tabWidth     = 4
	fenceMin     = 3
	maxOrdered   = 9
	colonOpener  = ":::mermaid"
	colonCloser  = ":::"
	infoMermaid  = "mermaid"
	infoMMD      = "mmd"
	infoBrackets = "{mermaid}"
)

var mermaidInfo = [...]string{infoMermaid, infoMMD, infoBrackets}

type BlockLine struct {
	HostOffset  int
	BlockOffset int
	Len         int
}

type Block struct {
	Source []byte
	Span   source.Span
	Lines  []BlockLine
}

func (b Block) HostOffset(blockOffset int) int {
	at := clamp(blockOffset, len(b.Source))
	if len(b.Lines) == 0 {
		return b.Span.Start
	}
	line := b.Lines[0]
	for _, l := range b.Lines {
		if l.BlockOffset > at {
			break
		}
		line = l
	}
	return line.HostOffset + clamp(at-line.BlockOffset, line.Len)
}

func Blocks(src []byte) []Block {
	s := &scanner{src: src}
	for at := 0; at < len(src); {
		l := nextLine(src, at)
		s.line(l)
		at = l.next
	}
	s.end()
	return s.blocks
}

type frame struct {
	quote  bool
	indent int
}

type hostLine struct {
	start      int
	contentEnd int
	next       int
}

type piece struct {
	start      int
	contentEnd int
	next       int
}

type blockKind uint8

const (
	blockFence blockKind = iota
	blockColon
)

type skipFence struct {
	char  byte
	count int
}

type openBlock struct {
	char   byte
	count  int
	kind   blockKind
	opener int
	stop   int
	alias  bool
	pieces []piece
}

type scanner struct {
	src    []byte
	frames []frame
	block  *openBlock
	skip   *skipFence
	blocks []Block
}

func nextLine(src []byte, at int) hostLine {
	end := at
	for end < len(src) && src[end] != '\n' && src[end] != '\r' {
		end++
	}
	line := hostLine{start: at, contentEnd: end, next: end}
	if end < len(src) {
		line.next = end + 1
		if src[end] == '\r' && end+1 < len(src) && src[end+1] == '\n' {
			line.next = end + 2
		}
	}
	return line
}

func (s *scanner) line(l hostLine) {
	pos := s.strip(l)
	switch {
	case s.block != nil:
		s.inside(l, pos)
	case s.skip != nil:
		s.fenced(l, pos)
	default:
		s.open(l, pos)
	}
}

func (s *scanner) strip(l hostLine) int {
	depth := 0
	pos := l.start
	for depth < len(s.frames) {
		next, ok := s.frames[depth].strip(s.src, pos, l.contentEnd)
		if !ok {
			break
		}
		pos = next
		depth++
	}
	if depth < len(s.frames) {
		s.frames = s.frames[:depth]
		s.endBlock()
		s.skip = nil
	}
	return pos
}

func (s *scanner) inside(l hostLine, pos int) {
	if s.block.closes(s.src, pos, l.contentEnd) {
		s.block.stop = l.contentEnd
		s.endBlock()
		return
	}
	s.block.pieces = append(s.block.pieces, piece{start: pos, contentEnd: l.contentEnd, next: l.next})
	s.block.stop = l.next
}

func (s *scanner) fenced(l hostLine, pos int) {
	if fenceAt(s.src, pos, l.contentEnd, s.skip.char, s.skip.count) {
		s.skip = nil
	}
}

func (s *scanner) open(l hostLine, pos int) {
	for {
		next, opened := s.openFrame(l, pos)
		if !opened {
			break
		}
		pos = next
	}
	if !s.openColon(l, pos) {
		s.openFence(l, pos)
	}
}

func (s *scanner) openFrame(l hostLine, pos int) (int, bool) {
	at := skipSpaces(s.src, pos, l.contentEnd, maxIndent)
	if at < l.contentEnd && s.src[at] == '>' {
		s.frames = append(s.frames, frame{quote: true})
		return quoteEnd(s.src, at, l.contentEnd), true
	}
	marker, ok := listMarker(s.src, at, l.contentEnd)
	if !ok {
		return pos, false
	}
	stop, indent := contentIndent(s.src, at+marker, l.contentEnd, at-pos+marker)
	s.frames = append(s.frames, frame{indent: indent})
	return stop, true
}

func (s *scanner) openColon(l hostLine, pos int) bool {
	stop := pos + len(colonOpener)
	if stop > l.contentEnd || string(s.src[pos:stop]) != colonOpener || !blank(s.src, stop, l.contentEnd) {
		return false
	}
	s.block = &openBlock{kind: blockColon, opener: l.start, stop: l.contentEnd, alias: len(s.frames) == 0}
	return true
}

func (s *scanner) openFence(l hostLine, pos int) bool {
	at := skipSpaces(s.src, pos, l.contentEnd, maxIndent)
	if at >= l.contentEnd || !isFenceChar(s.src[at]) {
		return false
	}
	run := runLength(s.src, at, l.contentEnd, s.src[at])
	if run < fenceMin {
		return false
	}
	if isMermaidInfo(s.src, at+run, l.contentEnd) {
		s.block = &openBlock{
			kind:   blockFence,
			char:   s.src[at],
			count:  run,
			opener: l.start,
			stop:   l.contentEnd,
			alias:  len(s.frames) == 0,
		}
		return true
	}
	s.skip = &skipFence{char: s.src[at], count: run}
	return true
}

func (s *scanner) endBlock() {
	b := s.block
	if b == nil {
		return
	}
	s.block = nil
	text, lines := b.materialize(s.src)
	s.blocks = append(s.blocks, Block{Source: text, Span: source.Span{Start: b.opener, End: b.stop}, Lines: lines})
}

func (s *scanner) end() {
	s.endBlock()
	s.skip = nil
	s.frames = s.frames[:0]
}

func (b *openBlock) materialize(src []byte) ([]byte, []BlockLine) {
	lines := make([]BlockLine, len(b.pieces))
	if b.alias {
		for i, p := range b.pieces {
			lines[i] = BlockLine{HostOffset: p.start, BlockOffset: p.start - b.origin(), Len: p.contentEnd - p.start}
		}
		return src[b.origin():b.contentStop()], lines
	}
	own := make([]byte, 0, b.stop-b.opener)
	for i, p := range b.pieces {
		lines[i] = BlockLine{HostOffset: p.start, BlockOffset: len(own), Len: p.contentEnd - p.start}
		own = append(own, src[p.start:p.contentEnd]...)
		own = append(own, src[p.contentEnd:p.next]...)
	}
	return own, lines
}

func (b *openBlock) origin() int {
	if len(b.pieces) == 0 {
		return b.opener
	}
	return b.pieces[0].start
}

func (b *openBlock) contentStop() int {
	if len(b.pieces) == 0 {
		return b.origin()
	}
	return b.pieces[len(b.pieces)-1].next
}

func (b *openBlock) closes(src []byte, pos, end int) bool {
	if b.kind == blockColon {
		return colonAt(src, pos, end)
	}
	return fenceAt(src, pos, end, b.char, b.count)
}

func (f frame) strip(src []byte, pos, end int) (int, bool) {
	if f.quote {
		at := skipSpaces(src, pos, end, maxIndent)
		if at >= end || src[at] != '>' {
			return pos, false
		}
		return quoteEnd(src, at, end), true
	}
	if blank(src, pos, end) {
		return pos, true
	}
	return stripIndent(src, pos, end, f.indent)
}

func quoteEnd(src []byte, at, end int) int {
	if at+1 < end && src[at+1] == ' ' {
		return at + 2
	}
	return at + 1
}

func stripIndent(src []byte, pos, end, indent int) (int, bool) {
	column := 0
	for pos < end && column < indent {
		width, ok := indentWidth(src[pos], column)
		if !ok {
			return pos, false
		}
		column += width
		pos++
	}
	return pos, column >= indent
}

func contentIndent(src []byte, pos, end, column int) (int, int) {
	for pos < end {
		width, ok := indentWidth(src[pos], column)
		if !ok {
			return pos, column
		}
		column += width
		pos++
	}
	return pos, column
}

func indentWidth(b byte, column int) (int, bool) {
	switch b {
	case ' ':
		return 1, true
	case '\t':
		return tabWidth - column%tabWidth, true
	}
	return 0, false
}

func listMarker(src []byte, at, end int) (int, bool) {
	if at >= end {
		return 0, false
	}
	if isBullet(src[at]) {
		return 1, startsContent(src, at+1, end)
	}
	if isOrdered(src, at, end) {
		return digitRun(src, at, end) + 1, true
	}
	return 0, false
}

func isOrdered(src []byte, at, end int) bool {
	digits := digitRun(src, at, end)
	if digits == 0 || at+digits >= end {
		return false
	}
	if src[at+digits] != '.' && src[at+digits] != ')' {
		return false
	}
	return startsContent(src, at+digits+1, end)
}

func digitRun(src []byte, at, end int) int {
	n := 0
	for at+n < end && n < maxOrdered && isDigit(src[at+n]) {
		n++
	}
	return n
}

func startsContent(src []byte, pos, end int) bool {
	if pos >= end {
		return true
	}
	return src[pos] == ' ' || src[pos] == '\t'
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

func isBullet(b byte) bool {
	return b == '-' || b == '*' || b == '+'
}

func isFenceChar(b byte) bool {
	return b == '`' || b == '~'
}

func skipSpaces(src []byte, pos, end, limit int) int {
	spaces := 0
	for spaces < limit && pos < end && src[pos] == ' ' {
		pos++
		spaces++
	}
	return pos
}

func skipBlanks(src []byte, pos, end int) int {
	for pos < end && (src[pos] == ' ' || src[pos] == '\t') {
		pos++
	}
	return pos
}

func blank(src []byte, pos, end int) bool {
	return skipBlanks(src, pos, end) >= end
}

func runLength(src []byte, pos, end int, char byte) int {
	at := pos
	for at < end && src[at] == char {
		at++
	}
	return at - pos
}

func fenceAt(src []byte, pos, end int, char byte, count int) bool {
	at := skipSpaces(src, pos, end, maxIndent)
	if at >= end || src[at] != char {
		return false
	}
	run := runLength(src, at, end, char)
	return run >= count && blank(src, at+run, end)
}

func colonAt(src []byte, pos, end int) bool {
	stop := pos + len(colonCloser)
	if stop > end || string(src[pos:stop]) != colonCloser {
		return false
	}
	return blank(src, stop, end)
}

func isMermaidInfo(src []byte, pos, end int) bool {
	pos = skipBlanks(src, pos, end)
	stop := pos
	for stop < end && src[stop] != ' ' && src[stop] != '\t' {
		stop++
	}
	word := src[pos:stop]
	for _, name := range mermaidInfo {
		if asciiEqualFold(word, name) {
			return true
		}
	}
	return false
}

func asciiEqualFold(word []byte, name string) bool {
	if len(word) != len(name) {
		return false
	}
	for i, b := range word {
		if lowerASCII(b) != name[i] {
			return false
		}
	}
	return true
}

func lowerASCII(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

func clamp(value, limit int) int {
	if value < 0 {
		return 0
	}
	if value > limit {
		return limit
	}
	return value
}
