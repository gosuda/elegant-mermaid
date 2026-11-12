package flowchart

import (
	"strings"
	"unicode/utf8"
)

func lit(s string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		if matchLiteral(l.src, l.pos, limit, s) {
			return l.pos + len(s)
		}
		return -1
	}
}

func matchLiteral(src []byte, pos, limit int, s string) bool {
	if pos+len(s) > limit {
		return false
	}
	for i := 0; i < len(s); i++ {
		if src[pos+i] != s[i] {
			return false
		}
	}
	return true
}

func isJSSpace(b byte) bool {
	switch b {
	case ' ', '\t', '\n', '\r', '\f', '\v':
		return true
	}
	return false
}

func skipSpaces(src []byte, pos, limit int) int {
	for pos < limit && (src[pos] == ' ' || src[pos] == '\t') {
		pos++
	}
	return pos
}

func skipAllSpace(src []byte, pos, limit int) int {
	for pos < limit && isJSSpace(src[pos]) {
		pos++
	}
	return pos
}

func lineEndAt(src []byte, pos int) (int, bool) {
	if pos >= len(src) {
		return pos, false
	}
	switch src[pos] {
	case '\n':
		return pos + 1, true
	case '\r':
		if pos+1 < len(src) && src[pos+1] == '\n' {
			return pos + 2, true
		}
		return pos + 1, true
	}
	return pos, false
}

func keywordThenSpace(word string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		if !matchLiteral(l.src, l.pos, limit, word) {
			return -1
		}
		pos := skipAllSpace(l.src, l.pos+len(word), limit)
		if pos == l.pos+len(word) {
			return -1
		}
		return pos
	}
}

func keywordSpacesColonSpaces(word string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		if !matchLiteral(l.src, l.pos, limit, word) {
			return -1
		}
		pos := skipAllSpace(l.src, l.pos+len(word), limit)
		if pos >= limit || l.src[pos] != ':' {
			return -1
		}
		return skipAllSpace(l.src, pos+1, limit)
	}
}

func keywordSpacesBrace(word string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		if !matchLiteral(l.src, l.pos, limit, word) {
			return -1
		}
		pos := skipAllSpace(l.src, l.pos+len(word), limit)
		if pos >= limit || l.src[pos] != '{' {
			return -1
		}
		return skipAllSpace(l.src, pos+1, limit)
	}
}

func wordBoundaryAt(src []byte, pos, limit int) bool {
	if pos >= limit {
		return true
	}
	b := src[pos]
	return !asciiAlnum(b) && b != '_'
}

func endKeyword(l *lexer, limit int) int {
	if !matchLiteral(l.src, l.pos, limit, "end") {
		return -1
	}
	pos := l.pos + 3
	if !wordBoundaryAt(l.src, pos, limit) {
		return -1
	}
	return skipSpaces(l.src, pos, limit)
}

func hrefKeyword(l *lexer, limit int) int {
	if !matchLiteral(l.src, l.pos, limit, "href") {
		return -1
	}
	pos := l.pos + 4
	if pos < limit && isJSSpace(l.src[pos]) {
		return pos + 1
	}
	return -1
}

func dirNoDir(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && isJSSpace(l.src[pos]) {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	if pos >= limit {
		return pos
	}
	if last := l.src[pos-1]; last == '\n' || last == '\r' {
		return pos
	}
	return -1
}

func dirKeywordRule(dir string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		pos := skipSpaces(l.src, l.pos, limit)
		if !matchLiteral(l.src, pos, limit, dir) {
			return -1
		}
		return pos + len(dir)
	}
}

func linkIDRule(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && isLinkIDByte(l.src[pos]) {
		pos++
	}
	if pos == l.pos || pos >= limit || l.src[pos] != '@' {
		return -1
	}
	if pos+1 >= limit {
		return -1
	}
	if next := l.src[pos+1]; next == '{' || next == '"' {
		return -1
	}
	return pos + 1
}

func isLinkIDByte(b byte) bool {
	if isJSSpace(b) {
		return false
	}
	switch b {
	case '"', '[', ']', '(', ')', '{', '}', '|':
		return false
	}
	return true
}

func numRule(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] >= '0' && l.src[pos] <= '9' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func isMarkerStart(b byte) bool { return b == 'x' || b == 'o' || b == '<' }

func linkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos < limit && isMarkerStart(l.src[pos]) {
		pos++
	}
	dash := 0
	for pos < limit && l.src[pos] == '-' {
		pos++
		dash++
	}
	if dash >= 2 && pos < limit && markerEnd(l.src[pos]) {
		return skipAllSpace(l.src, pos+1, limit)
	}
	if dash >= 3 {
		return skipAllSpace(l.src, pos, limit)
	}
	return -1
}

func startLinkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos < limit && isMarkerStart(l.src[pos]) {
		pos++
	}
	if pos+1 >= limit || l.src[pos] != '-' || l.src[pos+1] != '-' {
		return -1
	}
	return skipAllSpace(l.src, pos+2, limit)
}

func thickLinkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos < limit && isMarkerStart(l.src[pos]) {
		pos++
	}
	eq := 0
	for pos < limit && l.src[pos] == '=' {
		pos++
		eq++
	}
	if eq >= 2 && pos < limit && markerEnd(l.src[pos]) {
		return skipAllSpace(l.src, pos+1, limit)
	}
	if eq >= 3 {
		return skipAllSpace(l.src, pos, limit)
	}
	return -1
}

func thickStartLinkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos < limit && isMarkerStart(l.src[pos]) {
		pos++
	}
	if pos+1 >= limit || l.src[pos] != '=' || l.src[pos+1] != '=' {
		return -1
	}
	return skipAllSpace(l.src, pos+2, limit)
}

func dottedLinkRule(l *lexer, limit int) int {
	pos := dottedPrefix(l.src, skipAllSpace(l.src, l.pos, limit), limit)
	dots := 0
	for pos < limit && l.src[pos] == '.' {
		pos++
		dots++
	}
	if dots == 0 || pos >= limit || l.src[pos] != '-' {
		return -1
	}
	pos++
	if pos < limit && markerEnd(l.src[pos]) {
		pos++
	}
	return skipAllSpace(l.src, pos, limit)
}

func dottedPrefix(src []byte, pos, limit int) int {
	if pos < limit && isMarkerStart(src[pos]) {
		pos++
	}
	if pos < limit && src[pos] == '-' {
		pos++
	}
	return pos
}

func dottedStartLinkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos < limit && isMarkerStart(l.src[pos]) {
		pos++
	}
	if pos+1 >= limit || l.src[pos] != '-' || l.src[pos+1] != '.' {
		return -1
	}
	return skipAllSpace(l.src, pos+2, limit)
}

func invisibleLinkRule(l *lexer, limit int) int {
	pos := skipAllSpace(l.src, l.pos, limit)
	if pos+2 >= limit || l.src[pos] != '~' || l.src[pos+1] != '~' || l.src[pos+2] != '~' {
		return -1
	}
	pos += 3
	for pos < limit && l.src[pos] == '~' {
		pos++
	}
	return skipAllSpace(l.src, pos, limit)
}

func nodeStringRule(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && nodeStringByte(l.src, pos, limit) {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func nodeStringByte(src []byte, pos, limit int) bool {
	b := src[pos]
	if asciiAlnum(b) {
		return true
	}
	switch b {
	case '!', '"', '#', '$', '%', '&', '\'', '*', '+', '.', '`', '?', '\\', '_', '/':
		return true
	case '-':
		if pos+1 >= limit {
			return false
		}
		next := src[pos+1]
		return !strings.ContainsRune(">-.", rune(next))
	case '=':
		if pos+1 >= limit {
			return true
		}
		return src[pos+1] != '='
	}
	return false
}

func asciiAlnum(b byte) bool {
	return b >= 'A' && b <= 'Z' || b >= 'a' && b <= 'z' || b >= '0' && b <= '9'
}

func markerEnd(b byte) bool {
	return b == 'x' || b == 'o' || b == '>'
}

func unicodeTextRule(l *lexer, limit int) int {
	if l.pos >= limit {
		return -1
	}
	r, size := utf8.DecodeRune(l.src[l.pos:limit])
	if size == 0 || !inUnicodeTextRange(r) {
		return -1
	}
	return l.pos + size
}

func newlineRule(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit {
		next, ok := lineEndAt(l.src, pos)
		if !ok || next > limit {
			break
		}
		pos = next
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func spaceRule(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && (l.src[pos] == ' ' || l.src[pos] == '\t') {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func accValueRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit {
		b := l.src[pos]
		if b == '\n' || b == '\r' || b == ';' || b == '#' {
			break
		}
		pos++
	}
	return pos
}

func accBlockRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != '}' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func stringRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != '"' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func mdStringRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != '"' && l.src[pos] != '`' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func oneByteUnless(open byte) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		if l.src[l.pos] == open && l.pos+1 < limit && l.src[l.pos+1] == open {
			return -1
		}
		return l.pos + 1
	}
}

func callbackNameRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != '(' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func callbackArgsRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != ')' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func emptyCallArgs(l *lexer, limit int) int {
	if l.pos >= limit || l.src[l.pos] != '(' {
		return -1
	}
	pos := skipAllSpace(l.src, l.pos+1, limit)
	if pos < limit && l.src[pos] == ')' {
		return pos + 1
	}
	return -1
}

func shapePlainRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit {
		b := l.src[pos]
		if b == '}' || b == '^' || b == '"' {
			break
		}
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func shapeQuotedRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && l.src[pos] != '"' {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func ellipseTextRun(l *lexer, limit int) int {
	pos := l.pos
	if pos < limit && isEllipsePlain(l.src[pos]) {
		return pos + 1
	}
	if matchLiteral(l.src, pos, limit, "-!)") {
		pos += 3
		for matchLiteral(l.src, pos, limit, "-!)") {
			pos += 3
		}
		return pos
	}
	return -1
}

func isEllipsePlain(b byte) bool {
	switch b {
	case '(', ')', '[', ']', '{', '}':
		return false
	}
	return true
}

func ellipseEndRule(l *lexer, limit int) int {
	if l.pos+1 >= limit {
		return -1
	}
	b := l.src[l.pos]
	if b != '-' && b != '/' && b != ')' {
		return -1
	}
	if l.src[l.pos+1] != ')' {
		return -1
	}
	return l.pos + 2
}

func trapEndRule(l *lexer, limit int) int {
	if l.pos+1 < limit && l.src[l.pos] == '\\' && l.src[l.pos+1] == ']' {
		return l.pos + 2
	}
	if l.src[l.pos] == ']' {
		return l.pos + 1
	}
	return -1
}

func invTrapEndRule(l *lexer, limit int) int {
	if l.pos+1 < limit && l.src[l.pos] == '/' && l.src[l.pos+1] == ']' {
		return l.pos + 2
	}
	return -1
}

func trapTextRun(l *lexer, limit int) int {
	pos := l.pos
	if pos < limit && isTrapPlain(l.src[pos]) {
		return pos + 1
	}
	if pos+1 < limit && (l.src[pos] == '\\' || l.src[pos] == '/') && l.src[pos+1] != ']' {
		return pos + 1
	}
	return -1
}

func isTrapPlain(b byte) bool {
	switch b {
	case '\\', '[', ']', '(', ')', '{', '}', '/':
		return false
	}
	return true
}

func textRun(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit {
		b := l.src[pos]
		if strings.ContainsRune("[](){}|\"", rune(b)) {
			break
		}
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}

func directionStatement(kw string) func(*lexer, int) int {
	return func(l *lexer, limit int) int {
		stop := l.pos
		for stop < limit && l.src[stop] != '\n' {
			stop++
		}
		for idx := findLiteral(l.src, l.pos, stop, "direction"); idx >= 0; idx = findLiteral(l.src, idx+1, stop, "direction") {
			pos := skipAllSpace(l.src, idx+len("direction"), stop)
			if pos > idx+len("direction") && matchLiteral(l.src, pos, stop, kw) {
				return lineTail(l.src, pos, limit)
			}
		}
		return -1
	}
}

func lineTail(src []byte, pos, limit int) int {
	for pos < limit && src[pos] != '\n' {
		pos++
	}
	return pos
}

func findLiteral(src []byte, from, limit int, s string) int {
	for i := from; i+len(s) <= limit; i++ {
		if matchLiteral(src, i, limit, s) {
			return i
		}
	}
	return -1
}

func colonRun(l *lexer, limit int) int {
	if matchLiteral(l.src, l.pos, limit, ":::") {
		return l.pos + 3
	}
	return -1
}

func anySpaceByte(l *lexer, limit int) int {
	if l.pos < limit && isJSSpace(l.src[l.pos]) {
		return l.pos + 1
	}
	return -1
}

func anyNonSpace(l *lexer, limit int) int {
	pos := l.pos
	for pos < limit && !isJSSpace(l.src[pos]) {
		pos++
	}
	if pos == l.pos {
		return -1
	}
	return pos
}
