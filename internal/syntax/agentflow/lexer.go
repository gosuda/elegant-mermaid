package agentflow

import (
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type lexerFrame struct {
	mode    string
	opening int
}

type scanner struct {
	source     string
	cleaned    *source.Cleaned
	at         int
	frames     []lexerFrame
	tokens     []Token
	firstGraph bool
}

func Lex(src string, removed []source.Span) []Token {
	return lex(source.Clean([]byte(src), removed))
}

func lex(cleaned *source.Cleaned) []Token {
	s := &scanner{source: string(cleaned.Text), cleaned: cleaned, firstGraph: true}
	return s.run()
}

func (s *scanner) mode() string {
	if len(s.frames) == 0 {
		return "INITIAL"
	}
	return s.frames[len(s.frames)-1].mode
}

func (s *scanner) push(mode string) {
	s.frames = append(s.frames, lexerFrame{mode: mode, opening: s.at})
}

func (s *scanner) pop() {
	if len(s.frames) > 0 {
		s.frames = s.frames[:len(s.frames)-1]
	}
}

func (s *scanner) tail() string {
	if s.at >= len(s.source) {
		return ""
	}
	return s.source[s.at:]
}

func (s *scanner) slice(n int) string {
	if s.at+n > len(s.source) || n < 0 {
		return ""
	}
	return s.source[s.at : s.at+n]
}

func (s *scanner) raw(kind string, n int) {
	s.emit(kind, n, s.slice(n))
}

func (s *scanner) emit(kind string, n int, text string) {
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: s.at, End: s.at + n}})
	s.at += n
}

func (s *scanner) lastMut() *Token {
	if len(s.tokens) == 0 {
		return nil
	}
	return &s.tokens[len(s.tokens)-1]
}

func (s *scanner) run() []Token {
	for s.at < len(s.source) {
		if !s.next() {
			_, size := utf8.DecodeRuneInString(s.tail())
			if size == 0 {
				size = 1
			}
			s.raw("INVALID", size)
		}
	}
	s.finish()
	s.raw("EOF", 0)
	for i := range s.tokens {
		s.tokens[i].Span = s.cleaned.Span(s.tokens[i].Span.Start, s.tokens[i].Span.End)
	}
	return s.tokens
}

func (s *scanner) finish() {
	for i := len(s.frames) - 1; i >= 0; i-- {
		f := s.frames[i]
		if f.mode != "dir" {
			span := source.Span{Start: f.opening, End: len(s.source)}
			s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: s.source[min(span.Start, len(s.source)):], Span: span})
			return
		}
	}
}

func (s *scanner) next() bool {
	switch s.mode() {
	case "dir":
		return s.headerDirection()
	case "string", "md_string":
		return s.quotedValue()
	case "edgeText":
		return s.edgeText()
	case "text", "ellipseText", "trapText":
		return s.label()
	default:
		return s.initial()
	}
}

func (s *scanner) initial() bool {
	return s.leading() || s.reserved() || s.content() || s.spacing()
}

func (s *scanner) leading() bool {
	return s.accessibility() || s.metadata() || s.callback() || s.quoted()
}

func (s *scanner) reserved() bool {
	return s.keywords() || s.wholeDirection() || s.linkID() || s.punctuation()
}

func (s *scanner) content() bool {
	return s.link() || s.openLabel() || s.comment() || s.identifier()
}

func (s *scanner) spacing() bool {
	t := s.tail()
	if len(t) == 0 {
		return false
	}
	if t[0] == '\r' || t[0] == '\n' {
		s.raw("NEWLINE", newlineLen(t))
		return true
	}
	c, size := utf8.DecodeRuneInString(t)
	if !isWhitespace(c) {
		return false
	}
	s.raw("SPACE", size)
	return true
}

func (s *scanner) accessibility() bool {
	for _, entry := range [...][3]string{
		{"accTitle", "acc_title", "acc_title_value"},
		{"accDescr", "acc_descr", "acc_descr_value"},
	} {
		name, kind, value := entry[0], entry[1], entry[2]
		rest, ok := cutPrefix(s.tail(), name)
		if !ok {
			continue
		}
		trimmed := trimStartWhitespace(rest)
		if strings.HasPrefix(trimmed, ":") {
			text := trimStartWhitespace(trimmed[1:])
			prefix := len(s.tail()) - len(text)
			s.raw(kind, prefix)
			s.raw(value, lineLen(s.tail()))
			return true
		}
		if name == "accDescr" && strings.HasPrefix(trimmed, "{") {
			prefix := len(s.tail()) - len(trimmed) + 1
			s.delimited("acc_descr_multiline_value", prefix, "}")
			return true
		}
	}
	return false
}

func (s *scanner) delimited(kind string, prefix int, close string) {
	body := s.tail()
	if prefix <= len(body) {
		body = body[prefix:]
	} else {
		body = ""
	}
	if n := strings.Index(body, close); n >= 0 {
		s.emit(kind, prefix+n+len(close), body[:n])
	} else {
		s.raw("UNTERMINATED", len(s.tail()))
	}
}

func (s *scanner) quoted() bool {
	if strings.HasPrefix(s.tail(), "\"`") {
		s.push("md_string")
		s.at += 2
		return true
	}
	if strings.HasPrefix(s.tail(), "\"") {
		s.push("string")
		s.at += 1
		return true
	}
	return false
}

func (s *scanner) quotedValue() bool {
	mode := s.mode()
	ts := s.tail()
	if mode == "string" && strings.HasPrefix(ts, "\"`") {
		return s.quoted()
	}
	if close := stringClose(mode); strings.HasPrefix(ts, close) {
		s.closeString(len(close))
		return true
	}
	n := stringRun(mode, ts)
	if n == 0 {
		return s.quoted()
	}
	s.stringBody(mode, n)
	return true
}

func stringClose(mode string) string {
	if mode == "md_string" {
		return "`\""
	}
	return "\""
}

func stringRun(mode, ts string) int {
	n := strings.IndexByte(ts, '"')
	if mode == "md_string" {
		n = indexAnyByte(ts, '`', '"')
	}
	if n < 0 {
		return len(ts)
	}
	return n
}

func (s *scanner) openingOffset() int {
	if len(s.frames) > 0 {
		return s.frames[len(s.frames)-1].opening
	}
	return s.at
}

func (s *scanner) closeString(width int) {
	opening := s.openingOffset()
	s.pop()
	s.at += width
	if t := s.lastMut(); t != nil && t.Span.Start == opening {
		t.Span.End = s.at
	}
}

func (s *scanner) stringBody(mode string, n int) {
	opening := s.openingOffset()
	start := s.at
	kind := "STR"
	if mode == "md_string" {
		kind = "MD_STR"
	}
	s.raw(kind, n)
	if t := s.lastMut(); t != nil {
		t.Span.Start = min(opening, start)
	}
}

func (s *scanner) metadata() bool {
	if !strings.HasPrefix(s.tail(), "@{") {
		return false
	}
	opening := s.at
	s.emit("SHAPE_DATA", 2, "")
	for s.at < len(s.source) {
		if s.metadataPiece() {
			return true
		}
	}
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: s.source[min(opening, len(s.source)):], Span: source.Span{Start: opening, End: s.at}})
	return true
}

func (s *scanner) metadataPiece() bool {
	ts := s.tail()
	if strings.HasPrefix(ts, "}") {
		s.at++
		if t := s.lastMut(); t != nil {
			t.Span.End = s.at
		}
		return true
	}
	if strings.HasPrefix(ts, "\"") {
		s.metadataString()
		return false
	}
	n := indexAnyByte(ts, '}', '^', '"')
	if n < 0 {
		n = len(ts)
	}
	if n > 0 {
		s.raw("SHAPE_DATA", n)
	} else {
		s.raw("INVALID", 1)
	}
	return false
}

func (s *scanner) metadataString() {
	s.raw("SHAPE_DATA", 1)
	n := strings.IndexByte(s.tail(), '"')
	if n < 0 {
		n = len(s.tail())
	}
	if n > 0 {
		s.raw("SHAPE_DATA", n)
	}
	if strings.HasPrefix(s.tail(), "\"") {
		s.raw("SHAPE_DATA", 1)
	}
}

func (s *scanner) callback() bool {
	ts := s.tail()
	tailText, ok := cutPrefix(ts, "call")
	if !ok {
		return false
	}
	if len(tailText) == 0 || !isWhitespaceRuneAt(tailText, 0) {
		return false
	}
	name := trimStartWhitespace(tailText)
	prefix := len(ts) - len(name)
	n := strings.IndexByte(name, '(')
	if n < 0 {
		n = len(name)
	}
	s.emit("CALLBACKNAME", prefix+n, name[:n])
	if !strings.HasPrefix(s.tail(), "(") {
		return true
	}
	rest := s.tail()[1:]
	n = strings.IndexByte(rest, ')')
	if n < 0 {
		s.raw("UNTERMINATED", len(s.tail()))
		return true
	}
	value := rest[:n]
	if strings.TrimSpace(value) == "" {
		s.at += n + 2
	} else {
		s.emit("CALLBACKARGS", n+2, value)
	}
	return true
}

func (s *scanner) keywords() bool {
	ts := s.tail()
	for _, entry := range [...][2]string{
		{"style", "STYLE"},
		{"default", "DEFAULT"},
		{"linkStyle", "LINKSTYLE"},
		{"interpolate", "INTERPOLATE"},
		{"classDef", "CLASSDEF"},
		{"class", "CLASS"},
	} {
		literal, kind := entry[0], entry[1]
		if strings.HasPrefix(ts, literal) && wordBoundary(cutAt(ts, len(literal))) {
			s.raw(kind, len(literal))
			return true
		}
	}
	if s.hrefOrClick() {
		return true
	}
	if strings.HasPrefix(ts, "agentflow-beta") && headerBoundary(cutAt(ts, 14)) {
		if s.firstGraph {
			s.push("dir")
			s.firstGraph = false
		}
		s.raw("GRAPH", 14)
		return true
	}
	return s.remainingKeywords()
}

func (s *scanner) hrefOrClick() bool {
	return s.hrefKeyword() || s.clickKeyword()
}

func (s *scanner) hrefKeyword() bool {
	t, ok := cutPrefix(s.tail(), "href")
	if !ok || !isWhitespaceRuneAt(t, 0) {
		return false
	}
	_, size := utf8.DecodeRuneInString(t)
	s.raw("HREF", 4+size)
	return true
}

func (s *scanner) clickKeyword() bool {
	ts := s.tail()
	t, ok := cutPrefix(ts, "click")
	if !ok || !isWhitespaceRuneAt(t, 0) {
		return false
	}
	id := trimStartWhitespace(t)
	n := indexWhitespace(id)
	if n < 0 {
		n = len(id)
	}
	s.emit("CLICK", len(ts)-len(id)+n, id[:n])
	if rest := s.tail(); isWhitespaceRuneAt(rest, 0) {
		_, size := utf8.DecodeRuneInString(rest)
		s.at += size
	}
	return true
}

func (s *scanner) remainingKeywords() bool {
	ts := s.tail()
	for _, entry := range [...][2]string{
		{"flow", "flow"},
		{"connector", "connector"},
		{"global", "global"},
		{"end", "end"},
		{"_self", "LINK_TARGET"},
		{"_blank", "LINK_TARGET"},
		{"_parent", "LINK_TARGET"},
		{"_top", "LINK_TARGET"},
	} {
		literal, kind := entry[0], entry[1]
		if !strings.HasPrefix(ts, literal) {
			continue
		}
		tailText := cutAt(ts, len(literal))
		if !wordBoundary(tailText) {
			continue
		}
		n := len(literal)
		if kind == "global" || kind == "end" {
			trimmed := strings.TrimLeft(tailText, " \t")
			n = len(literal) + len(tailText) - len(trimmed)
		}
		s.raw(kind, n)
		return true
	}
	return false
}

func (s *scanner) headerDirection() bool {
	ts := s.tail()
	t := trimStartWhitespace(ts)
	whitespace := len(ts) - len(t)
	if strings.ContainsAny(ts[:whitespace], "\r\n") {
		s.pop()
		s.raw("NODIR", whitespace)
		return true
	}
	for _, d := range [...]string{"LR", "RL", "TB", "BT", "TD", "BR", "<", ">", "^", "v"} {
		if strings.HasPrefix(t, d) {
			s.pop()
			s.raw("DIR", whitespace+len(d))
			return true
		}
	}
	return false
}

func (s *scanner) wholeDirection() bool {
	ts := s.tail()
	line := cutAt(ts, lineLen(ts))
	for _, entry := range [...][2]string{
		{"TB", "direction_tb"},
		{"BT", "direction_bt"},
		{"RL", "direction_rl"},
		{"LR", "direction_lr"},
		{"TD", "direction_td"},
	} {
		axis, kind := entry[0], entry[1]
		at := 0
		for {
			p := strings.Index(line[at:], "direction")
			if p < 0 {
				break
			}
			p += at
			at = p + 1
			t := cutAt(line, p+9)
			if len(t) > 0 && isWhitespaceRuneAt(t, 0) && strings.HasPrefix(trimStartWhitespace(t), axis) {
				s.raw(kind, len(line))
				return true
			}
		}
	}
	return false
}

func (s *scanner) linkID() bool {
	ts := s.tail()
	n := indexAnyByte(ts, ' ', '\t', '\r', '\n', '"')
	if n < 0 {
		n = len(ts)
	}
	run := ts[:n]
	p := strings.LastIndexByte(run, '@')
	if p < 0 {
		return false
	}
	if p == 0 {
		return false
	}
	next := cutAt(ts, p+1)
	if len(next) == 0 {
		return false
	}
	c, _ := utf8.DecodeRuneInString(next)
	if c == '{' || c == '"' {
		return false
	}
	s.raw("LINK_ID", p+1)
	return true
}

func (s *scanner) punctuation() bool {
	ts := s.tail()
	n := 0
	for n < len(ts) && ts[n] >= '0' && ts[n] <= '9' {
		n++
	}
	if n > 0 {
		s.raw("NUM", n)
		return true
	}
	for _, entry := range [...][2]string{
		{"#", "BRKT"},
		{":::", "STYLE_SEPARATOR"},
		{":", "COLON"},
		{"&", "AMP"},
		{";", "SEMI"},
		{",", "COMMA"},
		{"*", "MULT"},
	} {
		if strings.HasPrefix(ts, entry[0]) {
			s.raw(entry[1], len(entry[0]))
			return true
		}
	}
	return false
}

func (s *scanner) link() bool {
	ts := s.tail()
	t := trimStartWhitespace(ts)
	prefix := len(ts) - len(t)
	hyphens := 0
	for hyphens < len(t) && t[hyphens] == '-' {
		hyphens++
	}
	suffix := cutAt(t, hyphens)
	if hyphens >= 2 && len(suffix) > 0 && (suffix[0] == 'x' || suffix[0] == '>') {
		s.pop()
		rest := suffix[1:]
		trimmed := trimStartWhitespace(rest)
		s.raw("LINK", prefix+hyphens+1+len(rest)-len(trimmed))
		return true
	}
	if strings.HasPrefix(t, "--") {
		s.frames = append(s.frames, lexerFrame{mode: "edgeText", opening: s.at + prefix})
		rest := t[2:]
		trimmed := trimStartWhitespace(rest)
		s.raw("START_LINK", prefix+2+len(rest)-len(trimmed))
		return true
	}
	return s.dottedLink(prefix, t)
}

func (s *scanner) dottedLink(prefix int, t string) bool {
	rest, ok := cutPrefix(t, "-")
	if !ok {
		return false
	}
	dots := 0
	for dots < len(rest) && rest[dots] == '.' {
		dots++
	}
	tailText := cutAt(rest, dots)
	if dots == 0 || !strings.HasPrefix(tailText, "-") {
		return false
	}
	after := tailText[1:]
	trimmed := trimStartWhitespace(after)
	s.raw("LINK", prefix+dots+2+len(after)-len(trimmed))
	return true
}

func (s *scanner) edgeText() bool {
	ts := s.tail()
	if linkAhead(trimStartWhitespace(ts)) {
		return s.link()
	}
	if s.quoted() || s.openLabel() {
		return true
	}
	if strings.HasPrefix(ts, "--") {
		return false
	}
	_, size := decodeRune(ts)
	s.raw("EDGE_TEXT", size)
	return true
}

func linkAhead(t string) bool {
	n := 0
	for n < len(t) && t[n] == '-' {
		n++
	}
	return n >= 2 && n < len(t) && (t[n] == 'x' || t[n] == '>')
}

func (s *scanner) openLabel() bool {
	ts := s.tail()
	if s.mode() == "INITIAL" && strings.HasPrefix(ts, "[|") {
		s.raw("VERTEX_WITH_PROPS_START", 2)
		return true
	}
	if s.mode() == "INITIAL" && strings.HasPrefix(ts, ">") {
		s.push("text")
		s.raw("TAGEND", 1)
		return true
	}
	for _, entry := range [...][3]string{
		{"(-", "(-", "ellipseText"},
		{"([", "STADIUMSTART", "text"},
		{"[[", "SUBROUTINESTART", "text"},
		{"[(", "CYLINDERSTART", "text"},
		{"(((", "DOUBLECIRCLESTART", "text"},
		{"[/", "TRAPSTART", "trapText"},
		{"[\\", "INVTRAPSTART", "trapText"},
		{"|", "PIPE", "text"},
		{"(", "PS", "text"},
		{"[", "SQS", "text"},
		{"{", "DIAMOND_START", "text"},
	} {
		if strings.HasPrefix(ts, entry[0]) {
			s.push(entry[2])
			s.raw(entry[1], len(entry[0]))
			return true
		}
	}
	return false
}

func (s *scanner) label() bool {
	if s.labelClose() || s.quoted() || s.labelComment() {
		return true
	}
	if s.openLabel() {
		return true
	}
	n := s.labelTextLen()
	if n == 0 {
		return false
	}
	s.raw("TEXT", n)
	return true
}

func (s *scanner) labelClose() bool {
	var choices [][2]string
	switch s.mode() {
	case "ellipseText":
		choices = [][2]string{{"-)", "-)"}, {"/)", "-)"}, {"))", "-)"}}
	case "trapText":
		choices = [][2]string{{"\\]", "TRAPEND"}, {")]", "TRAPEND"}, {"/]", "INVTRAPEND"}}
	default:
		choices = [][2]string{
			{"])", "STADIUMEND"}, {"]]", "SUBROUTINEEND"}, {")]", "CYLINDEREND"},
			{")))", "DOUBLECIRCLEEND"}, {"|", "PIPE"}, {")", "PE"}, {"]", "SQE"}, {"}", "DIAMOND_STOP"},
		}
	}
	for _, entry := range choices {
		if strings.HasPrefix(s.tail(), entry[0]) {
			s.pop()
			s.raw(entry[1], len(entry[0]))
			return true
		}
	}
	return false
}

func (s *scanner) labelTextLen() int {
	ts := s.tail()
	mode := s.mode()
	if mode == "ellipseText" {
		return ellipseTextLen(ts)
	}
	if mode == "trapText" && len(ts) > 0 && (ts[0] == '/' || ts[0] == '\\') {
		return 1
	}
	return labelRunLen(mode, ts)
}

func ellipseTextLen(ts string) int {
	if len(ts) == 0 {
		return 0
	}
	c, size := utf8.DecodeRuneInString(ts)
	if labelStructure("ellipseText", c) {
		return 0
	}
	return size
}

func labelRunLen(mode, ts string) int {
	n := 0
	for n < len(ts) {
		c, size := utf8.DecodeRuneInString(ts[n:])
		if labelStructure(mode, c) || strings.HasPrefix(ts[n:], "%%") {
			break
		}
		n += size
	}
	return n
}

func (s *scanner) labelComment() bool {
	if !strings.HasPrefix(s.tail(), "%%") || strings.HasPrefix(s.tail(), "%%{") {
		return false
	}
	s.at += lineLen(s.tail())
	return true
}

func (s *scanner) comment() bool {
	ts := s.tail()
	t := strings.TrimLeft(ts, " \t")
	if !strings.HasPrefix(t, "%%") || strings.HasPrefix(t, "%%{") {
		return false
	}
	s.raw("COMMENT", lineLen(ts))
	return true
}

func (s *scanner) identifier() bool {
	return s.directionWord() || s.nodeString() || s.minus() || s.unicodeText()
}

func (s *scanner) directionWord() bool {
	ts := s.tail()
	for _, entry := range [...][2]string{{"<", "TAGSTART"}, {"^", "UP"}, {"v", "DOWN"}} {
		literal, kind := entry[0], entry[1]
		if !strings.HasPrefix(ts, literal) {
			continue
		}
		if literal == "v" && !wordBoundary(cutAt(ts, 1)) {
			continue
		}
		s.raw(kind, 1)
		return true
	}
	return false
}

func (s *scanner) nodeString() bool {
	ts := s.tail()
	n := 0
	for n < len(ts) {
		c, size := utf8.DecodeRuneInString(ts[n:])
		if !asciiID(c, ts[n+size:]) {
			break
		}
		n += size
	}
	if n == 0 {
		return false
	}
	s.raw("NODE_STRING", n)
	return true
}

func (s *scanner) minus() bool {
	if !strings.HasPrefix(s.tail(), "-") {
		return false
	}
	s.raw("MINUS", 1)
	return true
}

func (s *scanner) unicodeText() bool {
	ts := s.tail()
	if len(ts) == 0 {
		return false
	}
	c, size := utf8.DecodeRuneInString(ts)
	if !unicodeLetter(c) {
		return false
	}
	s.raw("UNICODE_TEXT", size)
	return true
}

func labelStructure(mode string, c rune) bool {
	switch mode {
	case "ellipseText":
		return strings.ContainsRune("()[]{}", c)
	case "trapText":
		return strings.ContainsRune("()[]{}/\\\"", c)
	default:
		return strings.ContainsRune("()[]{}|\"", c)
	}
}

func asciiID(c rune, tail string) bool {
	if isASCIIAlnum(c) {
		return true
	}
	if strings.ContainsRune("!\"#$%&'*+.`?\\_/", c) {
		return true
	}
	if c == '-' {
		return hyphenContinues(tail)
	}
	if c == '=' {
		return !strings.HasPrefix(tail, "=")
	}
	return false
}

func hyphenContinues(tail string) bool {
	return len(tail) > 0 && !strings.HasPrefix(tail, ">") && !strings.HasPrefix(tail, "-") && !strings.HasPrefix(tail, ".")
}

func isASCIIAlnum(c rune) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

func lineLen(s string) int {
	if n := strings.IndexAny(s, "\r\n"); n >= 0 {
		return n
	}
	return len(s)
}

func newlineLen(s string) int {
	n := 0
	for n < len(s) && (s[n] == '\r' || s[n] == '\n') {
		n++
	}
	return n
}

func wordBoundary(s string) bool {
	if len(s) == 0 {
		return true
	}
	c, _ := utf8.DecodeRuneInString(s)
	return !isASCIIAlnum(c) && c != '_'
}

func headerBoundary(s string) bool {
	if len(s) == 0 {
		return true
	}
	c, _ := utf8.DecodeRuneInString(s)
	return !isASCIIAlnum(c) && c != '-' && c != '_'
}

func isWhitespace(c rune) bool { return unicode.IsSpace(c) }

func isWhitespaceRuneAt(s string, at int) bool {
	if at >= len(s) {
		return false
	}
	c, _ := utf8.DecodeRuneInString(s[at:])
	return unicode.IsSpace(c)
}

func trimStartWhitespace(s string) string {
	return strings.TrimLeftFunc(s, unicode.IsSpace)
}

func indexWhitespace(s string) int {
	for at, c := range s {
		if unicode.IsSpace(c) {
			return at
		}
	}
	return -1
}

func indexAnyByte(s string, needles ...byte) int {
	for i := 0; i < len(s); i++ {
		for _, n := range needles {
			if s[i] == n {
				return i
			}
		}
	}
	return -1
}

func cutPrefix(s, prefix string) (string, bool) {
	if strings.HasPrefix(s, prefix) {
		return s[len(prefix):], true
	}
	return "", false
}

func cutAt(s string, at int) string {
	if at < 0 {
		return ""
	}
	if at >= len(s) {
		return ""
	}
	return s[at:]
}

func decodeRune(s string) (rune, int) {
	c, size := utf8.DecodeRuneInString(s)
	if c == utf8.RuneError && size == 0 {
		return utf8.RuneError, 1
	}
	return c, size
}
