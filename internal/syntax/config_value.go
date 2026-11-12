package syntax

import (
	"math"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const configMaxDepth = 64

const (
	codeMalformed   = "config/malformed"
	codeAnchor      = "config/unsupported-anchor"
	codeTag         = "config/unsupported-tag"
	codeDepth       = "limit/nesting-depth"
	codeInvalidUTF8 = "source/invalid-utf8"
)

const (
	msgMalformed      = "malformed config value"
	msgTabIndent      = "tab in indentation"
	msgBlockSequence  = "block sequences are not supported"
	msgComplexKey     = "complex keys are not supported"
	msgMultiDocument  = "multi-document streams are not supported"
	msgBlockIndent    = "block scalar indentation indicator is not supported"
	msgInvalidEscape  = "invalid escape"
	msgUnicodeEscape  = "invalid unicode escape"
	msgDuplicateKey   = "duplicate key"
	msgFrontmatterMap = "frontmatter config must be a mapping"
	msgDirective      = "malformed directive"
	msgWrapBody       = "wrap takes no body"
	msgDirectiveBody  = "directive body must be a JSON object"
	msgAnchor         = "anchors and aliases are not supported"
	msgTag            = "tags are not supported"
	msgDepth          = "nesting depth exceeds 64"
)

type ValueKind uint8

const (
	ValueNull ValueKind = iota
	ValueBool
	ValueInteger
	ValueDecimal
	ValueString
	ValueSequence
	ValueMapping
)

type ConfigEntry struct {
	Key     string
	KeySpan source.Span
	Value   ConfigValue
}

type ConfigValue struct {
	Kind    ValueKind
	Bool    bool
	Text    string
	Items   []ConfigValue
	Entries []ConfigEntry
	Span    source.Span
}

var simpleEscapes = map[byte]byte{
	'"':  '"',
	'\\': '\\',
	'/':  '/',
	'b':  '\b',
	'f':  '\f',
	'n':  '\n',
	'r':  '\r',
	't':  '\t',
}

type configReader struct {
	src      []byte
	start    int
	pos      int
	end      int
	origin   int
	depth    int
	jsonMode bool
	diags    []diag.Diagnostic
	failed   bool
}

func clampSpanBounds(at, limit int) int {
	if at < 0 {
		return 0
	}
	if at > limit {
		return limit
	}
	return at
}

func newConfigReader(src []byte, start, end, origin int) *configReader {
	start = clampSpanBounds(start, len(src))
	end = clampSpanBounds(end, len(src))
	if start > end {
		start = end
	}
	return &configReader{src: src, start: start, pos: start, end: end, origin: origin}
}

func (r *configReader) lineIndentAt(p int) int {
	i := clampSpanBounds(p, r.end)
	for i > r.start && !isLineBreak(r.src[i-1]) {
		i--
	}
	return p - i
}

func configDiagnostic(code, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span}
}

func (r *configReader) span(a, b int) source.Span {
	return source.Span{
		Start: r.origin + clampSpanBounds(a, r.end),
		End:   r.origin + clampSpanBounds(b, r.end),
	}
}

func (r *configReader) posSpan(at int) source.Span {
	p := clampSpanBounds(at, r.end)
	return source.Span{Start: r.origin + p, End: r.origin + p}
}

func (r *configReader) fail(code, message string, span source.Span) {
	r.diags = append(r.diags, configDiagnostic(code, message, span))
	r.failed = true
}

func (r *configReader) note(code, message string, span source.Span) {
	r.diags = append(r.diags, configDiagnostic(code, message, span))
}

func configTokenSpan(src []byte, p, end, origin int) source.Span {
	p = clampSpanBounds(p, len(src))
	end = clampSpanBounds(end, len(src))
	if p >= end {
		return source.Span{Start: origin + end, End: origin + end}
	}
	switch src[p] {
	case '\r':
		return source.Span{Start: origin + p, End: origin + crlfLength(src[p:end])}
	case ' ', '\t', '\n':
		return source.Span{Start: origin + p, End: origin + p + 1}
	}
	i := p
	for i < end && !isConfigSpace(src[i]) {
		i++
	}
	return source.Span{Start: origin + p, End: origin + i}
}

func crlfLength(rest []byte) int {
	if len(rest) > 1 && rest[0] == '\r' && rest[1] == '\n' {
		return 2
	}
	return 1
}

func (r *configReader) tokenSpan(p int) source.Span {
	return configTokenSpan(r.src, p, r.end, r.origin)
}

func (r *configReader) failMalformed(p int) {
	r.fail(codeMalformed, msgMalformed, r.tokenSpan(p))
}

func (r *configReader) failTab(p int) {
	r.fail(codeMalformed, msgTabIndent, r.span(p, p+1))
}

func (r *configReader) enter(open int) bool {
	r.depth++
	if r.depth > configMaxDepth {
		r.fail(codeDepth, msgDepth, r.span(open, open+1))
		return false
	}
	return true
}

func (r *configReader) leave() {
	r.depth--
}

func isConfigSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func isLineBreak(b byte) bool {
	return b == '\r' || b == '\n'
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

func isNameByte(b byte) bool {
	if b >= 'a' && b <= 'z' {
		return true
	}
	if b >= 'A' && b <= 'Z' {
		return true
	}
	if b >= '0' && b <= '9' {
		return true
	}
	return b == '_'
}

func splitLine(src []byte, start, end int) (content int, next int) {
	for i := start; i < end; i++ {
		if src[i] == '\n' {
			return i, i + 1
		}
		if src[i] == '\r' {
			return i, i + crlfLength(src[i:end])
		}
	}
	return end, end
}

func lineStart(src []byte, p int) int {
	i := clampSpanBounds(p, len(src))
	for i > 0 && !isLineBreak(src[i-1]) {
		i--
	}
	return i
}

func (r *configReader) atNodeBreak(p int) bool {
	return p >= r.end || isConfigSpace(r.src[p])
}

func (r *configReader) atWhitespace(p int) bool {
	return p < r.end && isConfigSpace(r.src[p])
}

func (r *configReader) anchorEnd(p int) int {
	i := p + 1
	for i < r.end && (isNameByte(r.src[i]) || r.src[i] == '-') {
		i++
	}
	return i
}

func (r *configReader) tagEnd(p int) int {
	i := p + 1
	for i < r.end && !tagStop(r.src[i]) {
		i++
	}
	return i
}

func tagStop(b byte) bool {
	if isConfigSpace(b) {
		return true
	}
	switch b {
	case ',', '[', ']', '{', '}':
		return true
	}
	return false
}

func (r *configReader) markerAt(p int) bool {
	if r.end-p < 3 || p != lineStart(r.src, p) {
		return false
	}
	head := string(r.src[p : p+3])
	if head != "---" && head != "..." {
		return false
	}
	return r.atNodeBreak(p + 3)
}

func (r *configReader) nodePrefixFails(p int) bool {
	if p >= r.end {
		return false
	}
	return r.prefixFailsAt(p)
}

func (r *configReader) prefixFailsAt(p int) bool {
	switch r.src[p] {
	case '&', '*':
		r.fail(codeAnchor, msgAnchor, r.span(p, r.anchorEnd(p)))
		return true
	case '!':
		r.fail(codeTag, msgTag, r.span(p, r.tagEnd(p)))
		return true
	}
	return r.structureFailsAt(p)
}

func (r *configReader) structureFailsAt(p int) bool {
	if r.markerAt(p) {
		r.fail(codeMalformed, msgMultiDocument, r.span(p, p+3))
		return true
	}
	if r.src[p] != '-' && r.src[p] != '?' {
		return false
	}
	if !r.atWhitespace(p + 1) {
		return false
	}
	message := msgBlockSequence
	if r.src[p] == '?' {
		message = msgComplexKey
	}
	r.fail(codeMalformed, message, r.span(p, p+1))
	return true
}

const plainForbidden = "[]{}#|>'\",%@`"

func (r *configReader) plainStartFails(p int) bool {
	if p >= r.end {
		return true
	}
	b := r.src[p]
	if strings.IndexByte(plainForbidden, b) >= 0 {
		return true
	}
	if b != '-' && b != '?' && b != ':' {
		return false
	}
	return r.atWhitespace(p + 1)
}

func resolvePlain(text string, span source.Span) ConfigValue {
	if isNullText(text) {
		return ConfigValue{Kind: ValueNull, Span: span}
	}
	if value, ok := boolText(text); ok {
		return ConfigValue{Kind: ValueBool, Bool: value, Span: span}
	}
	if isNumberText(text) {
		return resolveNumber(text, span)
	}
	return ConfigValue{Kind: ValueString, Text: text, Span: span}
}

func resolveNumber(text string, span source.Span) ConfigValue {
	if strings.ContainsAny(text, ".eE") {
		return ConfigValue{Kind: ValueDecimal, Text: text, Span: span}
	}
	return ConfigValue{Kind: ValueInteger, Text: text, Span: span}
}

func isNullText(text string) bool {
	switch text {
	case "", "null", "Null", "NULL", "~":
		return true
	}
	return false
}

func boolText(text string) (bool, bool) {
	switch text {
	case "true", "True", "TRUE":
		return true, true
	case "false", "False", "FALSE":
		return false, true
	}
	return false, false
}

func readDigits(text string, i int) (next int, digits string) {
	start := i
	for i < len(text) && isDigit(text[i]) {
		i++
	}
	return i, text[start:i]
}

func isNumberText(text string) bool {
	i := skipSign(text)
	next, whole := readDigits(text, i)
	if whole == "" {
		return false
	}
	i = next
	if i >= len(text) {
		return true
	}
	if text[i] != '.' {
		return false
	}
	next, frac := readDigits(text, i+1)
	return frac != "" && next == len(text)
}

func skipSign(text string) int {
	if text == "" {
		return 0
	}
	if text[0] == '-' || text[0] == '+' {
		return 1
	}
	return 0
}

func hexDigit(b byte) (int, bool) {
	switch b {
	case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9':
		return int(b - '0'), true
	case 'a', 'b', 'c', 'd', 'e', 'f':
		return int(b-'a') + 10, true
	case 'A', 'B', 'C', 'D', 'E', 'F':
		return int(b-'A') + 10, true
	}
	return 0, false
}

func hex4(src []byte, p, limit int) (int, bool) {
	if p+4 > limit {
		return 0, false
	}
	value := 0
	for i := p; i < p+4; i++ {
		digit, ok := hexDigit(src[i])
		if !ok {
			return 0, false
		}
		value = value<<4 | digit
	}
	return value, true
}

func (r *configReader) readEscape(b *strings.Builder) bool {
	p := r.pos
	if p+1 >= r.end {
		r.fail(codeMalformed, msgInvalidEscape, r.span(p, r.end))
		return false
	}
	if r.src[p+1] == 'u' {
		return r.readUnicodeEscape(b, p)
	}
	decoded, ok := simpleEscapes[r.src[p+1]]
	if !ok {
		r.fail(codeMalformed, msgInvalidEscape, r.span(p, p+2))
		return false
	}
	b.WriteByte(decoded)
	r.pos = p + 2
	return true
}

func (r *configReader) readUnicodeEscape(b *strings.Builder, p int) bool {
	if p+6 > r.end {
		r.fail(codeMalformed, msgInvalidEscape, r.span(p, p+2))
		return false
	}
	value, ok := hex4(r.src, p+2, r.end)
	if !ok {
		r.fail(codeMalformed, msgInvalidEscape, r.span(p, p+2))
		return false
	}
	if value >= 0xD800 && value <= 0xDFFF {
		return r.surrogateEscape(b, p, value)
	}
	b.WriteRune(rune(value))
	r.pos = p + 6
	return true
}

func (r *configReader) surrogateEscape(b *strings.Builder, p, value int) bool {
	if !r.jsonMode || value > 0xDBFF || p+12 > r.end {
		r.fail(codeMalformed, msgUnicodeEscape, r.span(p, p+6))
		return false
	}
	low, ok := hex4(r.src, p+8, r.end)
	if !ok || r.src[p+6] != '\\' || r.src[p+7] != 'u' || low < 0xDC00 || low > 0xDFFF {
		r.fail(codeMalformed, msgUnicodeEscape, r.span(p, p+6))
		return false
	}
	b.WriteRune(rune(0x10000 + (value-0xD800)<<10 + (low - 0xDC00)))
	r.pos = p + 12
	return true
}

func (r *configReader) parseDoubleQuoted() (ConfigValue, bool) {
	start := r.pos
	r.pos++
	var b strings.Builder
	for r.pos < r.end {
		c := r.src[r.pos]
		if c == '"' {
			r.pos++
			return ConfigValue{Kind: ValueString, Text: b.String(), Span: r.span(start, r.pos)}, true
		}
		if r.readQuotedByte(&b, c) {
			continue
		}
		return ConfigValue{}, false
	}
	r.failMalformed(r.end)
	return ConfigValue{}, false
}

func (r *configReader) readQuotedByte(b *strings.Builder, c byte) bool {
	if c == '\\' {
		return r.readEscape(b)
	}
	if c < 0x20 {
		r.failMalformed(r.pos)
		return false
	}
	b.WriteByte(c)
	r.pos++
	return true
}

func (r *configReader) parseSingleQuoted() (ConfigValue, bool) {
	start := r.pos
	r.pos++
	var b strings.Builder
	for r.pos < r.end {
		c := r.src[r.pos]
		if c < 0x20 {
			r.failMalformed(r.pos)
			return ConfigValue{}, false
		}
		if r.readSingleByte(&b, c) {
			return ConfigValue{Kind: ValueString, Text: b.String(), Span: r.span(start, r.pos)}, true
		}
	}
	r.failMalformed(r.end)
	return ConfigValue{}, false
}

func (r *configReader) readSingleByte(b *strings.Builder, c byte) bool {
	if c != '\'' {
		b.WriteByte(c)
		r.pos++
		return false
	}
	if r.pos+1 < r.end && r.src[r.pos+1] == '\'' {
		b.WriteByte('\'')
		r.pos += 2
		return false
	}
	r.pos++
	return true
}

func findEntry(m ConfigValue, key string) int {
	for i := range m.Entries {
		if m.Entries[i].Key == key {
			return i
		}
	}
	return -1
}

func (r *configReader) appendEntry(out *ConfigValue, key string, keySpan source.Span, value ConfigValue) {
	if i := findEntry(*out, key); i >= 0 {
		out.Entries[i].Value = value
		r.note(codeMalformed, msgDuplicateKey, keySpan)
		return
	}
	out.Entries = append(out.Entries, ConfigEntry{Key: key, KeySpan: keySpan, Value: value})
}

func firstInvalidUTF8(src []byte, start, end int) int {
	for i := start; i < end; {
		r, size := utf8.DecodeRune(src[i:end])
		if r == utf8.RuneError && size <= 1 {
			return i
		}
		i += size
	}
	return -1
}

func emptyMappingAt(at int) ConfigValue {
	return ConfigValue{Kind: ValueMapping, Span: source.Span{Start: at, End: at}}
}

func emptyNullAt(at int) ConfigValue {
	return ConfigValue{Kind: ValueNull, Span: source.Span{Start: at, End: at}}
}

func invalidUTF8Message(offset int) string {
	return "invalid UTF-8 at byte " + strconv.Itoa(offset)
}

type numberText struct {
	negative bool
	whole    string
	fraction string
	exponent int64
}

const exponentClamp = 999999999

func skipSignAt(text string, i int) int {
	if i < len(text) && (text[i] == '-' || text[i] == '+') {
		return 1
	}
	return 0
}

func readExponent(text string, i int) (int64, int, bool) {
	negative := i < len(text) && text[i] == '-'
	i += skipSignAt(text, i)
	next, digits := readDigits(text, i)
	if digits == "" {
		return 0, 0, false
	}
	value := int64(exponentClamp)
	if len(digits) <= 9 {
		parsed, err := strconv.ParseInt(digits, 10, 64)
		if err != nil {
			return 0, 0, false
		}
		value = parsed
	}
	if negative {
		value = -value
	}
	return value, next, true
}

func splitNumberText(text string) (numberText, bool) {
	var n numberText
	i := skipSign(text)
	n.negative = i == 1 && text[0] == '-'
	next, whole := readDigits(text, i)
	if whole == "" {
		return numberText{}, false
	}
	n.whole = whole
	i = next
	if i < len(text) && text[i] == '.' {
		next, frac := readDigits(text, i+1)
		if frac == "" {
			return numberText{}, false
		}
		n.fraction = frac
		i = next
	}
	if i < len(text) && (text[i] == 'e' || text[i] == 'E') {
		exp, after, ok := readExponent(text, i+1)
		if !ok {
			return numberText{}, false
		}
		n.exponent = exp
		i = after
	}
	return n, i == len(text)
}

func incrementDecimal(s string) string {
	b := []byte(s)
	for i := len(b) - 1; i >= 0; i-- {
		if b[i] < '9' {
			b[i]++
			return string(b)
		}
		b[i] = '0'
	}
	return "1" + string(b)
}

func roundedPrefix(digits string, cut int) string {
	if len(digits) < cut {
		return "0"
	}
	prefix := digits[:len(digits)-cut]
	if digits[len(digits)-cut] < '5' {
		return prefix
	}
	if prefix == "" {
		return "1"
	}
	return incrementDecimal(prefix)
}

func signedThousandths(negative bool, digits string) (int32, bool) {
	if len(digits) > 10 {
		return 0, false
	}
	value, err := strconv.ParseInt(digits, 10, 64)
	if err != nil || value > math.MaxInt32 {
		return 0, false
	}
	if value == 0 {
		return 0, true
	}
	if negative {
		return int32(-value), true
	}
	return int32(value), true
}

func Thousandths(v ConfigValue) (int32, bool) {
	if v.Kind != ValueInteger && v.Kind != ValueDecimal {
		return 0, false
	}
	n, ok := splitNumberText(v.Text)
	if !ok {
		return 0, false
	}
	digits := strings.TrimLeft(n.whole+n.fraction, "0")
	if digits == "" {
		return 0, true
	}
	shift := n.exponent - int64(len(n.fraction)) + 3
	if shift > 10 {
		return 0, false
	}
	if shift >= 0 {
		return signedThousandths(n.negative, digits+strings.Repeat("0", int(shift)))
	}
	return signedThousandths(n.negative, roundedPrefix(digits, int(-shift)))
}
