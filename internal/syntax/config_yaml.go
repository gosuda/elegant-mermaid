package syntax

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type blockStyle uint8

const (
	blockLiteral blockStyle = iota
	blockFolded
)

type chompMode uint8

const (
	chompClip chompMode = iota
	chompStrip
	chompKeep
)

func ParseConfigYAML(src []byte, start, end int) (ConfigValue, []diag.Diagnostic) {
	value, diags, _ := parseConfigYAML(src, start, end)
	return value, diags
}

func parseConfigYAML(src []byte, start, end int) (ConfigValue, []diag.Diagnostic, bool) {
	r := newConfigReader(src, start, end, 0)
	if at := firstInvalidUTF8(r.src, r.pos, r.end); at >= 0 {
		r.fail(codeInvalidUTF8, invalidUTF8Message(r.origin+at), r.span(at, at+1))
		return emptyNullAt(r.origin + at), r.diags, false
	}
	value, ok := r.parseYAMLDocument()
	if !ok {
		return emptyNullAt(r.origin + r.end), r.diags, false
	}
	return value, r.diags, true
}

func (r *configReader) parseYAMLDocument() (ConfigValue, bool) {
	if !r.skipBlankAndComments() {
		return ConfigValue{}, false
	}
	if r.pos >= r.end {
		return emptyMappingAt(r.origin + r.end), true
	}
	if !r.yamlSequenceAt(r.pos) && r.nodePrefixFails(r.pos) {
		return ConfigValue{}, false
	}
	col := r.lineIndentAt(r.pos)
	return r.parseYAMLRoot(col)
}

func (r *configReader) parseYAMLRoot(col int) (ConfigValue, bool) {
	if r.yamlSequenceAt(r.pos) {
		value, ok := r.parseYAMLBlockSequence(col)
		if !ok || !r.requireEnd() {
			return ConfigValue{}, false
		}
		return value, true
	}
	switch r.src[r.pos] {
	case '[', '{':
		return r.parseRootFlow(col)
	}
	lineContent, _ := splitLine(r.src, r.pos, r.end)
	if keyColonAt(r.src, r.pos, lineContent) >= 0 {
		return r.parseRootBlockMap(col)
	}
	return r.parseRootScalar()
}

func (r *configReader) parseRootBlockMap(col int) (ConfigValue, bool) {
	value, ok := r.parseYAMLBlockMap(col)
	if !ok || !r.requireEnd() {
		return ConfigValue{}, false
	}
	return value, true
}

func (r *configReader) parseRootFlow(col int) (ConfigValue, bool) {
	value, ok := r.parseYAMLFlow(col)
	if !ok || !r.finishLineValue() {
		return ConfigValue{}, false
	}
	if !r.requireEnd() {
		return ConfigValue{}, false
	}
	return value, true
}

func (r *configReader) parseRootScalar() (ConfigValue, bool) {
	value, ok := r.parseYAMLScalar(r.lineIndentAt(r.pos) - 1)
	if !ok || !r.requireEnd() {
		return ConfigValue{}, false
	}
	return value, true
}

func (r *configReader) requireEnd() bool {
	if !r.skipBlankAndComments() {
		return false
	}
	if r.pos >= r.end {
		return true
	}
	if r.markerAt(r.pos) {
		r.fail(codeMalformed, msgMultiDocument, r.span(r.pos, r.pos+3))
		return false
	}
	r.failMalformed(r.pos)
	return false
}

func (r *configReader) parseYAMLBlockMap(col int) (ConfigValue, bool) {
	start := r.pos
	if !r.enter(start) {
		return ConfigValue{}, false
	}
	out := ConfigValue{Kind: ValueMapping}
	if !r.parseBlockMapEntry(col, &out) {
		return ConfigValue{}, false
	}
	for {
		more, ok := r.nextMapEntry(col)
		if !ok {
			return ConfigValue{}, false
		}
		if !more {
			break
		}
		if !r.parseBlockMapEntry(col, &out) {
			return ConfigValue{}, false
		}
	}
	r.leave()
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) nextMapEntry(col int) (bool, bool) {
	if !r.skipBlankAndComments() {
		return false, false
	}
	if r.pos >= r.end {
		return false, true
	}
	indent := r.lineIndentAt(r.pos)
	if indent < col {
		return false, true
	}
	if indent > col {
		r.failMalformed(r.pos)
		return false, false
	}
	return true, true
}

func (r *configReader) parseBlockMapEntry(col int, out *ConfigValue) bool {
	if r.nodePrefixFails(r.pos) {
		return false
	}
	key, keySpan, ok := r.parseEntryKey()
	if !ok {
		return false
	}
	r.pos++
	r.skipInlineSpace()
	value, ok := r.parseEntryValue(col, r.pos)
	if !ok {
		return false
	}
	r.appendEntry(out, key, keySpan, value)
	return true
}

func (r *configReader) parseEntryValue(col, valuePos int) (ConfigValue, bool) {
	if r.inlineValueStart() {
		return r.parseInlineValue(col)
	}
	if !r.finishLineValue() {
		return ConfigValue{}, false
	}
	return r.nestedMapOrNull(col, valuePos)
}

func (r *configReader) nestedMapOrNull(col, valuePos int) (ConfigValue, bool) {
	null := ConfigValue{Kind: ValueNull, Span: r.tokenSpan(valuePos)}
	if !r.skipBlankAndComments() {
		return ConfigValue{}, false
	}
	if r.pos >= r.end {
		return null, true
	}
	indent := r.lineIndentAt(r.pos)
	if indent <= col {
		return null, true
	}
	return r.parseYAMLBlockNode(indent, col)
}

func (r *configReader) inlineValueStart() bool {
	if r.pos >= r.end || isLineBreak(r.src[r.pos]) {
		return false
	}
	return r.src[r.pos] != '#'
}

func (r *configReader) parseInlineValue(col int) (ConfigValue, bool) {
	if r.nodePrefixFails(r.pos) {
		return ConfigValue{}, false
	}
	switch r.src[r.pos] {
	case '|':
		return r.parseBlockHeader(col, blockLiteral)
	case '>':
		return r.parseBlockHeader(col, blockFolded)
	case '[', '{':
		value, ok := r.parseYAMLFlow(col)
		if !ok {
			return ConfigValue{}, false
		}
		return value, r.finishLineValue()
	}
	return r.parseYAMLScalar(col)
}

func (r *configReader) parseScalarValue() (ConfigValue, bool) {
	if r.pos >= r.end {
		r.failMalformed(r.end)
		return ConfigValue{}, false
	}
	switch r.src[r.pos] {
	case '"':
		return r.parseDoubleQuoted()
	case '\'':
		return r.parseSingleQuoted()
	}
	return r.parsePlainBlockScalar()
}

func (r *configReader) finishLineValue() bool {
	content, next := splitLine(r.src, r.pos, r.end)
	i := skipLineSpaces(r.src, r.pos, content)
	if i < content && r.src[i] != '#' {
		r.failMalformed(i)
		return false
	}
	r.pos = next
	return true
}

func (r *configReader) skipInlineSpace() {
	for r.pos < r.end && (r.src[r.pos] == ' ' || r.src[r.pos] == '\t') {
		r.pos++
	}
}

func skipLineSpaces(src []byte, from, limit int) int {
	i := from
	for i < limit && (src[i] == ' ' || src[i] == '\t') {
		i++
	}
	return i
}

func (r *configReader) parseEntryKey() (string, source.Span, bool) {
	start := r.pos
	lineContent, _ := splitLine(r.src, start, r.end)
	if r.mapColonFails(start, lineContent) {
		return "", source.Span{}, false
	}
	if b := r.src[start]; b == '"' || b == '\'' {
		return r.parseQuotedKey(lineContent)
	}
	if r.plainStartFails(start) {
		r.failMalformed(start)
		return "", source.Span{}, false
	}
	colon := keyColonAt(r.src, start, lineContent)
	if colon < 0 {
		r.failMalformed(lineContent)
		return "", source.Span{}, false
	}
	text := strings.TrimRight(string(r.src[start:colon]), " \t")
	r.pos = colon
	return text, r.span(start, start+len(text)), true
}

func (r *configReader) mapColonFails(start, lineContent int) bool {
	if start < lineContent && r.src[start] == ':' && colonEndsKey(r.src, start, lineContent) {
		r.failMalformed(start)
		return true
	}
	return false
}

func (r *configReader) parseQuotedKey(lineContent int) (string, source.Span, bool) {
	value, ok := r.parseScalarValue()
	if !ok {
		return "", source.Span{}, false
	}
	r.skipInlineSpace()
	if r.pos >= lineContent || r.src[r.pos] != ':' || !colonEndsKey(r.src, r.pos, lineContent) {
		r.failMalformed(r.pos)
		return "", source.Span{}, false
	}
	return value.Text, value.Span, true
}

func keyColonAt(src []byte, content, lineEnd int) int {
	if content >= lineEnd {
		return -1
	}
	if b := src[content]; b == '"' || b == '\'' {
		return quotedKeyColon(src, content, lineEnd)
	}
	for i := content; i < lineEnd; i++ {
		if src[i] == ':' && colonEndsKey(src, i, lineEnd) {
			return i
		}
		if commentStartsAt(src, i) {
			return -1
		}
	}
	return -1
}

func commentStartsAt(src []byte, i int) bool {
	if src[i] != '#' {
		return false
	}
	return i == 0 || src[i-1] == ' ' || src[i-1] == '\t'
}

func quotedKeyColon(src []byte, content, lineEnd int) int {
	after := skipQuoteToken(src, content, lineEnd)
	if after < 0 {
		return -1
	}
	i := skipLineSpaces(src, after, lineEnd)
	if i < lineEnd && src[i] == ':' {
		return i
	}
	return -1
}

func colonEndsKey(src []byte, i, lineEnd int) bool {
	if i+1 >= lineEnd {
		return true
	}
	return src[i+1] == ' ' || src[i+1] == '\t'
}

func skipQuoteToken(src []byte, start, lineEnd int) int {
	quote := src[start]
	for i := start + 1; i < lineEnd; i++ {
		if quote == '"' && src[i] == '\\' {
			i++
			continue
		}
		if src[i] != quote {
			continue
		}
		if quote == '\'' && i+1 < lineEnd && src[i+1] == '\'' {
			i++
			continue
		}
		return i + 1
	}
	return -1
}

func (r *configReader) parsePlainBlockScalar() (ConfigValue, bool) {
	start := r.pos
	if r.plainStartFails(start) {
		r.failMalformed(start)
		return ConfigValue{}, false
	}
	return r.readPlainBlockScalar(), true
}

func (r *configReader) readPlainBlockScalar() ConfigValue {
	start := r.pos
	lineContent, _ := splitLine(r.src, start, r.end)
	end := start
	for end < lineContent && !commentAfterSpace(r.src, end, lineContent) {
		end++
	}
	text := strings.TrimRight(string(r.src[start:end]), " \t")
	r.pos = end
	return resolvePlain(text, r.span(start, start+len(text)))
}

func commentAfterSpace(src []byte, i, lineEnd int) bool {
	if src[i] != ' ' && src[i] != '\t' {
		return false
	}
	return i+1 < lineEnd && src[i+1] == '#'
}

func (r *configReader) parseBlockHeader(col int, style blockStyle) (ConfigValue, bool) {
	headerStart := r.pos
	r.pos++
	chomp := r.readChomp()
	if r.pos < r.end && isDigit(r.src[r.pos]) {
		r.fail(codeMalformed, msgBlockIndent, r.span(r.pos, r.pos+1))
		return ConfigValue{}, false
	}
	if !r.finishLineValue() {
		return ConfigValue{}, false
	}
	return r.readBlockScalar(col, style, chomp, headerStart)
}

func (r *configReader) readChomp() chompMode {
	if r.pos >= r.end {
		return chompClip
	}
	switch r.src[r.pos] {
	case '-':
		r.pos++
		return chompStrip
	case '+':
		r.pos++
		return chompKeep
	}
	return chompClip
}

func (r *configReader) readBlockScalar(col int, style blockStyle, chomp chompMode, headerStart int) (ConfigValue, bool) {
	content, prefixLen, ok := r.blockContentStart(col)
	if !ok {
		return ConfigValue{}, false
	}
	text := r.blockScalarText(content, prefixLen, style, chomp)
	if r.failed {
		return ConfigValue{}, false
	}
	return r.blockScalarValue(text, headerStart), true
}

func (r *configReader) blockScalarValue(text string, headerStart int) ConfigValue {
	return ConfigValue{Kind: ValueString, Text: text, Span: r.span(headerStart, r.pos)}
}

func (r *configReader) blockContentStart(col int) (int, int, bool) {
	blankPrefix := 0
	for cursor := r.pos; cursor < r.end; {
		lineContent, next := splitLine(r.src, cursor, r.end)
		indent, content, tabAt := r.scanIndent(cursor, lineContent)
		if tabAt >= 0 {
			r.failTab(tabAt)
			return 0, 0, false
		}
		if content >= lineContent {
			blankPrefix++
			cursor = next
			continue
		}
		if indent <= col {
			r.pos = cursor
			return -1, blankPrefix, true
		}
		r.pos = cursor
		return indent, blankPrefix, true
	}
	r.pos = r.end
	return -1, blankPrefix, true
}

func (r *configReader) blockScalarText(content, blankPrefix int, style blockStyle, chomp chompMode) string {
	if content < 0 {
		return emptyBlockText(blankPrefix, chomp)
	}
	lines, trailing := r.collectBlockLines(content)
	return leadingLines(blankPrefix) + blockLines(lines, style) + blockTail(trailing, chomp)
}

func emptyBlockText(blankPrefix int, chomp chompMode) string {
	if chomp != chompKeep {
		return ""
	}
	return strings.Repeat("\n", blankPrefix)
}

func leadingLines(count int) string {
	return strings.Repeat("\n", count)
}

func (r *configReader) collectBlockLines(m int) ([]string, int) {
	var lines []string
	trailing := 0
	for cursor := r.pos; cursor < r.end; {
		lineContent, next := splitLine(r.src, cursor, r.end)
		indent, content, tabAt := r.scanIndent(cursor, lineContent)
		if tabAt >= 0 {
			r.failTab(tabAt)
			return nil, 0
		}
		if content < lineContent && indent < m {
			break
		}
		if content >= lineContent {
			lines = append(lines, "")
			trailing++
		} else {
			lines = append(lines, string(r.src[cursor+m:lineContent]))
			trailing = 0
		}
		cursor = next
		r.pos = cursor
	}
	return lines, trailing
}

func blockTail(trailing int, chomp chompMode) string {
	switch chomp {
	case chompStrip:
		return ""
	case chompKeep:
		return strings.Repeat("\n", trailing+1)
	}
	return "\n"
}

func blockLines(lines []string, style blockStyle) string {
	var b strings.Builder
	emptyRun := 0
	haveLine := false
	for _, line := range lines {
		if line == "" {
			emptyRun++
			continue
		}
		if haveLine {
			b.WriteString(blockSeparator(emptyRun, style, b.String(), line))
		}
		emptyRun = 0
		haveLine = true
		b.WriteString(line)
	}
	return b.String()
}

func blockSeparator(emptyRun int, style blockStyle, written, next string) string {
	if style == blockLiteral || startsWithSpace(next) || startsWithSpace(lastLine(written)) {
		return strings.Repeat("\n", emptyRun+1)
	}
	if emptyRun == 0 {
		return " "
	}
	return strings.Repeat("\n", emptyRun)
}

func startsWithSpace(line string) bool {
	return line != "" && (line[0] == ' ' || line[0] == '\t')
}

func lastLine(text string) string {
	if i := strings.LastIndexByte(text, '\n'); i >= 0 {
		return text[i+1:]
	}
	return text
}

func (r *configReader) scanIndent(p, lineContent int) (indent, content, tabAt int) {
	i := p
	for i < lineContent && r.src[i] == ' ' {
		i++
	}
	if i < lineContent && r.src[i] == '\t' {
		return i - p, i, i
	}
	return i - p, i, -1
}

func (r *configReader) skipBlankAndComments() bool {
	for r.pos < r.end {
		lineContent, next := splitLine(r.src, r.pos, r.end)
		_, content, tabAt := r.scanIndent(r.pos, lineContent)
		if tabAt >= 0 {
			r.failTab(tabAt)
			return false
		}
		if content < lineContent && r.src[content] != '#' {
			r.pos = content
			return true
		}
		r.pos = next
	}
	return true
}

func (r *configReader) parseYAMLFlow(ownerCol int) (ConfigValue, bool) {
	open := r.pos
	if !r.enter(open) {
		return ConfigValue{}, false
	}
	var value ConfigValue
	var ok bool
	if r.src[open] == '[' {
		value, ok = r.parseFlowSeq(ownerCol)
	} else {
		value, ok = r.parseFlowMap(ownerCol)
	}
	r.leave()
	return value, ok
}

func (r *configReader) parseFlowSeq(ownerCol int) (ConfigValue, bool) {
	start := r.pos
	r.pos++
	out := ConfigValue{Kind: ValueSequence}
	if !r.flowSpace(ownerCol) {
		return ConfigValue{}, false
	}
	if !r.flowCloses(']') {
		if !r.parseFlowSeqItems(ownerCol, &out) {
			return ConfigValue{}, false
		}
	}
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) parseFlowSeqItems(ownerCol int, out *ConfigValue) bool {
	for {
		item, ok := r.parseFlowItem(ownerCol)
		if !ok {
			return false
		}
		out.Items = append(out.Items, item)
		done, ok := r.afterFlowItem(ownerCol, ']')
		if !ok || done {
			return ok
		}
	}
}

func (r *configReader) parseFlowMap(ownerCol int) (ConfigValue, bool) {
	start := r.pos
	r.pos++
	out := ConfigValue{Kind: ValueMapping}
	if !r.flowSpace(ownerCol) {
		return ConfigValue{}, false
	}
	if !r.flowCloses('}') {
		if !r.parseFlowPairs(ownerCol, &out) {
			return ConfigValue{}, false
		}
	}
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) parseFlowPairs(ownerCol int, out *ConfigValue) bool {
	for {
		if !r.parseFlowPair(ownerCol, out) {
			return false
		}
		done, ok := r.afterFlowItem(ownerCol, '}')
		if !ok || done {
			return ok
		}
	}
}

func (r *configReader) parseFlowPair(ownerCol int, out *ConfigValue) bool {
	key, keySpan, ok := r.parseFlowKey()
	if !ok {
		return false
	}
	if !r.flowSpace(ownerCol) {
		return false
	}
	if r.pos >= r.end || r.src[r.pos] != ':' {
		r.failMalformed(r.pos)
		return false
	}
	r.pos++
	if !r.flowSpace(ownerCol) {
		return false
	}
	value := ConfigValue{Kind: ValueNull, Span: r.posSpan(r.pos)}
	if !r.flowValueAbsent() {
		if value, ok = r.parseFlowItem(ownerCol); !ok {
			return false
		}
	}
	r.appendEntry(out, key, keySpan, value)
	return true
}

func (r *configReader) flowValueAbsent() bool {
	if r.pos >= r.end {
		return true
	}
	return r.src[r.pos] == ',' || r.src[r.pos] == '}'
}

func (r *configReader) parseFlowKey() (string, source.Span, bool) {
	if r.pos >= r.end {
		r.failMalformed(r.end)
		return "", source.Span{}, false
	}
	start := r.pos
	if b := r.src[start]; b == '"' || b == '\'' {
		value, ok := r.parseScalarValue()
		if !ok {
			return "", source.Span{}, false
		}
		return value.Text, value.Span, true
	}
	if r.nodePrefixFails(start) {
		return "", source.Span{}, false
	}
	text, ok := r.plainFlowText(start)
	if !ok {
		return "", source.Span{}, false
	}
	return text, r.span(start, start+len(text)), true
}

func (r *configReader) parseFlowItem(ownerCol int) (ConfigValue, bool) {
	if r.pos >= r.end {
		r.failMalformed(r.end)
		return ConfigValue{}, false
	}
	switch r.src[r.pos] {
	case '[', '{':
		return r.parseYAMLFlow(ownerCol)
	case '"', '\'':
		return r.parseYAMLQuoted(ownerCol)
	}
	if r.nodePrefixFails(r.pos) {
		return ConfigValue{}, false
	}
	return r.parseYAMLPlainFlow(ownerCol)
}

func (r *configReader) plainFlowText(start int) (string, bool) {
	if r.plainStartFails(start) {
		r.failMalformed(start)
		return "", false
	}
	end := start
	for end < r.end && !flowStop(r.src[end]) {
		end++
	}
	text := strings.TrimRight(string(r.src[start:end]), " \t")
	r.pos = end
	return text, true
}

func flowStop(b byte) bool {
	switch b {
	case ',', '[', ']', '{', '}', ':', '\r', '\n':
		return true
	}
	return false
}

func (r *configReader) flowCloses(closing byte) bool {
	if r.pos < r.end && r.src[r.pos] == closing {
		r.pos++
		return true
	}
	return false
}

func (r *configReader) afterFlowItem(ownerCol int, closing byte) (bool, bool) {
	if !r.flowSpace(ownerCol) {
		return false, false
	}
	if r.flowCloses(closing) {
		return true, true
	}
	if r.pos >= r.end || r.src[r.pos] != ',' {
		r.failMalformed(r.pos)
		return false, false
	}
	r.pos++
	if !r.flowSpace(ownerCol) {
		return false, false
	}
	if r.pos < r.end && (r.src[r.pos] == closing || r.src[r.pos] == ',') {
		r.failMalformed(r.pos)
		return false, false
	}
	return false, true
}

func (r *configReader) flowSpace(ownerCol int) bool {
	for r.pos < r.end {
		switch r.src[r.pos] {
		case ' ', '\t':
			r.pos++
		case '\r', '\n':
			if !r.flowLineBreak(ownerCol) {
				return false
			}
		default:
			return true
		}
	}
	return true
}

func (r *configReader) flowLineBreak(ownerCol int) bool {
	_, next := splitLine(r.src, r.pos, r.end)
	return r.flowNextLine(next, ownerCol)
}

func (r *configReader) flowNextLine(from, ownerCol int) bool {
	for from < r.end {
		lineContent, next := splitLine(r.src, from, r.end)
		indent, content, tabAt := r.scanIndent(from, lineContent)
		if content >= lineContent {
			from = next
			continue
		}
		if tabAt >= 0 {
			r.failTab(tabAt)
			return false
		}
		if indent <= ownerCol {
			r.failMalformed(content)
			return false
		}
		r.pos = content
		return true
	}
	r.pos = r.end
	return true
}
