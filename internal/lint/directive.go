package lint

import (
	"math"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type DirectiveKind uint8

const (
	DisableNextLine DirectiveKind = iota
	Disable
	Enable
	DisableDiagram
	DisableFile
)

type codeScope struct {
	code  string
	start int
	end   int
}

type Directive struct {
	Kind   DirectiveKind
	Span   source.Span
	Names  []string
	scopes []codeScope
}

type finding struct {
	code  string
	value string
	span  source.Span
}

type codeRef struct {
	code string
	name string
}

type rawDirective struct {
	kind DirectiveKind
	span source.Span
	line line
	refs []codeRef
}

type codeToken struct {
	text string
	span source.Span
}

type listParser func(src []byte, pos, limit int) ([]codeToken, bool)

type directiveForm struct {
	kind  DirectiveKind
	parse listParser
}

var mermaidForms = map[string]directiveForm{
	"emd-disable-next-line": {kind: DisableNextLine, parse: parseReasonList},
	"emd-disable":           {kind: Disable, parse: parseReasonList},
	"emd-disable-diagram":   {kind: DisableDiagram, parse: parseReasonList},
	"emd-enable":            {kind: Enable, parse: parseBareList},
}

type lineKind uint8

const (
	ordinaryLine lineKind = iota
	malformedLine
	directiveLine
)

type lineResult struct {
	kind   lineKind
	form   directiveForm
	tokens []codeToken
}

func isCodeByte(b byte) bool {
	switch {
	case b >= 'a' && b <= 'z', b >= 'A' && b <= 'Z', b >= '0' && b <= '9':
		return true
	}
	return b == '/' || b == '_' || b == '-'
}

func isKeywordByte(b byte) bool {
	return b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b == '-'
}

func keywordEnd(src []byte, pos, limit int) int {
	for pos < limit && isKeywordByte(src[pos]) {
		pos++
	}
	return pos
}

func keywordTerminated(src []byte, end, limit int) bool {
	return end == limit || isBlank(src[end]) || src[end] == ':'
}

func scanToken(src []byte, pos, limit int) (codeToken, bool) {
	start := pos
	for pos < limit && isCodeByte(src[pos]) {
		pos++
	}
	if pos == start {
		return codeToken{}, false
	}
	return codeToken{text: string(src[start:pos]), span: source.Span{Start: start, End: pos}}, true
}

func scanTokenList(src []byte, pos, limit int) ([]codeToken, int, bool) {
	pos = skipBlanks(src, pos, limit)
	var tokens []codeToken
	for {
		token, ok := scanToken(src, pos, limit)
		if !ok {
			return nil, pos, false
		}
		tokens = append(tokens, token)
		pos = token.span.End
		if pos == limit || src[pos] != ',' {
			return tokens, pos, true
		}
		pos++
		if pos < limit && src[pos] == ' ' {
			pos++
		}
	}
}

func parseReasonList(src []byte, pos, limit int) ([]codeToken, bool) {
	tokens, stop, ok := scanTokenList(src, pos, limit)
	if !ok || stop == limit || src[stop] != ':' {
		return nil, false
	}
	return tokens, skipBlanks(src, stop+1, limit) < trimEnd(src, stop+1, limit)
}

func parseBareList(src []byte, pos, limit int) ([]codeToken, bool) {
	tokens, stop, ok := scanTokenList(src, pos, limit)
	return tokens, ok && stop == limit
}

func parseMermaidLine(src []byte, ln line) lineResult {
	start := skipBlanks(src, ln.start, ln.end)
	if !hasPrefixAt(src, start, ln.end, "%%") || start+2 >= ln.end || !isBlank(src[start+2]) {
		return lineResult{}
	}
	kw := skipBlanks(src, start+2, ln.end)
	end := keywordEnd(src, kw, ln.end)
	form, ok := mermaidForms[string(src[kw:end])]
	if !ok || !keywordTerminated(src, end, ln.end) {
		return lineResult{}
	}
	tokens, ok := form.parse(src, end, trimEnd(src, end, ln.end))
	if !ok {
		return lineResult{kind: malformedLine}
	}
	return lineResult{kind: directiveLine, form: form, tokens: tokens}
}

func directiveSpan(src []byte, ln line) source.Span {
	start := skipBlanks(src, ln.start, ln.end)
	return source.Span{Start: start, End: trimEnd(src, start, ln.end)}
}

func classify(tokens []codeToken) ([]codeRef, []finding, bool) {
	refs := make([]codeRef, 0, len(tokens))
	var finds []finding
	blocked := false
	for _, t := range tokens {
		e, ok := lookup(t.text)
		if !ok {
			finds = append(finds, finding{code: codeUnknown, value: t.text, span: t.span})
			continue
		}
		blocked = blocked || !e.suppressible()
		if !hasCode(refs, e.canonical) {
			refs = append(refs, codeRef{code: e.canonical, name: t.text})
		}
	}
	return refs, finds, blocked
}

func hasCode(refs []codeRef, code string) bool {
	for _, r := range refs {
		if r.code == code {
			return true
		}
	}
	return false
}

func admit(span source.Span, tokens []codeToken) ([]codeRef, []finding, bool) {
	refs, finds, blocked := classify(tokens)
	if blocked {
		return nil, append(finds, finding{code: codeMalformed, span: span}), false
	}
	return refs, finds, true
}

func scanMermaid(src []byte, bodyStart int) ([]rawDirective, []finding) {
	var raws []rawDirective
	var finds []finding
	for pos := min(max(bodyStart, 0), len(src)); pos < len(src); {
		ln := lineAt(src, pos)
		pos = ln.next
		res := parseMermaidLine(src, ln)
		span := directiveSpan(src, ln)
		switch res.kind {
		case malformedLine:
			finds = append(finds, finding{code: codeMalformed, span: span})
		case directiveLine:
			refs, more, ok := admit(span, res.tokens)
			finds = append(finds, more...)
			if ok {
				raws = append(raws, rawDirective{kind: res.form.kind, span: span, line: ln, refs: refs})
			}
		}
	}
	return raws, finds
}

type openScope struct {
	dir   int
	scope int
}

type resolver struct {
	src      []byte
	open     map[string]openScope
	dirs     []Directive
	findings []finding
}

func parseBlockDirectives(src []byte, bodyStart int) ([]Directive, []finding) {
	raws, finds := scanMermaid(src, bodyStart)
	r := &resolver{src: src, open: map[string]openScope{}}
	for i := range raws {
		r.resolve(&raws[i])
	}
	return r.dirs, append(finds, r.findings...)
}

func (r *resolver) resolve(d *rawDirective) {
	switch d.kind {
	case DisableNextLine:
		r.add(d, r.nextLineScopes(d))
	case DisableDiagram:
		r.add(d, wholeScopes(d.refs, len(r.src)+1))
	case Disable:
		r.disable(d)
	default:
		r.enable(d)
	}
}

func (r *resolver) add(d *rawDirective, scopes []codeScope) int {
	r.dirs = append(r.dirs, Directive{Kind: d.kind, Span: d.span, Names: names(d.refs), scopes: scopes})
	return len(r.dirs) - 1
}

func (r *resolver) malformed(d *rawDirective) {
	r.findings = append(r.findings, finding{code: codeMalformed, span: d.span})
}

func names(refs []codeRef) []string {
	out := make([]string, len(refs))
	for i, ref := range refs {
		out[i] = ref.name
	}
	return out
}

func wholeScopes(refs []codeRef, end int) []codeScope {
	scopes := make([]codeScope, len(refs))
	for i, ref := range refs {
		scopes[i] = codeScope{code: ref.code, start: 0, end: end}
	}
	return scopes
}

func (r *resolver) nextLineScopes(d *rawDirective) []codeScope {
	if d.line.next >= len(r.src) {
		return nil
	}
	next := lineAt(r.src, d.line.next)
	scopes := make([]codeScope, len(d.refs))
	for i, ref := range d.refs {
		scopes[i] = codeScope{code: ref.code, start: next.start, end: next.exclusiveEnd()}
	}
	return scopes
}

func (r *resolver) disable(d *rawDirective) {
	for _, ref := range d.refs {
		if _, taken := r.open[ref.code]; taken {
			r.malformed(d)
			return
		}
	}
	scopes := make([]codeScope, len(d.refs))
	for i, ref := range d.refs {
		scopes[i] = codeScope{code: ref.code, start: d.line.start, end: len(r.src) + 1}
	}
	index := r.add(d, scopes)
	for i, ref := range d.refs {
		r.open[ref.code] = openScope{dir: index, scope: i}
	}
}

func (r *resolver) enable(d *rawDirective) {
	for _, ref := range d.refs {
		if _, ok := r.open[ref.code]; !ok {
			r.malformed(d)
			return
		}
	}
	for _, ref := range d.refs {
		o := r.open[ref.code]
		r.dirs[o.dir].scopes[o.scope].end = d.line.start
		delete(r.open, ref.code)
	}
}

const (
	commentOpen  = "<!--"
	commentClose = "-->"
	fileKeyword  = "emd-disable-file"
)

func parseFileLine(host []byte, ln line) lineResult {
	start := skipBlanks(host, ln.start, ln.end)
	if !hasPrefixAt(host, start, ln.end, commentOpen) {
		return lineResult{}
	}
	kw := skipBlanks(host, start+len(commentOpen), ln.end)
	end := keywordEnd(host, kw, ln.end)
	if string(host[kw:end]) != fileKeyword || !keywordTerminated(host, end, ln.end) {
		return lineResult{}
	}
	limit := trimEnd(host, end, ln.end) - len(commentClose)
	if limit < end || !hasPrefixAt(host, limit, limit+len(commentClose), commentClose) {
		return lineResult{kind: malformedLine}
	}
	tokens, ok := parseReasonList(host, end, limit)
	if !ok {
		return lineResult{kind: malformedLine}
	}
	return lineResult{kind: directiveLine, tokens: tokens}
}

func fenceRun(host []byte, ln line) (byte, int, int) {
	at := ln.start
	for at < ln.end && at-ln.start < 3 && host[at] == ' ' {
		at++
	}
	if at >= ln.end || (host[at] != '`' && host[at] != '~') {
		return 0, 0, at
	}
	char, run := host[at], 0
	for at+run < ln.end && host[at+run] == char {
		run++
	}
	return char, run, at + run
}

func openingFence(host []byte, ln line) (byte, int, bool) {
	char, run, after := fenceRun(host, ln)
	if run < 3 || char == '`' && containsByte(host[after:ln.end], '`') {
		return 0, 0, false
	}
	return char, run, true
}

func containsByte(b []byte, want byte) bool {
	for _, c := range b {
		if c == want {
			return true
		}
	}
	return false
}

func closingFence(host []byte, ln line, char byte, count int) bool {
	got, run, after := fenceRun(host, ln)
	return got == char && run >= count && skipBlanks(host, after, ln.end) == ln.end
}

func fencedSpans(host []byte) []source.Span {
	var spans []source.Span
	for pos := 0; pos < len(host); {
		ln := lineAt(host, pos)
		pos = ln.next
		char, count, ok := openingFence(host, ln)
		if !ok {
			continue
		}
		end := len(host)
		for pos < len(host) {
			inner := lineAt(host, pos)
			pos = inner.next
			if closingFence(host, inner, char, count) {
				end = inner.next
				break
			}
		}
		spans = append(spans, source.Span{Start: ln.start, End: end})
	}
	return spans
}

func parseFileDirectives(host []byte, skip []source.Span) ([]Directive, []finding) {
	var dirs []Directive
	var finds []finding
	for pos := 0; pos < len(host); {
		ln := lineAt(host, pos)
		pos = ln.next
		if containsOffset(skip, ln.start) {
			continue
		}
		res := parseFileLine(host, ln)
		span := directiveSpan(host, ln)
		switch res.kind {
		case malformedLine:
			finds = append(finds, finding{code: codeMalformed, span: span})
		case directiveLine:
			refs, more, ok := admit(span, res.tokens)
			finds = append(finds, more...)
			if ok {
				dirs = append(dirs, Directive{Kind: DisableFile, Span: span, Names: names(refs), scopes: wholeScopes(refs, math.MaxInt)})
			}
		}
	}
	return dirs, finds
}
