package flowchart

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeString
	modeMDString
	modeAccTitle
	modeAccDescr
	modeAccDescrMultiline
	modeDir
	modeText
	modeEllipseText
	modeTrapText
	modeEdgeText
	modeThickEdgeText
	modeDottedEdgeText
	modeClick
	modeCallbackName
	modeCallbackArgs
	modeShapeData
	modeShapeDataStr
)

type lexAct uint8

const (
	actNone lexAct = iota
	actOpenString
	actOpenMDString
	actCloseString
	actCloseMDString
	actShapeOpen
	actShapeRun
	actGraph
	actAccBlockOpen
	actAccBlockClose
	actLeaveOnly
	actBeginCallbackArgs
)

type modeFrame struct {
	mode lexMode
	open source.Span
}

type lexer struct {
	src     []byte
	pos     int
	removed []source.Span
	rm      int
	reach   int
	frames  []modeFrame
	diags   []diag.Diagnostic
	toks    []Token

	graphSeen bool
	accBlock  source.Span
	silent    bool

	openQuote int
	firstCont int
	lastCont  int

	eofQuote    int
	eofLabel    source.Span
	eofLabelSet bool
	eofShape    source.Span
	eofShapeSet bool
	eofAcc      source.Span
	eofAccSet   bool
}

func newLexer(src []byte, removed []source.Span) *lexer {
	return &lexer{
		src:       src,
		removed:   removed,
		frames:    []modeFrame{{mode: modeInitial}},
		openQuote: -1,
		firstCont: -1,
		lastCont:  -1,
		eofQuote:  -1,
	}
}

func (l *lexer) top() lexMode { return l.frames[len(l.frames)-1].mode }

func (l *lexer) push(m lexMode, open source.Span) {
	l.frames = append(l.frames, modeFrame{mode: m, open: open})
}

func (l *lexer) pop() {
	if len(l.frames) > 1 {
		l.frames = l.frames[:len(l.frames)-1]
	}
}

func (l *lexer) skipRemoved() {
	for {
		moved := false
		for l.rm < len(l.removed) && l.removed[l.rm].End <= l.pos {
			l.rm++
		}
		if l.rm < len(l.removed) && l.pos >= l.removed[l.rm].Start {
			l.pos = l.removed[l.rm].End
			moved = true
		}
		if !moved {
			return
		}
	}
}

func (l *lexer) removedFrom(p int) int {
	j := l.rm
	for j < len(l.removed) && l.removed[j].End <= p {
		j++
	}
	return j
}

func (l *lexer) limitAt(p int) int {
	if j := l.removedFrom(p); j < len(l.removed) && p < l.removed[j].Start {
		return l.removed[j].Start
	}
	return len(l.src)
}

func (l *lexer) skipRemovedAt(p int) int {
	if j := l.removedFrom(p); j < len(l.removed) && p >= l.removed[j].Start {
		return l.removed[j].End
	}
	return p
}

func (l *lexer) hop(pos, limit int) (int, int, bool) {
	if pos < limit || limit >= len(l.src) {
		return pos, limit, false
	}
	next := l.skipRemovedAt(pos)
	if next == pos {
		return pos, limit, false
	}
	limit = l.limitAt(next)
	l.reach = max(l.reach, limit)
	return next, limit, true
}

func (l *lexer) runWhile(pos, limit int, pred func(byte) bool) (int, int) {
	for {
		for pos < limit && pred(l.src[pos]) {
			pos++
		}
		next, nextLimit, hopped := l.hop(pos, limit)
		if !hopped {
			return pos, limit
		}
		pos, limit = next, nextLimit
	}
}

func (l *lexer) skipSpace(pos, limit int) (int, int) {
	return l.runWhile(pos, limit, isJSSpace)
}

func (l *lexer) spaceEnd(pos, limit int) int {
	end, _ := l.skipSpace(pos, limit)
	return end
}

func (l *lexer) spaceFollows(pos, limit int) bool {
	if pos >= limit {
		pos = l.skipRemovedAt(pos)
	}
	return pos < len(l.src) && isJSSpace(l.src[pos])
}

func (l *lexer) text(start, end int) string {
	if start < 0 || start > end || end > len(l.src) {
		return ""
	}
	j := l.removedFrom(start)
	if j >= len(l.removed) || l.removed[j].Start >= end {
		return string(l.src[start:end])
	}
	var sb strings.Builder
	at := start
	for ; j < len(l.removed) && l.removed[j].Start < end; j++ {
		sb.Write(l.src[at:l.removed[j].Start])
		at = l.removed[j].End
	}
	if at < end {
		sb.Write(l.src[at:end])
	}
	return sb.String()
}

func (l *lexer) span(start, end int) source.Span { return source.Span{Start: start, End: end} }

func (l *lexer) lexAll() []Token {
	for {
		l.skipRemoved()
		if l.pos >= len(l.src) {
			l.captureEOF()
			l.keep(Token{Kind: TokEOF, Span: l.span(l.pos, l.pos), StringOpen: -1})
			return l.toks
		}
		if _, ok := l.step(); !ok {
			l.recordUnexpected()
		}
	}
}

func (l *lexer) captureEOF() {
	l.eofQuote = l.openQuote
	for _, f := range l.frames {
		switch f.mode {
		case modeText, modeEllipseText, modeTrapText:
			if !l.eofLabelSet {
				l.eofLabel = f.open
				l.eofLabelSet = true
			}
		case modeShapeData:
			l.eofShape = f.open
			l.eofShapeSet = true
		case modeAccDescrMultiline:
			l.eofAcc = f.open
			l.eofAccSet = true
		}
	}
}

func (l *lexer) step() (lexRule, bool) {
	rules := rulesFor(l.top())
	limit := l.limitAt(l.pos)
	for i := range rules {
		r := rules[i]
		l.reach = limit
		end := r.match(l, limit)
		if end < 0 || end > l.reach {
			continue
		}
		if end == l.pos && !r.allowEmpty {
			continue
		}
		l.emit(&r, end)
		return r, true
	}
	return lexRule{}, false
}

func (l *lexer) keep(tok Token) {
	if l.silent {
		return
	}
	l.toks = append(l.toks, tok)
}

func (l *lexer) report(d diag.Diagnostic) {
	if l.silent {
		return
	}
	l.diags = append(l.diags, d)
}

func (l *lexer) emit(r *lexRule, end int) {
	start := l.pos
	l.pos = end
	tok := Token{Kind: r.kind, Text: l.text(start, end), Span: l.span(start, end), StringOpen: -1}
	switch r.act {
	case actOpenString:
		if l.top() == modeCallbackName {
			l.report(unexpectedDiagnostic(tok.Span, tok.Text, []string{"CALLBACKNAME"}))
		}
		l.openQuote = start
		l.push(modeString, tok.Span)
		return
	case actOpenMDString:
		l.openQuote = start
		l.push(modeMDString, tok.Span)
		return
	case actCloseString, actCloseMDString:
		l.endString(end)
		return
	case actShapeOpen:
		tok.Text = ""
		l.push(modeShapeData, tok.Span)
	case actShapeRun:
		tok.Text, tok.BRs = replaceLineEnds([]byte(l.text(start, end)))
		l.keep(tok)
		return
	case actGraph:
		if !l.graphSeen {
			l.graphSeen = true
			l.push(modeDir, tok.Span)
		}
	default:
		if l.emitModeAction(r.act, tok) {
			return
		}
	}
	l.finishEmit(r, tok)
}

func (l *lexer) emitModeAction(act lexAct, tok Token) bool {
	switch act {
	case actAccBlockOpen:
		l.accBlock = tok.Span
		l.push(modeAccDescrMultiline, tok.Span)
	case actAccBlockClose, actLeaveOnly:
		l.pop()
	case actBeginCallbackArgs:
		l.pop()
		l.push(modeCallbackArgs, tok.Span)
	default:
		return false
	}
	return true
}

func (l *lexer) finishEmit(r *lexRule, tok Token) {
	if r.pushOnPush {
		l.push(r.push, tok.Span)
	}
	if r.pop {
		l.pop()
	}
	if tok.Kind == TokNone {
		return
	}
	l.shapeToken(tok)
}

func (l *lexer) shapeToken(tok Token) {
	if tok.Kind == TokStr || tok.Kind == TokMDStr {
		l.contentToken(tok)
		return
	}
	if l.openQuote >= 0 {
		tok.StringOpen = l.openQuote
	}
	l.keep(tok)
}

func (l *lexer) contentToken(tok Token) {
	tok.StringOpen = l.openQuote
	if l.firstCont < 0 {
		l.firstCont = len(l.toks)
	}
	l.lastCont = len(l.toks)
	l.keep(tok)
}

func (l *lexer) endString(end int) {
	open := l.openQuote
	l.pop()
	l.openQuote = -1
	if l.firstCont >= 0 && !l.silent {
		l.toks[l.firstCont].Span.Start = open
		l.toks[l.lastCont].Span.End = end
		l.firstCont, l.lastCont = -1, -1
		return
	}
	l.firstCont, l.lastCont = -1, -1
	l.keep(Token{Kind: TokStr, Span: l.span(open, end), StringOpen: -1})
}

func (l *lexer) recordUnexpected() {
	start := l.pos
	limit := l.limitAt(start)
	size := 1
	if start < limit {
		if _, s := utf8.DecodeRune(l.src[start:limit]); s > 0 {
			size = s
		}
	}
	l.report(unexpectedDiagnostic(l.span(start, start+size), l.text(start, start+size), expectedFor(l.top())))
	l.frames = []modeFrame{{mode: modeInitial}}
	l.openQuote = -1
	l.firstCont, l.lastCont = -1, -1
	l.pos = l.skipToBoundary(start)
	l.skipRemoved()
}

func (l *lexer) skipToBoundary(from int) int {
	frames := l.frames
	l.frames = []modeFrame{{mode: modeInitial}}
	l.pos = from
	l.silent = true
	defer func() {
		l.silent = false
		l.frames = frames
	}()
	for {
		l.skipRemoved()
		if l.pos >= len(l.src) {
			return len(l.src)
		}
		start := l.pos
		r, ok := l.step()
		if !ok {
			l.pos = start + 1
			continue
		}
		if len(l.frames) == 1 && (r.kind == TokNewline || r.kind == TokSemi) {
			return start
		}
	}
}

type BRPoint struct {
	Text int
	Src  int
}

func replaceLineEnds(b []byte) (string, []BRPoint) {
	var sb strings.Builder
	var brs []BRPoint
	for i := 0; i < len(b); {
		next, isEnd := lineEndAt(b, i)
		if !isEnd {
			sb.WriteByte(b[i])
			i++
			continue
		}
		brs = append(brs, BRPoint{Text: sb.Len(), Src: i})
		sb.WriteString("<br/>")
		i = next
		for i < len(b) && (b[i] == ' ' || b[i] == '\t') {
			i++
		}
	}
	return sb.String(), brs
}
