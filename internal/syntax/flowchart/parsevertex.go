package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func (p *parser) atVertexStart() bool {
	switch p.peek().Kind {
	case TokNodeString, TokStr, TokMDStr, TokLinkID, TokNum, TokUnicodeText, TokDown,
		TokDefault, TokComma, TokColon, TokAmp, TokBrkt, TokMult, TokMinus:
		return true
	}
	return false
}

func (p *parser) parseVertexStatement() (Stmt, bool) {
	group, ok := p.parseNodeGroup()
	if !ok {
		return p.rejectStatement()
	}
	stmt := &VertexStatement{node: node{Span: group.Span}, Groups: []NodeGroup{group}}
	for {
		link, outcome := p.tryParseLink()
		switch outcome {
		case linkNone:
			return p.finishVertexStatement(stmt, true), true
		case linkBroken:
			return p.finishVertexStatement(stmt, false), true
		}
		p.skipSpaces()
		if !p.atVertexStart() {
			p.report(plainDiagnostic(codeLinkMissing, link.Span))
			return p.finishVertexStatement(stmt, false), true
		}
		next, ok := p.parseNodeGroup()
		if !ok {
			return p.finishVertexStatement(stmt, false), true
		}
		stmt.Links = append(stmt.Links, link)
		stmt.Span = spanJoin(stmt.Span, link.Span)
		stmt.Groups = append(stmt.Groups, next)
		stmt.Span = spanJoin(stmt.Span, next.Span)
	}
}

func (p *parser) finishVertexStatement(stmt *VertexStatement, clean bool) Stmt {
	if p.at(TokSpace) {
		p.next()
	}
	if !p.atAny(TokEOF, TokNewline, TokSemi) {
		if clean && p.atVertexStart() {
			p.report(plainDiagnostic(codeLinkMissing, p.peek().Span))
		} else if clean {
			tok := p.peek()
			p.report(unexpectedDiagnostic(codeUnexpectedToken, tok.Span, tok.Text, vertexFollowNames()))
		}
		p.skipToStatementBoundary()
	}
	stmt.Span.End = p.statementEnd(stmt.Span.End)
	return stmt
}

func (p *parser) statementEnd(fallback int) int {
	if p.i > 0 && p.i <= len(p.toks) {
		return p.toks[p.i-1].Span.End
	}
	return fallback
}

func vertexFollowNames() []string {
	return []string{"AMP", "EOF", "LINK", "NEWLINE", "SEMI", "SHAPE_DATA", "START_LINK", "STYLE_SEPARATOR"}
}

func (p *parser) parseNodeGroup() (NodeGroup, bool) {
	first, ok := p.parseStyledVertex()
	if !ok {
		return NodeGroup{}, false
	}
	group := NodeGroup{Vertices: []StyledVertex{first}, Span: first.Span}
	for {
		save := p.i
		p.skipSpaces()
		amp, found := p.accept(TokAmp)
		if !found {
			p.i = save
			return group, true
		}
		p.skipSpaces()
		next, ok := p.parseStyledVertex()
		if !ok {
			p.report(plainDiagnostic(codeLinkMissing, amp.Span))
			return group, true
		}
		group.Vertices = append(group.Vertices, next)
		group.Span = spanJoin(group.Span, next.Span)
	}
}

func (p *parser) skipSpaces() {
	for p.at(TokSpace) {
		p.next()
	}
}

func (p *parser) parseStyledVertex() (StyledVertex, bool) {
	vertex, ok := p.parseVertex()
	if !ok {
		return StyledVertex{}, false
	}
	sv := StyledVertex{Vertex: vertex, Span: vertex.Span}
	if p.at(TokStyleSeparator) {
		p.next()
		if class, ok := p.parseIdString(); ok {
			sv.Class = &class
			sv.Span = spanJoin(sv.Span, class.Span)
		}
	}
	if p.at(TokShapeData) {
		data := p.parseShapeData()
		sv.ShapeData = &data
		sv.Span = spanJoin(sv.Span, data.Span)
	}
	return sv, true
}

func (p *parser) parseVertex() (Vertex, bool) {
	id, ok := p.parseIdString()
	if !ok {
		return Vertex{}, false
	}
	vertex := Vertex{ID: id, Shape: "squareRect", Span: id.Span}
	opener := p.peek()
	if !isLabelOpener(opener.Kind) {
		return vertex, true
	}
	p.next()
	vertex.Shape = shapeByOpener[opener.Kind]
	vertex.Label = true
	if opener.Kind == TokVertexWithPropsStart {
		p.parseRectProps()
	}
	if (opener.Kind == TokPS || opener.Kind == TokDiamondStart) && p.at(opener.Kind) {
		return p.parsePairedVertex(vertex, opener), true
	}
	text := p.parseText(closerByOpener[opener.Kind]...)
	vertex.Text = text
	vertex.Span = source.Span{Start: id.Span.Start, End: p.closeLabel(opener, text)}
	return vertex, true
}

func (p *parser) parsePairedVertex(vertex Vertex, opener Token) Vertex {
	p.next()
	closer := TokPE
	vertex.Shape = "circle"
	if opener.Kind == TokDiamondStart {
		closer = TokDiamondStop
		vertex.Shape = "hexagon"
	}
	text := p.parseText(closer)
	p.reportLabelRules(text, opener)
	vertex.Text = text
	for range 2 {
		last, ok := p.accept(closer)
		if !ok {
			p.end = endStateUnclosedBracket
			return vertex
		}
		vertex.Span.End = last.Span.End
	}
	return vertex
}

func (p *parser) parseRectProps() {
	for _, want := range []TokenKind{TokNodeString, TokColon, TokNodeString, TokPipe} {
		if _, ok := p.accept(want); ok {
			continue
		}
		tok := p.peek()
		p.report(unexpectedDiagnostic(codeUnexpectedToken, tok.Span, tok.Text, []string{want.Name()}))
	}
}

func (p *parser) closeLabel(opener Token, text Text) int {
	p.reportLabelRules(text, opener)
	if closer, ok := p.acceptCloser(closerByOpener[opener.Kind]); ok {
		return closer.Span.End
	}
	p.end = endStateUnclosedBracket
	if token, ok := p.acceptAnyCloser(); ok {
		p.report(plainDiagnostic(codeNodeMixedBrackets, token.Span))
		return token.Span.End
	}
	if !p.atAny(TokEOF) {
		p.report(plainDiagnostic(codeNodeMixedBrackets, p.peek().Span))
	}
	return textEnd(text, opener)
}

func textEnd(text Text, opener Token) int {
	if text.Span.End > opener.Span.End {
		return text.Span.End
	}
	return opener.Span.End
}

func (p *parser) acceptCloser(accepted []TokenKind) (Token, bool) {
	for _, k := range accepted {
		if p.at(k) {
			return p.next(), true
		}
	}
	return Token{}, false
}

func (p *parser) acceptAnyCloser() (Token, bool) {
	switch p.peek().Kind {
	case TokSQE, TokPE, TokDiamondStop, TokStadiumEnd, TokSubroutineEnd,
		TokCylinderEnd, TokDoubleCircleEnd, TokEllipseEnd, TokTrapEnd, TokInvTrapEnd:
		return p.next(), true
	}
	return Token{}, false
}

func (p *parser) reportLabelRules(text Text, opener Token) {
	if len(text.Tokens) == 0 {
		p.report(plainDiagnostic(codeNodeEmpty, opener.Span))
		return
	}
	want := labelRuleFor(text.Tokens[0].Kind)
	for _, tok := range text.Tokens {
		if tok.Kind != TokStr && tok.Kind != TokMDStr {
			continue
		}
		escapedQuoteIn(p.src, tok.Span, func(span source.Span) {
			p.report(plainDiagnostic(codeLabelEscapedQuote, span))
		})
	}
	for _, tok := range text.Tokens[1:] {
		if tok.Kind != TokStr && tok.Kind != TokMDStr {
			continue
		}
		p.report(plainDiagnostic(want, openingQuote(tok)))
	}
	if text.Kind != LabelPlain {
		return
	}
	for _, tok := range text.Tokens {
		p.reportPlainParens(tok)
	}
}

func openingQuote(tok Token) source.Span {
	if tok.StringOpen < 0 {
		return source.Span{Start: tok.Span.Start, End: tok.Span.Start + 1}
	}
	return source.Span{Start: tok.StringOpen, End: tok.StringOpen + 1}
}
func labelRuleFor(first TokenKind) string {
	switch first {
	case TokStr:
		return codeLabelDoubleInDouble
	case TokMDStr:
		return codeLabelDoubleInSingle
	}
	return codeLabelQuoteInUnquoted
}

func (p *parser) reportPlainParens(tok Token) {
	for off := range len(tok.Text) {
		if b := tok.Text[off]; b == '(' || b == ')' {
			p.report(plainDiagnostic(codeLabelParensUnquoted, source.Span{Start: tok.Span.Start + off, End: tok.Span.Start + off + 1}))
			return
		}
	}
}

func escapedQuoteIn(src []byte, span source.Span, emit func(source.Span)) {
	for i := span.Start; i+1 < span.End && i+1 < len(src); i++ {
		if src[i] == '\\' && src[i+1] == '"' {
			emit(source.Span{Start: i, End: i + 2})
		}
	}
}

func (p *parser) parseShapeData() ShapeData {
	open := p.next()
	data := ShapeData{Span: open.Span}
	for {
		tok := p.peek()
		if tok.Kind != TokShapeData {
			if tok.Kind == TokEOF {
				p.end = endStateUnterminated
			}
			return data
		}
		tok = p.next()
		data.Span.End = tok.Span.End
		if tok.Text == "" {
			return data
		}
		data.Tokens = append(data.Tokens, tok)
	}
}

func (p *parser) parseText(closers ...TokenKind) Text {
	text := Text{Tokens: []Token{}}
	for {
		tok := p.peek()
		if isCloser(tok.Kind, closers) {
			return finishText(text)
		}
		if !isLabelTextToken(tok.Kind) {
			return finishText(text)
		}
		if len(text.Tokens) > 0 && isQuotedToken(tok.Kind) {
			p.report(plainDiagnostic(labelRuleFor(text.Tokens[0].Kind), openingQuote(tok)))
			return finishText(text)
		}
		tok = p.next()
		if len(text.Tokens) == 0 {
			text.Kind = tokenLabelKind(tok.Kind)
		}
		text.Tokens = append(text.Tokens, tok)
	}
}

func finishText(text Text) Text {
	if len(text.Tokens) > 0 {
		text.Span = source.Span{Start: text.Tokens[0].Span.Start, End: text.Tokens[len(text.Tokens)-1].Span.End}
	}
	return text
}

func isCloser(k TokenKind, closers []TokenKind) bool {
	for _, want := range closers {
		if k == want {
			return true
		}
	}
	return false
}

func (p *parser) parseIdString() (IdString, bool) {
	out := IdString{}
	for isIDToken(p.peek().Kind) {
		out.Tokens = append(out.Tokens, p.next())
	}
	if len(out.Tokens) == 0 {
		return IdString{}, false
	}
	out.Span = source.Span{Start: out.Tokens[0].Span.Start, End: out.Tokens[len(out.Tokens)-1].Span.End}
	return out, true
}

type linkOutcome uint8

const (
	linkNone linkOutcome = iota
	linkFound
	linkBroken
)

func (p *parser) tryParseLink() (Link, linkOutcome) {
	save := p.i
	p.skipSpaces()
	link := Link{}
	stmt := LinkStatement{}
	if p.at(TokLinkID) {
		id := p.parseLinkID()
		stmt.ID = &id
		stmt.Span = id.Span
	}
	if open, ok := p.accept(TokLink); ok {
		stmt.Open = open
		stmt.Span = spanJoin(stmt.Span, open.Span)
		p.reportArrowInvalid(open)
		p.reportUnsupportedMarker()
		link.Statement = stmt
		link.Span = stmt.Span
		if arrow, ok := p.tryParseArrowText(); ok {
			link.Arrow = &arrow
			link.Span = spanJoin(link.Span, arrow.Span)
		}
		return link, linkFound
	}
	start, ok := p.accept(TokStartLink)
	if !ok {
		p.i = save
		return Link{}, linkNone
	}
	stmt.Open = start
	stmt.Span = spanJoin(stmt.Span, start.Span)
	edge := p.parseEdgeText()
	link.Edge = &edge
	end, ok := p.accept(TokLink)
	if !ok {
		tok := p.peek()
		p.report(unexpectedDiagnostic(codeUnexpectedToken, tok.Span, tok.Text, []string{"LINK"}))
		p.i = save
		return Link{}, linkBroken
	}
	stmt.End = &end
	stmt.Span = spanJoin(stmt.Span, end.Span)
	link.Statement = stmt
	link.Span = spanJoin(stmt.Span, edge.Span)
	if arrow, ok := p.tryParseArrowText(); ok {
		link.Arrow = &arrow
		link.Span = spanJoin(link.Span, arrow.Span)
	}
	return link, linkFound
}

func (p *parser) reportArrowInvalid(open Token) {
	if strings.TrimSpace(open.Text) == "->" {
		p.report(plainDiagnostic(codeArrowInvalid, open.Span))
	}
}

func (p *parser) reportUnsupportedMarker() {
	next := p.peek()
	if next.Kind != TokLink {
		return
	}
	p.next()
	p.report(plainDiagnostic(codeLinkUnsupportedMark, source.Span{Start: p.toks[p.i-2].Span.Start, End: next.Span.End}))
}

func (p *parser) parseLinkID() IdString {
	tok := p.next()
	text := tok.Text
	if len(text) > 0 && text[len(text)-1] == '@' {
		text = text[:len(text)-1]
	}
	tok.Text = text
	tok.Span.End = tok.Span.Start + len(text)
	return IdString{Tokens: []Token{tok}, Span: tok.Span}
}

func (p *parser) parseEdgeText() EdgeText {
	text := Text{Tokens: []Token{}}
	for {
		tok := p.peek()
		if len(text.Tokens) > 0 && isQuotedToken(tok.Kind) {
			break
		}
		if tok.Kind != TokEdgeText && !isQuotedToken(tok.Kind) {
			break
		}
		tok = p.next()
		if len(text.Tokens) == 0 {
			text.Kind = tokenLabelKind(tok.Kind)
		}
		text.Tokens = append(text.Tokens, tok)
	}
	text = finishText(text)
	return EdgeText{Text: text, Span: text.Span}
}

func (p *parser) tryParseArrowText() (ArrowText, bool) {
	open, ok := p.accept(TokPipe)
	if !ok {
		return ArrowText{}, false
	}
	text := p.parseText(TokPipe)
	arrow := ArrowText{Text: text, Span: source.Span{Start: open.Span.Start, End: textEnd(text, open)}}
	if closer, ok := p.accept(TokPipe); ok {
		arrow.Span.End = closer.Span.End
		return arrow, true
	}
	p.report(arrowSpanDiagnostic(arrow.Span))
	return arrow, true
}

func arrowSpanDiagnostic(span source.Span) diag.Diagnostic {
	return plainDiagnostic(codeUnclosedNodeBracket, span)
}

func isQuotedToken(k TokenKind) bool {
	return k == TokStr || k == TokMDStr
}

func isLabelTextToken(k TokenKind) bool {
	return isTextToken(k) || isQuotedToken(k)
}

func tokenLabelKind(k TokenKind) LabelKind {
	switch k {
	case TokStr:
		return LabelString
	case TokMDStr:
		return LabelMarkdown
	default:
		return LabelPlain
	}
}
