package flowchart

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func Parse(src []byte, removed []source.Span) (*File, []diag.Diagnostic) {
	lx := newLexer(src, removed)
	toks := lx.lexAll()
	p := newParser(src, toks)
	file := p.parse()
	diags := append(lx.diags, p.diags...)
	diags = append(diags, eofDiagnostics(lx, p, len(src))...)
	attachFixes(src, diags)
	diag.Sort(diags)
	if diags == nil {
		return file, []diag.Diagnostic{}
	}
	return file, diags
}

type endState uint8

const (
	endStateClean endState = iota
	endStateUnclosedBracket
	endStateUnterminated
)

func eofDiagnostics(lx *lexer, p *parser, size int) []diag.Diagnostic {
	var out []diag.Diagnostic
	switch p.end {
	case endStateUnterminated:
		if lx.eofShapeSet {
			out = append(out, tokenDiagnostic(codeUnterminated, source.Span{Start: lx.eofShape.Start, End: size}, "@{"))
		}
		if lx.eofAccSet {
			out = append(out, tokenDiagnostic(codeUnterminated, source.Span{Start: lx.eofAcc.Start, End: size}, "{"))
		}
		return out
	case endStateUnclosedBracket:
		if lx.eofLabelSet {
			out = append(out, tokenDiagnostic(codeUnclosedNodeBracket, source.Span{Start: lx.eofLabel.Start, End: size}, string(lx.src[lx.eofLabel.Start:lx.eofLabel.End])))
		}
		return out
	}
	if lx.eofQuote >= 0 {
		out = append(out, plainDiagnostic(codeQuoteUnclosed, source.Span{Start: lx.eofQuote, End: size}))
	}
	return out
}

type parser struct {
	src   []byte
	toks  []Token
	i     int
	depth int
	diags []diag.Diagnostic
	end   endState
}

func newParser(src []byte, toks []Token) *parser {
	return &parser{src: src, toks: toks}
}

func (p *parser) eofSpan() source.Span {
	n := len(p.src)
	return source.Span{Start: n, End: n}
}

func (p *parser) peek() Token {
	if p.i < len(p.toks) {
		return p.toks[p.i]
	}
	return Token{Kind: TokEOF, Span: p.eofSpan(), StringOpen: -1}
}

func (p *parser) at(k TokenKind) bool { return p.peek().Kind == k }

func (p *parser) atAny(ks ...TokenKind) bool {
	return slices.Contains(ks, p.peek().Kind)
}

func (p *parser) next() Token {
	tok := p.peek()
	if p.i < len(p.toks) {
		p.i++
	}
	return tok
}

func (p *parser) accept(k TokenKind) (Token, bool) {
	if p.at(k) {
		return p.next(), true
	}
	return Token{}, false
}

func (p *parser) report(d diag.Diagnostic) { p.diags = append(p.diags, d) }

func (p *parser) parse() *File {
	file := &File{Span: source.Span{Start: 0, End: len(p.src)}}
	file.Config = p.parseHeader()
	file.Doc = p.parseStatements()
	return file
}

func (p *parser) skipTrivia() {
	for p.atAny(TokSpace, TokNewline, TokSemi) {
		p.next()
	}
}

func (p *parser) parseHeader() GraphConfig {
	p.skipTrivia()
	kw, ok := p.accept(TokGraph)
	if !ok {
		return GraphConfig{}
	}
	cfg := GraphConfig{Keyword: kw, Span: kw.Span}
	if p.at(TokSpace) {
		p.next()
	}
	switch tok := p.peek(); {
	case tok.Kind == TokDir || isDirectionKeyword(tok.Kind):
		cfg.Direction = &tok
		cfg.Span.End = tok.Span.End
		p.next()
	case tok.Kind == TokNoDir:
		p.next()
	case tok.Kind == TokNodeString:
		p.recoverDirection()
	}
	if p.atAny(TokNewline, TokSemi) {
		p.next()
	}
	return cfg
}

func isDirectionKeyword(k TokenKind) bool {
	switch k {
	case TokDirectionTB, TokDirectionBT, TokDirectionRL, TokDirectionLR, TokDirectionTD:
		return true
	}
	return false
}

func (p *parser) recoverDirection() {
	word := p.next()
	for !p.atAny(TokEOF, TokNewline, TokSemi) {
		if p.at(TokDir) {
			p.report(plainDiagnostic(codeDirKeywordInvalid, word.Span))
			p.skipToLineEnd()
			return
		}
		p.next()
	}
	p.report(plainDiagnostic(codeDirInvalid, word.Span))
	p.skipToLineEnd()
}

func (p *parser) skipToLineEnd() {
	for !p.atAny(TokEOF, TokNewline, TokSemi) {
		p.next()
	}
}

func (p *parser) parseStatements() Document {
	doc := Document{}
	for {
		p.skipTrivia()
		tok := p.peek()
		if tok.Kind == TokEOF {
			return doc
		}
		stmt, ok := p.parseStatement()
		if !ok {
			continue
		}
		doc.Lines = append(doc.Lines, Line{Stmt: stmt})
		doc.Span = spanJoin(doc.Span, stmt.Bounds())
	}
}

func spanJoin(into, add source.Span) source.Span {
	if into.End == 0 && into.Start == 0 {
		return add
	}
	if add.Start < into.Start {
		into.Start = add.Start
	}
	if add.End > into.End {
		into.End = add.End
	}
	return into
}

func (p *parser) parseStatement() (Stmt, bool) {
	switch p.peek().Kind {
	case TokSubgraph:
		return p.parseSubgraph(), true
	case TokStyle:
		return p.parseStyle(), true
	case TokClassDef:
		return p.parseClassDef(), true
	case TokClass:
		return p.parseClass(), true
	case TokLinkStyle:
		return p.parseLinkStyle(), true
	case TokClick:
		return p.parseClick(), true
	default:
		return p.parseContentStatement()
	}
}

func (p *parser) parseContentStatement() (Stmt, bool) {
	switch p.peek().Kind {
	case TokAccTitle:
		return p.parseAccTitle(), true
	case TokAccDescr:
		return p.parseAccDescr(), true
	case TokAccDescrMultilineValue:
		return p.parseAccDescrBlock(), true
	case TokDirectionTB, TokDirectionBT, TokDirectionRL, TokDirectionLR, TokDirectionTD:
		return p.parseDirection(), true
	case TokEnd:
		return p.parseStrayEnd(), true
	}
	if p.atVertexStart() {
		return p.parseVertexStatement()
	}
	return p.rejectStatement()
}

func (p *parser) rejectStatement() (Stmt, bool) {
	tok := p.next()
	p.skipToStatementBoundary()
	end := p.lastEnd()
	p.report(tokenDiagnostic(codeUnknownStatement, source.Span{Start: tok.Span.Start, End: end}, tok.Text))
	return nil, false
}

func (p *parser) lastEnd() int {
	if p.i > 0 {
		return p.toks[p.i-1].Span.End
	}
	return p.peek().Span.Start
}

func (p *parser) skipToStatementBoundary() {
	for !p.atAny(TokEOF, TokNewline, TokSemi) {
		p.next()
	}
}

func (p *parser) parseStrayEnd() Stmt {
	kw := p.next()
	p.report(plainDiagnostic(codeEndWithoutSubgraph, kw.Span))
	return &EmptyStatement{node: node{Span: kw.Span}}
}

func (p *parser) parseDirection() Stmt {
	kw := p.next()
	return &DirectionStatement{node: node{Span: kw.Span}, Keyword: kw, Value: kw}
}

func (p *parser) parseAccTitle() Stmt {
	kw := p.next()
	stmt := &AccTitle{node: node{Span: kw.Span}, Keyword: kw}
	if val, ok := p.accept(TokAccTitleValue); ok {
		stmt.Value = val
		stmt.Span.End = val.Span.End
	}
	return stmt
}

func (p *parser) parseAccDescr() Stmt {
	kw := p.next()
	stmt := &AccDescr{node: node{Span: kw.Span}, Keyword: kw}
	if val, ok := p.accept(TokAccDescrValue); ok {
		stmt.Value = val
		stmt.Span.End = val.Span.End
	}
	return stmt
}

func (p *parser) parseAccDescrBlock() Stmt {
	val := p.next()
	return &AccDescrBlock{node: node{Span: val.Span}, Value: val}
}
