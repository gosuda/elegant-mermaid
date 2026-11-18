package treemap

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "treemap/unexpected-token"
	codeUnknown      = "treemap/unknown-statement"
	codeUnterminated = "treemap/unterminated"
)

func Parse(src []byte, removed []source.Span) (*Treemap, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	return p.treemap(), p.diags
}

type parser struct {
	src    string
	tokens []Token
	at     int
	diags  []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string { return p.token().Kind }

func (p *parser) kindAt(offset int) string {
	if p.at+offset < len(p.tokens) {
		return p.tokens[p.at+offset].Kind
	}
	return "EOF"
}

func (p *parser) take() Token {
	t := p.token()
	if p.at < len(p.tokens) {
		p.at++
	}
	return t
}

func (p *parser) lastEnd() int {
	if p.at == 0 {
		return 0
	}
	return p.tokens[p.at-1].Span.End
}

func (p *parser) raw(span source.Span) string {
	if span.Start < 0 || span.End < span.Start || span.End > len(p.src) {
		return ""
	}
	return p.src[span.Start:span.End]
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	help := ""
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			help = gen.Diagnostics[i].Help
		}
	}
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: help}
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		p.unterminated(token)
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.raw(token.Span)+", expected one of: "+strings.Join(names, ", "), token.Span)
	p.recover(p.lastEnd())
}

func (p *parser) unterminated(token Token) {
	p.issue(codeUnterminated, "unterminated "+token.Text, token.Span)
	p.take()
}

func (p *parser) lineBreakBetween(from, to int) bool {
	if from < 0 || to < from || to > len(p.src) {
		return false
	}
	return strings.ContainsAny(p.src[from:to], "\n\r")
}

func (p *parser) boundary(prevEnd int) bool {
	t := p.token()
	switch t.Kind {
	case "EOF", "UNTERMINATED":
		return true
	}
	return p.lineBreakBetween(prevEnd, t.Span.Start)
}

func (p *parser) recover(prevEnd int) {
	for !p.boundary(prevEnd) {
		prevEnd = p.take().Span.End
	}
}

func (p *parser) treemap() *Treemap {
	for p.kind() == "INDENTATION" {
		p.take()
	}
	doc := &Treemap{Span: source.Span{Start: p.token().Span.Start}}
	if p.kind() == "TREEMAP_KEYWORD" {
		doc.Header = p.take()
	} else {
		p.unexpected("TREEMAP_KEYWORD")
	}
	for p.kind() != "EOF" {
		if stmt := p.statement(); stmt != nil {
			doc.Rows = append(doc.Rows, stmt)
		}
	}
	doc.Span.End = len(p.src)
	return doc
}

func (p *parser) statement() Statement {
	switch p.kind() {
	case "UNTERMINATED":
		p.unterminated(p.token())
		return nil
	case "ACC_DESCR", "ACC_TITLE", "TITLE":
		return p.metadata()
	case "INDENTATION", "STRING2", "CLASS_DEF":
		if row := p.row(); row != nil {
			return row
		}
		return nil
	}
	p.unknownStatement()
	return nil
}

func (p *parser) unknownStatement() {
	first := p.take()
	end := first.Span.End
	for !p.boundary(end) {
		end = p.take().Span.End
	}
	p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: end})
}

func isMetadata(kind string) bool {
	return kind == "ACC_DESCR" || kind == "ACC_TITLE" || kind == "TITLE"
}

func (p *parser) metadata() *TitleAndAccessibilities {
	group := &TitleAndAccessibilities{Span: source.Span{Start: p.token().Span.Start}}
	for isMetadata(p.kind()) {
		token := p.take()
		group.Tokens = append(group.Tokens, token)
		group.Span.End = token.Span.End
	}
	return group
}

func (p *parser) row() *TreemapRow {
	start := p.token().Span.Start
	row := &TreemapRow{}
	if p.kind() == "INDENTATION" {
		token := p.take()
		row.Indent = &Indentation{Span: token.Span, Width: len(token.Text)}
	}
	switch p.kind() {
	case "CLASS_DEF":
		token := p.take()
		_, name, style, _ := matchClassDef(token.Text)
		row.ClassDef = &ClassDef{Span: token.Span, Name: name, Style: style, HasStyle: style != ""}
	case "STRING2":
		if row.Item = p.item(); row.Item == nil {
			return nil
		}
	default:
		p.unexpected("CLASS_DEF", "STRING2")
		return nil
	}
	row.Span = source.Span{Start: start, End: p.lastEnd()}
	return row
}

func (p *parser) item() Item {
	token := p.take()
	name := Name{Span: token.Span, Value: token.Text[1 : len(token.Text)-1]}
	if p.leafAhead() {
		return p.leaf(name)
	}
	selector, ok := p.classSelector()
	if !ok {
		return nil
	}
	return &Section{Span: source.Span{Start: name.Span.Start, End: p.lastEnd()}, Name: name, ClassSelector: selector}
}

func (p *parser) leafAhead() bool {
	offset := 0
	if p.kind() == "INDENTATION" {
		offset = 1
	}
	kind := p.kindAt(offset)
	return kind == "SEPARATOR" || kind == "COMMA"
}

func (p *parser) leaf(name Name) Item {
	if p.kind() == "INDENTATION" {
		p.take()
	}
	p.take()
	expected := []string{"NUMBER2"}
	if p.kind() == "INDENTATION" {
		p.take()
	} else {
		expected = append(expected, "INDENTATION")
	}
	if p.kind() != "NUMBER2" {
		p.unexpected(expected...)
		return nil
	}
	number := p.number(p.take())
	selector, ok := p.classSelector()
	if !ok {
		return nil
	}
	return &Leaf{Span: source.Span{Start: name.Span.Start, End: p.lastEnd()}, Name: name, Value: number, ClassSelector: selector}
}

func (p *parser) classSelector() (*ClassSelector, bool) {
	if p.kind() != "STYLE_SEPARATOR" {
		return nil, true
	}
	p.take()
	if p.kind() != "ID2" {
		p.unexpected("ID2")
		return nil, false
	}
	token := p.take()
	return &ClassSelector{Span: token.Span, Name: token.Text}, true
}

func (p *parser) number(token Token) MyNumber {
	literal, valid := convertNumber(token.Text)
	return MyNumber{Span: token.Span, Raw: token.Text, Literal: literal, Valid: valid}
}

func digitRun(text string, from int) int {
	n := 0
	for from+n < len(text) && text[from+n] >= '0' && text[from+n] <= '9' {
		n++
	}
	return n
}

func convertNumber(raw string) (string, bool) {
	text := strings.ReplaceAll(raw, ",", "")
	whole := digitRun(text, 0)
	end, fraction := whole, 0
	if end < len(text) && text[end] == '.' {
		fraction = digitRun(text, end+1)
		end += 1 + fraction
	}
	if whole == 0 && fraction == 0 {
		return "", false
	}
	return text[:end], true
}
