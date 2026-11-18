package radar

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "radar/unexpected-token"
	codeUnknown      = "radar/unknown-statement"
	codeUnterminated = "radar/unterminated"
)

var optionValueKinds = map[string]string{
	"showLegend": "BOOLEAN",
	"ticks":      "NUMBER",
	"max":        "NUMBER",
	"min":        "NUMBER",
	"graticule":  "GRATICULE",
}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	p.skipNewlines()
	start := &Start{}
	p.start = start
	start.Header = p.header()
	p.statements()
	start.Span = source.Span{Start: start.Header.Span.Start, End: max(p.contentEnd(), start.Header.Span.End)}
	return start, p.diags
}

type parser struct {
	src    string
	tokens []Token
	at     int
	start  *Start
	diags  []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string { return p.token().Kind }

func (p *parser) take() Token {
	t := p.token()
	if p.at < len(p.tokens) {
		p.at++
	}
	return t
}

func (p *parser) skipNewlines() {
	for p.kind() == "NEWLINE" {
		p.at++
	}
}

func (p *parser) contentEnd() int {
	for i := min(p.at, len(p.tokens)) - 1; i >= 0; i-- {
		if p.tokens[i].Kind != "NEWLINE" {
			return p.tokens[i].Span.End
		}
	}
	return 0
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: diagnosticHelp(code)}
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.src[token.Span.Start:token.Span.End]+", expected one of: "+strings.Join(names, ", "), token.Span)
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() != kind {
		p.unexpected(kind)
		return Token{}, false
	}
	return p.take(), true
}

func (p *parser) header() Token {
	switch p.kind() {
	case "radar-beta:":
		return p.take()
	case headerKeyword:
		header := p.take()
		if p.kind() == ":" {
			p.take()
		}
		return header
	}
	p.unexpected(headerKeyword, headerKeyword+":")
	return Token{}
}

func (p *parser) statements() {
	for {
		switch p.kind() {
		case "EOF":
			return
		case "UNTERMINATED":
			token := p.token()
			p.issue(codeUnterminated, "unterminated "+token.Text, token.Span)
			return
		case "NEWLINE":
			p.take()
		case "ACC_DESCR", "ACC_TITLE", "TITLE":
			p.metadata()
		case "axis":
			p.axes()
		case "curve":
			p.curves()
		case "showLegend", "ticks", "max", "min", "graticule":
			p.options()
		default:
			p.unknown()
		}
	}
}

func (p *parser) unknown() {
	first := p.take()
	end := p.skipStatement()
	p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(end, first.Span.End)})
}

func (p *parser) skipStatement() int {
	end, depth := p.contentEnd(), 0
	for {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return end
		case "NEWLINE":
			if depth == 0 {
				p.take()
				return end
			}
			p.take()
			continue
		case "{":
			depth++
		case "}":
			depth = max(depth-1, 0)
		}
		end = p.take().Span.End
	}
}

func (p *parser) skipBraces() {
	for depth := 1; depth > 0; {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return
		case "{":
			depth++
		case "}":
			depth--
		}
		p.take()
	}
}

func (p *parser) metadata() {
	token := p.take()
	switch p.kind() {
	case "NEWLINE":
		p.skipNewlines()
	case "EOF":
	default:
		p.unexpected("EOF", "NEWLINE")
		p.skipStatement()
		return
	}
	text := &Text{Value: token.Text, Span: token.Span}
	switch token.Kind {
	case "ACC_DESCR":
		p.start.AccDescr = text
	case "ACC_TITLE":
		p.start.AccTitle = text
	default:
		p.start.Title = text
	}
}

func (p *parser) label() (*Label, bool) {
	if p.kind() != "[" {
		return nil, true
	}
	open := p.take()
	value, ok := p.expect("STRING")
	if !ok {
		return nil, false
	}
	closing, ok := p.expect("]")
	if !ok {
		return nil, false
	}
	return &Label{Span: source.Span{Start: open.Span.Start, End: closing.Span.End}, Value: value}, true
}

func (p *parser) axes() {
	p.take()
	for {
		name, ok := p.expect("ID")
		if !ok {
			p.skipStatement()
			return
		}
		label, ok := p.label()
		if !ok {
			p.skipStatement()
			return
		}
		p.start.Axes = append(p.start.Axes, Axis{Span: source.Span{Start: name.Span.Start, End: p.contentEnd()}, Name: name, Label: label})
		if p.kind() != "," {
			return
		}
		p.take()
	}
}

func (p *parser) curves() {
	p.take()
	for {
		curve, ok := p.curve()
		if !ok {
			return
		}
		p.start.Curves = append(p.start.Curves, curve)
		if p.kind() != "," {
			return
		}
		p.take()
	}
}

func (p *parser) curve() (Curve, bool) {
	name, ok := p.expect("ID")
	if !ok {
		p.skipStatement()
		return Curve{}, false
	}
	curve := Curve{Name: name}
	if curve.Label, ok = p.label(); !ok {
		p.skipStatement()
		return Curve{}, false
	}
	if _, ok = p.expect("{"); !ok {
		p.skipStatement()
		return Curve{}, false
	}
	if curve.Entries, ok = p.entries(); !ok {
		p.skipBraces()
		return Curve{}, false
	}
	closing, ok := p.expect("}")
	if !ok {
		p.skipBraces()
		return Curve{}, false
	}
	curve.Span = source.Span{Start: name.Span.Start, End: closing.Span.End}
	return curve, true
}

func (p *parser) entries() ([]Entry, bool) {
	p.skipNewlines()
	first := p.kind()
	if first != "NUMBER" && first != "ID" {
		p.unexpected("ID", "NUMBER")
		return nil, false
	}
	var entries []Entry
	for {
		entry, ok := p.entry(first)
		if !ok {
			return nil, false
		}
		entries = append(entries, entry)
		if p.kind() != "," {
			p.skipNewlines()
			return entries, true
		}
		p.take()
		p.skipNewlines()
	}
}

func (p *parser) entry(kind string) (Entry, bool) {
	if kind == "NUMBER" {
		number, ok := p.number()
		return NumberEntry{Value: number}, ok
	}
	axis, ok := p.expect("ID")
	if !ok {
		return nil, false
	}
	if p.kind() == ":" {
		p.take()
	}
	number, ok := p.number()
	return DetailedEntry{Span: source.Span{Start: axis.Span.Start, End: number.Span.End}, Axis: axis, Value: number}, ok
}

func (p *parser) number() (Number, bool) {
	token, ok := p.expect("NUMBER")
	return Number{Span: token.Span, Text: token.Text}, ok
}

func (p *parser) options() {
	for {
		keyword := p.take()
		value, ok := p.expect(optionValueKinds[keyword.Kind])
		if !ok {
			p.skipStatement()
			return
		}
		p.start.Options = append(p.start.Options, Option{Span: source.Span{Start: keyword.Span.Start, End: value.Span.End}, Name: keyword, Value: value})
		if p.kind() != "," {
			return
		}
		p.take()
		if _, ok = optionValueKinds[p.kind()]; !ok {
			p.unexpected("graticule", "max", "min", "showLegend", "ticks")
			p.skipStatement()
			return
		}
	}
}
