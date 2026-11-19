package railroad

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeNesting      = "limit/nesting-depth"
	codeUnexpected   = "railroad/unexpected-token"
	codeUnknown      = "railroad/unknown-statement"
	codeUnterminated = "railroad/unterminated"

	maxDepth = 64
)

var (
	idNames     = [...]string{"RR_ID", "EBNF_ID", "ABNF_RULENAME", "PEG_ID"}
	stringNames = [...]string{"RR_STRING", "EBNF_STRING", "ABNF_STRING", "PEG_STRING"}
	operators   = [...][]string{Constructor: {"="}, EBNF: {"=", "::="}, ABNF: {"="}, PEG: {"<-"}}
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	notation := notationOf(text, removed)
	p := &parser{src: text, n: notation, tokens: lex(text, removed, notation)}
	return p.document(), p.diags
}

func notationOf(text string, removed []source.Span) Notation {
	i := 0
	for i < len(text) {
		if end, ok := removedEnd(removed, i); ok {
			i = end
			continue
		}
		if c := text[i]; c != ' ' && c != '\t' && c != '\r' && c != '\n' {
			break
		}
		i++
	}
	for n := Constructor; n <= PEG; n++ {
		if end := i + len(headers[n]); end <= len(text) && equalFoldASCII(text[i:end], headers[n]) {
			return n
		}
	}
	return Constructor
}

func removedEnd(removed []source.Span, at int) (int, bool) {
	for _, span := range removed {
		if span.Start <= at && at < span.End {
			return span.End, true
		}
	}
	return 0, false
}

type parser struct {
	src    string
	tokens []Token
	n      Notation
	at     int
	depth  int
	diags  []diag.Diagnostic
}

func (p *parser) tok() Token { return p.tokens[min(p.at, len(p.tokens)-1)] }

func (p *parser) kind() string { return p.tok().Kind }

func (p *parser) take() Token {
	t := p.tok()
	if p.at < len(p.tokens)-1 {
		p.at++
	}
	return t
}

func (p *parser) lastEnd() int {
	if p.at == 0 {
		return 0
	}
	return p.tokens[min(p.at, len(p.tokens))-1].Span.End
}

func (p *parser) since(start int) source.Span {
	return source.Span{Start: start, End: max(p.lastEnd(), start)}
}

func (p *parser) halt() { p.at = len(p.tokens) - 1 }

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
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

func (p *parser) name(kind string) string {
	switch kind {
	case "HEADER":
		return headers[p.n]
	case "ID":
		return idNames[p.n]
	case "STRING":
		return stringNames[p.n]
	case "SPECIAL":
		return "EBNF_SPECIAL_SEQUENCE"
	case "NUMVAL":
		return "ABNF_NUMVAL"
	case "REPEAT":
		return "ABNF_REPEAT"
	case "EXACT_REPEAT":
		return "ABNF_EXACT_REPEAT"
	}
	return kind
}

func (p *parser) display(t Token) string {
	if t.Kind == "EOF" {
		return "EOF"
	}
	return p.src[t.Span.Start:t.Span.End]
}

func (p *parser) fail(expected ...string) {
	t := p.tok()
	if t.Kind == "UNTERMINATED" {
		p.issue(codeUnterminated, "unterminated "+t.Text, t.Span)
		p.halt()
		return
	}
	names := make([]string, len(expected))
	for i, kind := range expected {
		names[i] = p.name(kind)
	}
	slices.Sort(names)
	names = slices.Compact(names)
	p.issue(codeUnexpected, "unexpected "+p.display(t)+", expected one of: "+strings.Join(names, ", "), t.Span)
}

func (p *parser) expect(kind string, expected ...string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	if len(expected) == 0 {
		expected = []string{kind}
	}
	p.fail(expected...)
	return Token{}, false
}

func (p *parser) enter(at Token) bool {
	if p.depth >= maxDepth {
		p.issue(codeNesting, "nesting depth exceeds 64", at.Span)
		p.halt()
		return false
	}
	p.depth++
	return true
}

func (p *parser) document() *Start {
	start := &Start{Notation: p.n}
	at := p.tok().Span.Start
	header, ok := p.expect("HEADER")
	start.Header = header
	if !ok {
		start.Header = Token{Kind: "HEADER", Span: source.Span{Start: at, End: at}}
	}
	for p.kind() != "EOF" {
		p.statement(start)
	}
	start.Span = source.Span{Start: start.Header.Span.Start, End: len(p.src)}
	return start
}

func metaKind(kind string) (MetaKind, bool) {
	switch kind {
	case "TITLE":
		return MetaTitle, true
	case "ACC_TITLE":
		return MetaAccTitle, true
	case "ACC_DESCR":
		return MetaAccDescr, true
	}
	return 0, false
}

func (p *parser) statement(start *Start) {
	t := p.tok()
	if kind, ok := metaKind(t.Kind); ok && len(start.Rules) == 0 {
		p.take()
		start.Meta = append(start.Meta, Meta{Span: t.Span, Kind: kind, Value: p.metaValue(kind, t)})
		return
	}
	switch t.Kind {
	case "ID":
		if rule, ok := p.rule(len(start.Rules)); ok {
			start.Rules = append(start.Rules, rule)
		}
	case "UNTERMINATED":
		p.fail()
	default:
		p.unknownStatement()
	}
}

func (p *parser) metaValue(kind MetaKind, t Token) string {
	switch kind {
	case MetaTitle:
		return metaTitle(t.Text, p.n)
	case MetaAccTitle:
		return metaAccTitle(t.Text)
	}
	return metaAccDescr(t.Text)
}

func (p *parser) unknownStatement() {
	first := p.take()
	if _, meta := metaKind(first.Kind); !meta {
		p.resync()
	}
	p.issue(codeUnknown, "unknown statement "+p.display(first), source.Span{Start: first.Span.Start, End: max(p.lastEnd(), first.Span.End)})
}

func (p *parser) rule(index int) (Rule, bool) {
	p.depth = 0
	name := p.take()
	rule := Rule{Index: index, Name: Value{Span: name.Span, Text: name.Text}}
	if body, ok := p.afterName(); ok {
		if semicolon, ok := p.expect(";"); ok {
			rule.Body = body
			rule.Span = source.Span{Start: name.Span.Start, End: semicolon.Span.End}
			return rule, true
		}
	}
	p.resync()
	return Rule{}, false
}

func (p *parser) afterName() (Expression, bool) {
	if !slices.Contains(operators[p.n], p.kind()) {
		p.fail(operators[p.n]...)
		return nil, false
	}
	p.take()
	return p.body()
}

func (p *parser) body() (Expression, bool) {
	switch p.n {
	case EBNF:
		return asExpression(p.ebnfChoice())
	case ABNF:
		return asExpression(p.abnfAlternation())
	case PEG:
		return asExpression(p.pegChoice())
	}
	return p.railroadExpr()
}

func asExpression[T Expression](node T, ok bool) (Expression, bool) {
	if !ok {
		return nil, false
	}
	return node, true
}

func (p *parser) resync() {
	if p.n == ABNF {
		for p.kind() != "EOF" && !p.ruleStartsHere() {
			p.at++
		}
		return
	}
	depth := 0
	for {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return
		case ";":
			if depth == 0 {
				p.at++
				return
			}
		case "(", "[", "{":
			depth++
		case ")", "]", "}":
			depth = max(depth-1, 0)
		}
		p.at++
	}
}

func (p *parser) ruleStartsHere() bool {
	t := p.tok()
	if t.Kind != "ID" || p.at+1 >= len(p.tokens) || p.tokens[p.at+1].Kind != "=" {
		return false
	}
	for i := t.Span.Start - 1; i >= 0; i-- {
		switch p.src[i] {
		case ' ', '\t':
		case '\n', '\r':
			return true
		default:
			return false
		}
	}
	return true
}
