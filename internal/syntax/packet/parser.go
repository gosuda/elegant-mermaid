package packet

import (
	"math"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "packet/unexpected-token"
	codeUnknown      = "packet/unknown-statement"
	codeUnterminated = "packet/unterminated"
)

var metadataFields = map[string]string{"ACC_DESCR": "accDescr", "ACC_TITLE": "accTitle", "TITLE": "title"}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	p.skipNewlines()
	start := &Start{}
	start.Header = p.header()
	p.statements(start)
	start.Span = source.Span{Start: start.Header.Span.Start, End: len(text)}
	return start, p.diags
}

type parser struct {
	src          string
	tokens       []Token
	at           int
	statementEnd int
	diags        []diag.Diagnostic
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

func (p *parser) lineEnd() int {
	for i := p.at; i < len(p.tokens); i++ {
		switch p.tokens[i].Kind {
		case "NEWLINE", "EOF", "UNTERMINATED":
			return p.tokens[i].Span.Start
		}
	}
	return len(p.src)
}

func (p *parser) skipLine() {
	for {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return
		case "NEWLINE":
			p.take()
			return
		}
		p.take()
	}
}

func (p *parser) header() Token {
	switch p.kind() {
	case "packet", "packet-beta":
		return p.take()
	}
	p.unexpected("packet", "packet-beta")
	return Token{}
}

func (p *parser) statements(start *Start) {
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
		default:
			p.statementOrUnknown(start)
		}
	}
}

func (p *parser) statementOrUnknown(start *Start) {
	first := p.token()
	var kind StatementKind
	switch first.Kind {
	case "INT", "+":
		kind = p.block()
	case "ACC_DESCR", "ACC_TITLE", "TITLE":
		kind = p.metadata()
	default:
		p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(p.lineEnd(), first.Span.End)})
		p.skipLine()
		return
	}
	if kind != nil {
		start.Statements = append(start.Statements, Statement{Span: source.Span{Start: first.Span.Start, End: p.statementEnd}, Kind: kind})
	}
}

func (p *parser) finish(kind StatementKind) StatementKind {
	end := p.contentEnd()
	switch p.kind() {
	case "NEWLINE":
		p.take()
	case "EOF":
	default:
		p.unexpected("EOF", "NEWLINE")
		return p.reject()
	}
	p.statementEnd = end
	return kind
}

func (p *parser) reject() StatementKind {
	p.skipLine()
	return nil
}

func (p *parser) operand() (*Operand, bool) {
	if p.kind() != "INT" {
		p.unexpected("INT")
		return nil, false
	}
	token := p.take()
	return &Operand{Value: parseInt(token.Text), Span: token.Span}, true
}

func parseInt(text string) int64 {
	value, err := strconv.ParseInt(text, 10, 64)
	if err != nil || value > math.MaxInt32 {
		return math.MaxInt32
	}
	return value
}

func (p *parser) block() StatementKind {
	node := &PacketBlock{}
	var colon []string
	var ok bool
	if p.kind() == "+" {
		p.take()
		colon = []string{":"}
		node.Bits, ok = p.operand()
	} else {
		colon, ok = p.rangeOperands(node)
	}
	if !ok {
		return p.reject()
	}
	return p.label(node, colon)
}

func (p *parser) rangeOperands(node *PacketBlock) ([]string, bool) {
	start, ok := p.operand()
	if !ok {
		return nil, false
	}
	node.Start = start
	if p.kind() != "-" {
		return []string{"-", ":"}, true
	}
	p.take()
	node.End, ok = p.operand()
	return []string{":"}, ok
}

func (p *parser) label(node *PacketBlock, colon []string) StatementKind {
	if p.kind() != ":" {
		p.unexpected(colon...)
		return p.reject()
	}
	p.take()
	if p.kind() != "STRING" {
		p.unexpected("STRING")
		return p.reject()
	}
	label := p.take()
	node.Label = Label{Text: label.Text, Span: label.Span}
	return p.finish(node)
}

func (p *parser) metadata() StatementKind {
	token := p.take()
	return p.finish(&Metadata{Field: metadataFields[token.Kind], Value: token.Text})
}
