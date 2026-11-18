package gitgraph

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "gitgraph/unexpected-token"
	codeUnknown      = "gitgraph/unknown-statement"
	codeUnterminated = "gitgraph/unterminated"
)

var (
	commitOptions  = []string{"STRING", "id:", "msg:", "tag:", "type:"}
	mergeOptions   = []string{"id:", "tag:", "type:"}
	pickOptions    = []string{"id:", "parent:", "tag:"}
	commitTypes    = []string{"HIGHLIGHT", "NORMAL", "REVERSE"}
	metadataFields = map[string]string{"ACC_DESCR": "accDescr", "ACC_TITLE": "accTitle", "TITLE": "title"}
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	p.skipNewlines()
	start := &Start{}
	start.Header, start.Direction = p.header()
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

func (p *parser) header() (Token, *Token) {
	switch p.kind() {
	case "gitGraph:":
		return p.take(), nil
	case "gitGraph":
		return p.bareHeader()
	}
	p.unexpected("gitGraph", "gitGraph:")
	return Token{}, nil
}

func (p *parser) bareHeader() (Token, *Token) {
	header := p.take()
	switch p.kind() {
	case ":":
		p.take()
	case "LR", "TB", "BT":
		direction := p.take()
		if p.kind() != ":" {
			p.unexpected(":")
			return header, &direction
		}
		p.take()
		return header, &direction
	}
	return header, nil
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
	kind, known := p.statementKind(first)
	if !known {
		p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(p.lineEnd(), first.Span.End)})
		p.skipLine()
		return
	}
	if kind != nil {
		start.Statements = append(start.Statements, Statement{Span: source.Span{Start: first.Span.Start, End: p.statementEnd}, Kind: kind})
	}
}

func (p *parser) statementKind(first Token) (StatementKind, bool) {
	switch first.Kind {
	case "commit":
		return p.commit(), true
	case "branch":
		return p.branch(), true
	case "merge":
		return p.merge(), true
	case "checkout", "switch":
		return p.checkout(), true
	case "cherry-pick":
		return p.cherryPick(), true
	case "ACC_DESCR", "ACC_TITLE", "TITLE":
		return p.metadata(), true
	}
	return nil, false
}

func (p *parser) finish(kind StatementKind, expected ...string) StatementKind {
	end := p.contentEnd()
	switch p.kind() {
	case "NEWLINE":
		p.take()
	case "EOF":
	default:
		p.unexpected(append(slices.Clone(expected), "EOF", "NEWLINE")...)
		return p.reject()
	}
	p.statementEnd = end
	return kind
}

func (p *parser) reject() StatementKind {
	p.skipLine()
	return nil
}

func (p *parser) text(kind string) (Value, bool) {
	if p.kind() != kind {
		p.unexpected(kind)
		return Value{}, false
	}
	token := p.take()
	return Value{Text: token.Text, Span: token.Span}, true
}

func (p *parser) name() (Value, bool) {
	switch p.kind() {
	case "REFERENCE", "STRING":
		token := p.take()
		return Value{Text: token.Text, Span: token.Span}, true
	}
	p.unexpected("REFERENCE", "STRING")
	return Value{}, false
}

func (p *parser) commitType() (Value, bool) {
	switch p.kind() {
	case "NORMAL", "REVERSE", "HIGHLIGHT":
		token := p.take()
		return Value{Text: token.Kind, Span: token.Span}, true
	}
	p.unexpected(commitTypes...)
	return Value{}, false
}

type options struct {
	id, message, parent, typ *Value
	tags                     []Value
}

func (p *parser) options(allowed []string) (options, bool) {
	var found options
	for slices.Contains(allowed, p.kind()) {
		keyword := p.kind()
		if keyword == "STRING" {
			keyword = "msg:"
		} else {
			p.take()
		}
		var value Value
		var ok bool
		switch keyword {
		case "type:":
			value, ok = p.commitType()
		default:
			value, ok = p.text("STRING")
		}
		if !ok {
			return found, false
		}
		found.assign(keyword, value)
	}
	return found, true
}

func (o *options) assign(keyword string, value Value) {
	switch keyword {
	case "id:":
		o.id = &value
	case "msg:":
		o.message = &value
	case "parent:":
		o.parent = &value
	case "type:":
		o.typ = &value
	default:
		o.tags = append(o.tags, value)
	}
}

func (p *parser) commit() StatementKind {
	keyword := p.take().Span
	found, ok := p.options(commitOptions)
	if !ok {
		return p.reject()
	}
	return p.finish(&Commit{Keyword: keyword, ID: found.id, Message: found.message, Tags: found.tags, Type: found.typ}, commitOptions...)
}

func (p *parser) merge() StatementKind {
	keyword := p.take().Span
	name, ok := p.name()
	if !ok {
		return p.reject()
	}
	found, ok := p.options(mergeOptions)
	if !ok {
		return p.reject()
	}
	return p.finish(&Merge{Keyword: keyword, Branch: name, ID: found.id, Tags: found.tags, Type: found.typ}, mergeOptions...)
}

func (p *parser) cherryPick() StatementKind {
	keyword := p.take().Span
	found, ok := p.options(pickOptions)
	if !ok {
		return p.reject()
	}
	return p.finish(&CherryPicking{Keyword: keyword, ID: found.id, Tags: found.tags, Parent: found.parent}, pickOptions...)
}

func (p *parser) branch() StatementKind {
	keyword := p.take().Span
	name, ok := p.name()
	if !ok {
		return p.reject()
	}
	node := &Branch{Keyword: keyword, Name: name}
	if p.kind() != "order:" {
		return p.finish(node, "order:")
	}
	p.take()
	token := p.token()
	if token.Kind != "INT" {
		p.unexpected("INT")
		return p.reject()
	}
	p.take()
	node.Order = &Order{Value: parseOrder(token.Text), Span: token.Span}
	return p.finish(node)
}

func parseOrder(text string) int64 {
	value, err := strconv.ParseInt(text, 10, 32)
	if err != nil {
		return 1<<31 - 1
	}
	return value
}

func (p *parser) checkout() StatementKind {
	keyword := p.take()
	name, ok := p.name()
	if !ok {
		return p.reject()
	}
	return p.finish(&Checkout{Keyword: keyword.Span, Switch: keyword.Kind == "switch", Branch: name})
}

func (p *parser) metadata() StatementKind {
	token := p.take()
	return p.finish(&Metadata{Field: metadataFields[token.Kind], Value: token.Text})
}
