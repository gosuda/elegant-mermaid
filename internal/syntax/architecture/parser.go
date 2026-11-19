package architecture

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "architecture/unexpected-token"
	codeUnknown      = "architecture/unknown-statement"
	codeUnterminated = "architecture/unterminated"
	codeDirection    = "architecture/invalid-direction"
	codeTooFew       = "architecture/align-too-few-members"
)

var metadataFields = map[string]string{"ACC_DESCR": "accDescr", "ACC_TITLE": "accTitle", "TITLE": "title"}

func Parse(src []byte, removed []source.Span) (*Architecture, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	p.skipNewlines()
	root := &Architecture{Header: p.header()}
	p.statements(root)
	root.Span = source.Span{Start: root.Header.Span.Start, End: len(text)}
	return root, p.diags
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
	case "architecture-beta", "architecture":
		return p.take()
	}
	p.unexpected("architecture", "architecture-beta")
	return Token{Kind: "architecture-beta"}
}

func (p *parser) statements(root *Architecture) {
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
			p.statementOrUnknown(root)
		}
	}
}

func (p *parser) statementOrUnknown(root *Architecture) {
	first := p.token()
	kind, known := p.statementKind(first)
	if !known {
		p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(p.lineEnd(), first.Span.End)})
		p.skipLine()
		return
	}
	if kind == nil {
		return
	}
	statement := Statement{Span: source.Span{Start: first.Span.Start, End: p.statementEnd}, Kind: kind}
	if merged, ok := mergeMetadata(root.Statements, statement); ok {
		root.Statements = merged
		return
	}
	root.Statements = append(root.Statements, statement)
}

func mergeMetadata(statements []Statement, next Statement) ([]Statement, bool) {
	incoming, ok := next.Kind.(*TitleAndAccessibilities)
	if !ok || len(statements) == 0 {
		return statements, false
	}
	last := &statements[len(statements)-1]
	existing, ok := last.Kind.(*TitleAndAccessibilities)
	if !ok {
		return statements, false
	}
	existing.Items = append(existing.Items, incoming.Items...)
	last.Span.End = next.Span.End
	return statements, true
}

func (p *parser) statementKind(first Token) (StatementKind, bool) {
	switch first.Kind {
	case "group":
		return p.group(), true
	case "service":
		return p.service(), true
	case "junction":
		return p.junction(), true
	case "align":
		return p.alignment(), true
	case "ID":
		return p.edge(), true
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

func (p *parser) value(kind string) (*Value, bool) {
	if p.kind() != kind {
		p.unexpected(kind)
		return nil, false
	}
	token := p.take()
	return &Value{Text: token.Text, Span: token.Span}, true
}

var (
	groupSlots    = [][]string{{"ARCH_ICON"}, {"ARCH_TITLE"}, {"in"}}
	serviceSlots  = [][]string{{"ARCH_ICON", "STRING"}, {"ARCH_TITLE"}, {"in"}}
	junctionSlots = [][]string{{"in"}}
)

func pending(slots [][]string, from int) []string {
	var out []string
	for _, kinds := range slots[from:] {
		out = append(out, kinds...)
	}
	return out
}

func (p *parser) fill(slots [][]string, assign func(slot int, kind string, v Value)) (int, bool) {
	next := 0
	for i, kinds := range slots {
		kind := p.kind()
		if !slices.Contains(kinds, kind) {
			continue
		}
		token := p.take()
		if kind == "in" {
			id, ok := p.value("ID")
			if !ok {
				return 0, false
			}
			token = Token{Text: id.Text, Span: id.Span}
		}
		assign(i, kind, Value{Text: token.Text, Span: token.Span})
		next = i + 1
	}
	return next, true
}

func (p *parser) group() StatementKind {
	keyword := p.take().Span
	id, ok := p.value("ID")
	if !ok {
		return p.reject()
	}
	node := &Group{Keyword: keyword, ID: *id}
	next, ok := p.fill(groupSlots, func(slot int, _ string, v Value) {
		switch slot {
		case 0:
			node.Icon = &v
		case 1:
			node.Title = &v
		default:
			node.In = &v
		}
	})
	if !ok {
		return p.reject()
	}
	return p.finish(node, pending(groupSlots, next)...)
}

func (p *parser) service() StatementKind {
	keyword := p.take().Span
	id, ok := p.value("ID")
	if !ok {
		return p.reject()
	}
	node := &Service{Keyword: keyword, ID: *id}
	next, ok := p.fill(serviceSlots, func(slot int, kind string, v Value) {
		switch {
		case slot == 0 && kind == "STRING":
			node.IconText = &v
		case slot == 0:
			node.Icon = &v
		case slot == 1:
			node.Title = &v
		default:
			node.In = &v
		}
	})
	if !ok {
		return p.reject()
	}
	return p.finish(node, pending(serviceSlots, next)...)
}

func (p *parser) junction() StatementKind {
	keyword := p.take().Span
	id, ok := p.value("ID")
	if !ok {
		return p.reject()
	}
	node := &Junction{Keyword: keyword, ID: *id}
	next, ok := p.fill(junctionSlots, func(_ int, _ string, v Value) { node.In = &v })
	if !ok {
		return p.reject()
	}
	return p.finish(node, pending(junctionSlots, next)...)
}

func (p *parser) alignment() StatementKind {
	keyword := p.take().Span
	switch p.kind() {
	case "row", "column":
	default:
		p.unexpected("column", "row")
		return p.reject()
	}
	direction := p.take()
	node := &Alignment{Keyword: keyword, Direction: Value{Text: direction.Kind, Span: direction.Span}}
	for p.kind() == "ID" {
		member := p.take()
		node.Members = append(node.Members, Value{Text: member.Text, Span: member.Span})
	}
	if len(node.Members) < 2 {
		if p.kind() == "NEWLINE" || p.kind() == "EOF" {
			p.issue(codeTooFew, "alignment requires at least two members", source.Span{Start: keyword.Start, End: p.contentEnd()})
			return p.reject()
		}
		p.unexpected("ID")
		return p.reject()
	}
	return p.finish(node, "ID")
}

func (p *parser) optionalSpan(kind string) *source.Span {
	if p.kind() != kind {
		return nil
	}
	span := p.take().Span
	return &span
}

func (p *parser) colon(alternatives ...string) bool {
	if p.kind() == ":" {
		p.take()
		return true
	}
	p.unexpected(append([]string{":"}, alternatives...)...)
	return false
}

func absent(span *source.Span, kind string) []string {
	if span == nil {
		return []string{kind}
	}
	return nil
}

func (p *parser) edge() StatementKind {
	lhs := p.take()
	node := &Edge{LhsID: Value{Text: lhs.Text, Span: lhs.Span}}
	node.LhsGroup = p.optionalSpan("ARROW_GROUP")
	if !p.colon(absent(node.LhsGroup, "ARROW_GROUP")...) || !p.port(&node.LhsDir) {
		return p.reject()
	}
	node.LhsInto = p.optionalSpan("ARROW_INTO")
	if !p.dashes(node) {
		return p.reject()
	}
	node.RhsInto = p.optionalSpan("ARROW_INTO")
	if !p.port(&node.RhsDir, absent(node.RhsInto, "ARROW_INTO")...) || !p.colon() {
		return p.reject()
	}
	rhs, ok := p.value("ID")
	if !ok {
		return p.reject()
	}
	node.RhsID = *rhs
	node.RhsGroup = p.optionalSpan("ARROW_GROUP")
	return p.finish(node, "ARROW_GROUP")
}

func (p *parser) port(dir *Value, alternatives ...string) bool {
	switch p.kind() {
	case "ARROW_DIRECTION":
		token := p.take()
		*dir = Value{Text: token.Text, Span: token.Span}
		return true
	case "ID":
		token := p.token()
		p.issue(codeDirection, "invalid edge direction "+token.Text+"; expected L, R, T, B", token.Span)
		return false
	}
	p.unexpected(append([]string{"ARROW_DIRECTION"}, alternatives...)...)
	return false
}

func (p *parser) dashes(node *Edge) bool {
	switch p.kind() {
	case "--":
		p.take()
		return true
	case "-":
		p.take()
		title, ok := p.value("ARCH_TITLE")
		if !ok {
			return false
		}
		node.Title = title
		_, ok = p.value("-")
		return ok
	}
	p.unexpected(append([]string{"--", "-"}, absent(node.LhsInto, "ARROW_INTO")...)...)
	return false
}

func (p *parser) metadata() StatementKind {
	token := p.take()
	item := MetadataItem{Field: metadataFields[token.Kind], Value: token.Text, Span: token.Span}
	return p.finish(&TitleAndAccessibilities{Items: []MetadataItem{item}})
}
