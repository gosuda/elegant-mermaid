package agentflow

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	cleaned := source.Clean(src, removed)
	p := &parser{source: string(src), cleaned: cleaned, removed: removed, tokens: lex(cleaned)}
	for p.kind() == "SPACE" || p.kind() == "NEWLINE" || p.kind() == "COMMENT" {
		p.at++
	}
	header := p.require("GRAPH")
	if header == nil {
		header = &Token{Kind: "GRAPH", Span: source.Span{Start: 0, End: len(src)}}
	}
	config := p.graphConfig(header)
	document := p.document(0)
	start := &Start{
		Span:     source.Span{Start: header.Span.Start, End: len(src)},
		Header:   *header,
		Config:   config,
		Document: document,
	}
	return start, p.diagnostics
}

type parser struct {
	source      string
	cleaned     *source.Cleaned
	removed     []source.Span
	tokens      []Token
	at          int
	diagnostics []diag.Diagnostic
}

func (p *parser) sliceText(span source.Span) string {
	return string(p.cleaned.Slice(span))
}

func (p *parser) kind() string {
	if p.at < len(p.tokens) {
		return p.tokens[p.at].Kind
	}
	return "EOF"
}

func (p *parser) take() *Token {
	if p.at >= len(p.tokens) {
		return nil
	}
	t := p.tokens[p.at]
	p.at++
	return &t
}

func (p *parser) position() int {
	if p.at < len(p.tokens) {
		return p.tokens[p.at].Span.Start
	}
	return len(p.source)
}

func (p *parser) end() int {
	if p.at > 0 && p.at-1 < len(p.tokens) {
		return p.tokens[p.at-1].Span.End
	}
	return 0
}

func (p *parser) span(start int) source.Span {
	return source.Span{Start: start, End: p.end()}
}

func (p *parser) spaces() int {
	start := p.at
	for p.kind() == "SPACE" {
		p.at++
	}
	return p.at - start
}

func (p *parser) require(kind string) *Token {
	if p.kind() == kind {
		return p.take()
	}
	p.unexpected(kind)
	return nil
}

func (p *parser) unexpected(accepted string) {
	if p.kind() == "UNTERMINATED" {
		if t := p.take(); t != nil {
			p.unterminated(t.Span)
		}
		return
	}
	span := source.Span{Start: len(p.source), End: len(p.source)}
	if p.at < len(p.tokens) {
		span = p.tokens[p.at].Span
	}
	text := p.sliceText(span)
	p.diagnostics = append(p.diagnostics, diagnostic("agentflow/unexpected-token", "unexpected "+text+", expected one of: "+accepted, span))
}

func (p *parser) unterminated(opening source.Span) {
	token := p.sliceText(opening)
	p.diagnostics = append(p.diagnostics, diagnostic("agentflow/unterminated", "unterminated "+token, source.Span{Start: opening.Start, End: len(p.source)}))
}

func (p *parser) graphConfig(header *Token) GraphConfig {
	var authored *Token
	if p.kind() == "DIR" {
		authored = p.take()
	}
	direction := Direction{Span: header.Span, Value: "TB"}
	if authored != nil {
		direction.Span = authored.Span
		direction.Value = normalized(strings.TrimSpace(authored.Text))
	}
	var separator *FirstStmtSeparator
	if p.kind() == "NODIR" {
		if t := p.take(); t != nil {
			separator = &FirstStmtSeparator{Span: t.Span, Tokens: []Token{*t}}
		}
	} else {
		separator = p.firstSeparator()
	}
	return GraphConfig{Span: p.span(header.Span.Start), Direction: direction, Authored: authored, Separator: separator}
}

func (p *parser) firstSeparator() *FirstStmtSeparator {
	start := p.position()
	var tokens []Token
	for p.kind() == "SPACE" {
		if t := p.take(); t != nil {
			tokens = append(tokens, *t)
		} else {
			return nil
		}
	}
	if p.kind() != "NEWLINE" && p.kind() != "SEMI" && p.kind() != "COMMENT" {
		p.unexpected("COMMENT, NEWLINE, SEMI")
		return nil
	}
	if t := p.take(); t != nil {
		tokens = append(tokens, *t)
	} else {
		return nil
	}
	return &FirstStmtSeparator{Span: p.span(start), Tokens: tokens}
}

func (p *parser) document(depth int) Document {
	start := p.position()
	var lines []Line
	for p.kind() != "EOF" {
		if p.kind() == "end" && depth > 0 {
			break
		}
		if p.kind() == "SPACE" || p.kind() == "NEWLINE" || p.kind() == "SEMI" || p.kind() == "COMMENT" {
			if t := p.take(); t != nil {
				lines = append(lines, Line{Span: t.Span})
			}
			continue
		}
		p.documentStatement(depth, &lines)
	}
	end := start
	if len(lines) > 0 {
		end = lines[len(lines)-1].Span.End
	}
	return Document{Span: source.Span{Start: start, End: end}, Lines: lines}
}

func (p *parser) documentStatement(depth int, lines *[]Line) {
	before := p.at
	start := p.position()
	statement := p.statement(depth)
	if statement == nil {
		p.recover()
		p.resynchronizeLine(start)
	} else {
		*lines = append(*lines, Line{Span: statement.Span, Statement: statement})
	}
	if p.at == before {
		p.at++
	}
}

func (p *parser) recover() {
	for p.kind() != "EOF" && p.kind() != "NEWLINE" && p.kind() != "SEMI" && p.kind() != "COMMENT" && p.kind() != "end" {
		p.at++
	}
}

func (p *parser) resynchronizeLine(start int) {
	if p.kind() != "EOF" {
		return
	}
	if len(p.diagnostics) == 0 {
		return
	}
	d := &p.diagnostics[len(p.diagnostics)-1]
	if d.Code != "agentflow/unexpected-token" && d.Code != "agentflow/unknown-statement" {
		return
	}
	if start > len(p.source) {
		return
	}
	tail := p.source[start:]
	offset := strings.IndexAny(tail, "\r\n")
	if offset < 0 {
		return
	}
	end := start + offset
	if d.Span.Start >= end || strings.HasPrefix(tail, "\"") {
		return
	}
	d.Span.End = min(d.Span.End, end)
	removed := make([]source.Span, 0, len(p.removed)+1)
	removed = append(removed, p.removed...)
	removed = append(removed, source.Span{Start: 0, End: end})
	p.tokens = Lex(p.source, removed)
	p.at = 0
}

func (p *parser) statement(depth int) *Statement {
	start := p.position()
	switch p.kind() {
	case "direction_tb", "direction_bt", "direction_rl", "direction_lr", "direction_td":
		return p.directionStatement()
	case "acc_title", "acc_descr", "acc_descr_multiline_value":
		return p.accessibility()
	}
	kind, ok := p.statementKind(depth)
	if !ok {
		return nil
	}
	if kind.Flow == nil && kind.Global == nil && !p.endOfStatement() {
		return nil
	}
	return &Statement{Span: p.span(start), Kind: kind}
}

func (p *parser) directionStatement() *Statement {
	t := p.take()
	if t == nil {
		return nil
	}
	return &Statement{Span: t.Span, Kind: StatementKind{Direction: &Direction{Span: t.Span, Value: directionKind(t.Kind)}}}
}

func (p *parser) statementKind(depth int) (StatementKind, bool) {
	switch p.kind() {
	case "flow", "global", "connector":
		return kindValue(p.container(depth))
	case "STYLE", "CLASSDEF", "CLASS":
		return kindValue(p.styleStatement())
	case "LINKSTYLE":
		result := p.linkStyle()
		return StatementKind{LinkStyle: result}, result != nil
	case "CLICK":
		result := p.click()
		return StatementKind{Click: result}, result != nil
	}
	if !idKind(p.kind()) {
		p.unknown()
		return StatementKind{}, false
	}
	result := p.vertexStatement()
	return StatementKind{Vertex: result}, result != nil
}

func kindValue(result *StatementKind) (StatementKind, bool) {
	if result == nil {
		return StatementKind{}, false
	}
	return *result, true
}

func (p *parser) endOfStatement() bool {
	p.spaces()
	if boundary(p.kind()) {
		return true
	}
	p.unexpected("COMMENT, EOF, NEWLINE, SEMI")
	return false
}

func (p *parser) unknown() {
	if p.kind() == "UNTERMINATED" {
		p.unexpected("")
		return
	}
	t := p.take()
	if t == nil {
		return
	}
	p.recover()
	p.diagnostics = append(p.diagnostics, diagnostic("agentflow/unknown-statement", "unknown statement "+t.Text, source.Span{Start: t.Span.Start, End: p.end()}))
}

func (p *parser) accessibility() *Statement {
	t := p.take()
	if t == nil {
		return nil
	}
	title := t.Kind == "acc_title"
	var value *Token
	switch t.Kind {
	case "acc_title":
		value = p.require("acc_title_value")
	case "acc_descr":
		value = p.require("acc_descr_value")
	default:
		value = t
	}
	if value == nil {
		return nil
	}
	return &Statement{Span: p.span(t.Span.Start), Kind: StatementKind{Access: &Accessibility{Title: title, Value: *value}}}
}

func (p *parser) container(depth int) *StatementKind {
	open := p.take()
	if open == nil {
		return nil
	}
	if open.Kind == "global" {
		return p.global(*open, depth)
	}
	name := p.containerName()
	if open.Kind == "connector" && name == nil {
		p.unexpected("MD_STR, NODE_STRING, STR")
		return nil
	}
	title, ok := p.containerTitle()
	if !ok {
		return nil
	}
	metadata, ok := p.metadata()
	if !ok {
		return nil
	}
	if !p.endOfStatement() {
		return nil
	}
	if open.Kind == "connector" {
		return &StatementKind{Connector: &ConnectorStatement{Name: *name, Title: title, Metadata: metadata}}
	}
	body, close, ok := p.block(open, depth)
	if !ok {
		return nil
	}
	return &StatementKind{Flow: &FlowStatement{Name: name, Title: title, Metadata: metadata, Opening: open.Span, Body: body, Close: close}}
}

func (p *parser) containerTitle() (*Text, bool) {
	if p.kind() != "SQS" {
		return nil, true
	}
	text, _, _ := p.bracketText()
	return text, text != nil
}

func (p *parser) containerName() *TextNoTags {
	if p.spaces() == 0 {
		return nil
	}
	start := p.position()
	var pieces []Token
	for noTagsKind(p.kind()) {
		if t := p.take(); t != nil {
			pieces = append(pieces, *t)
		} else {
			return nil
		}
	}
	for len(pieces) > 0 && pieces[len(pieces)-1].Kind == "SPACE" {
		pieces = pieces[:len(pieces)-1]
	}
	if len(pieces) == 0 {
		return nil
	}
	first := pieces[0]
	end := start
	if len(pieces) > 0 {
		end = pieces[len(pieces)-1].Span.End
	}
	return &TextNoTags{Span: source.Span{Start: start, End: end}, Pieces: pieces, Kind: textKind(first.Kind)}
}

func (p *parser) global(open Token, depth int) *StatementKind {
	if !p.endOfStatement() {
		return nil
	}
	body, close, ok := p.block(&open, depth)
	if !ok {
		return nil
	}
	return &StatementKind{Global: &GlobalStatement{Opening: open.Span, Body: body, Close: close}}
}

func (p *parser) block(open *Token, depth int) (Document, source.Span, bool) {
	if depth >= 64 {
		p.diagnostics = append(p.diagnostics, diagnostic("limit/nesting-depth", "nesting depth exceeds 64", open.Span))
		p.at = len(p.tokens)
		return Document{}, source.Span{}, false
	}
	if p.kind() != "EOF" {
		p.at++
	}
	body := p.document(depth + 1)
	if p.kind() != "end" {
		lastCode := ""
		if len(p.diagnostics) > 0 {
			lastCode = p.diagnostics[len(p.diagnostics)-1].Code
		}
		if lastCode != "limit/nesting-depth" && lastCode != "agentflow/unterminated" {
			p.unterminated(open.Span)
		}
		return Document{}, source.Span{}, false
	}
	t := p.take()
	if t == nil {
		return Document{}, source.Span{}, false
	}
	return body, t.Span, true
}

func boundary(kind string) bool {
	switch kind {
	case "NEWLINE", "SEMI", "COMMENT", "EOF":
		return true
	}
	return false
}

func idKind(kind string) bool {
	switch kind {
	case "NUM", "NODE_STRING", "DOWN", "MINUS", "DEFAULT", "COMMA", "COLON", "AMP", "BRKT", "MULT", "UNICODE_TEXT":
		return true
	}
	return false
}

func alphaKind(kind string) bool {
	if kind == "DIR" {
		return true
	}
	return idKind(kind) && kind != "DEFAULT"
}

func noTagsKind(kind string) bool {
	switch kind {
	case "NUM", "NODE_STRING", "SPACE", "MINUS", "AMP", "UNICODE_TEXT", "COLON", "MULT", "BRKT",
		"STYLE", "LINKSTYLE", "CLASSDEF", "CLASS", "CLICK", "GRAPH", "DIR",
		"flow", "connector", "global", "end", "DOWN", "UP", "START_LINK", "STR", "MD_STR":
		return true
	}
	return false
}

func textKind(kind string) TextKind {
	switch kind {
	case "STR":
		return TextString
	case "MD_STR":
		return TextMarkdown
	default:
		return TextPlain
	}
}

func normalized(value string) string {
	switch value {
	case "LR", ">":
		return "LR"
	case "RL", "<":
		return "RL"
	case "BT", "^":
		return "BT"
	default:
		return "TB"
	}
}

func directionKind(kind string) string {
	switch kind {
	case "direction_bt":
		return "BT"
	case "direction_rl":
		return "RL"
	case "direction_lr":
		return "LR"
	default:
		return "TB"
	}
}
