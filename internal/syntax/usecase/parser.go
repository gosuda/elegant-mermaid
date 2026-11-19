package usecase

import (
	"fmt"
	"slices"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type parser struct {
	src      string
	cleaned  *source.Cleaned
	tokens   []Token
	at       int
	diags    []diag.Diagnostic
	openings []Token
}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	cleaned := source.Clean(src, removed)
	p := &parser{src: text, cleaned: cleaned, tokens: lex(cleaned)}
	header, lineEnd := p.documentHeader()
	var lines []Line
	for p.kind() != "EOF" {
		if line, ok := p.line(); ok {
			lines = append(lines, line)
		}
	}
	diag.Sort(p.diags)
	return &Start{Span: source.Span{Start: header.Span.Start, End: len(text)}, Header: header, LineEnd: lineEnd, Tokens: p.tokens, Lines: lines}, p.diags
}

func (p *parser) documentHeader() (Token, LineEnd) {
	for k := p.kind(); k == "NEWLINE" || k == "COMMENT"; k = p.kind() {
		p.at++
	}
	header, ok := p.expect("USECASE")
	if !ok {
		header = Token{Kind: "USECASE"}
	}
	lineEnd, ok := p.lineEnd()
	if !ok {
		lineEnd = LineEnd{Span: p.here()}
	}
	return header, lineEnd
}

func (p *parser) kind() string {
	if t := p.peek(0); t != nil {
		return t.Kind
	}
	return "EOF"
}

func (p *parser) peek(n int) *Token {
	if i := p.at + n; i < len(p.tokens) {
		return &p.tokens[i]
	}
	return nil
}

func (p *parser) take() (Token, bool) {
	t := p.peek(0)
	if t == nil {
		return Token{}, false
	}
	p.at++
	return *t, true
}

func (p *parser) end() int {
	if i := max(p.at-1, 0); i < len(p.tokens) {
		return p.tokens[i].Span.End
	}
	return 0
}

func (p *parser) span(start int) source.Span { return source.Span{Start: start, End: p.end()} }

func (p *parser) here() source.Span {
	if t := p.peek(0); t != nil {
		return t.Span
	}
	return source.Span{Start: len(p.src), End: len(p.src)}
}

func (p *parser) text(span source.Span) string { return string(p.cleaned.Slice(span)) }

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: helpFor(code)})
}

func helpFor(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take()
	}
	p.unexpected(kind)
	return Token{}, false
}

func (p *parser) oneOf(kinds ...string) (Token, bool) {
	if slices.Contains(kinds, p.kind()) {
		return p.take()
	}
	p.unexpected(kinds...)
	return Token{}, false
}

func (p *parser) unexpected(kinds ...string) {
	if p.unclosedAtEOF() || p.kind() == "EOF" && len(p.openings) > 0 {
		p.unfinished()
		return
	}
	expected := slices.Compact(slices.Sorted(slices.Values(kinds)))
	span := p.here()
	p.issue("usecase/unexpected-token", fmt.Sprintf("unexpected %s, expected one of: %s", p.text(span), strings.Join(expected, ", ")), span)
}

func (p *parser) unfinished() {
	opening, ok := p.unfinishedOpening()
	if !ok {
		return
	}
	if n := len(p.diags); n > 0 && p.diags[n-1].Code == "usecase/unterminated" {
		return
	}
	p.issue("usecase/unterminated", "unterminated "+opening.Text, source.Span{Start: opening.Span.Start, End: len(p.src)})
	p.at = len(p.tokens)
}

func (p *parser) unfinishedOpening() (Token, bool) {
	if t := p.peek(0); t != nil && strings.HasPrefix(t.Kind, "UNCLOSED_") && t.Kind != "UNCLOSED_STEREOTYPE_TEXT" {
		return *t, true
	}
	if n := len(p.openings); n > 0 {
		return p.openings[n-1], true
	}
	if t := p.peek(0); t != nil {
		return *t, true
	}
	return Token{}, false
}

func (p *parser) unclosedAtEOF() bool {
	t := p.peek(0)
	if t == nil || t.Kind == "UNCLOSED_STEREOTYPE_TEXT" && strings.Contains(t.Text, ">>") {
		return false
	}
	return strings.HasPrefix(t.Kind, "UNCLOSED_") && p.cleaned.Index(t.Span.End) == len(p.cleaned.Text)
}

func (p *parser) lineEnd() (LineEnd, bool) {
	span := p.here()
	if p.kind() == "EOF" {
		return LineEnd{Span: span}, true
	}
	token, ok := p.expect("NEWLINE")
	if !ok {
		return LineEnd{}, false
	}
	return LineEnd{Span: span, Token: &token}, true
}

func (p *parser) line() (Line, bool) {
	if line, ok := p.spacing(); ok {
		return line, true
	}
	before, errors, open := p.at, len(p.diags), len(p.openings)
	line, ok := p.statementLine()
	if !ok {
		p.recover()
		p.coalesceUnfinished(errors)
	}
	p.truncateOpenings(open)
	if p.at == before {
		p.at++
	}
	return line, ok
}

func (p *parser) statementLine() (Line, bool) {
	start := p.here().Start
	statement, ok := p.statement()
	if !ok {
		return Line{}, false
	}
	statement.Span = p.span(start)
	lineEnd, ok := p.lineEnd()
	if !ok {
		return Line{}, false
	}
	statement.LineEnd = lineEnd
	return Line{Span: statement.Span, Statement: &statement}, true
}

func (p *parser) coalesceUnfinished(errors int) {
	n := len(p.diags)
	if n == 0 || p.diags[n-1].Code != "usecase/unterminated" || n <= errors+1 {
		return
	}
	last := p.diags[n-1]
	p.diags = append(p.diags[:errors], last)
}

func (p *parser) popOpening() {
	if n := len(p.openings); n > 0 {
		p.openings = p.openings[:n-1]
	}
}

func (p *parser) truncateOpenings(n int) {
	if len(p.openings) > n {
		p.openings = p.openings[:n]
	}
}

func (p *parser) recover() {
	depth := 0
	for _, t := range p.openings {
		if t.Kind == "METADATA_START" {
			depth++
		}
	}
	for k := p.kind(); k != "EOF" && k != "END"; k = p.kind() {
		if k == "NEWLINE" && depth == 0 {
			break
		}
		if p.unclosedAtEOF() {
			p.unfinished()
			return
		}
		p.recoverDelimiter(&depth)
		p.at++
	}
	if p.kind() == "EOF" && len(p.openings) > 0 {
		p.unfinished()
	}
}

func (p *parser) recoverDelimiter(depth *int) {
	switch p.kind() {
	case "METADATA_START", "LBRACE":
		*depth++
	case "RBRACE":
		*depth = max(*depth-1, 0)
		if *depth == 0 {
			p.closeRecovered("METADATA_START")
		}
	case "RPAREN":
		p.closeRecovered("LPAREN")
	case "RBRACKET":
		p.closeRecovered("LBRACKET")
	case "UNCLOSED_STEREOTYPE_TEXT":
		p.closeRecovered("STEREOTYPE_START")
	}
}

func (p *parser) closeRecovered(kind string) {
	if n := len(p.openings); n > 0 && p.openings[n-1].Kind == kind {
		p.openings = p.openings[:n-1]
	}
}

func (p *parser) spacing() (Line, bool) {
	switch p.kind() {
	case "NEWLINE":
		token, _ := p.take()
		return Line{Span: token.Span, Blank: &BlankLine{Span: token.Span, Token: token}}, true
	case "COMMENT":
		token, _ := p.take()
		lineEnd, ok := p.lineEnd()
		if !ok {
			return Line{}, false
		}
		return Line{Span: token.Span, Comment: &CommentLine{Span: token.Span, Token: token, LineEnd: lineEnd}}, true
	}
	return Line{}, false
}

func (p *parser) baseName(delimiters ...string) (ActorName, bool) {
	id, ok := p.oneOf("IDENTIFIER", "PLAIN_STRING", "MARKDOWN_STRING")
	if !ok {
		return ActorName{}, false
	}
	name := ActorName{ID: id, IDContentSpan: contentSpan(id)}
	if id.Kind == "IDENTIFIER" && slices.Contains(delimiters, p.kind()) {
		pair, label, ok := p.delimitedLabel()
		if !ok {
			return ActorName{}, false
		}
		name.Label, name.Delimiters = label, pair
	}
	name.Span = p.span(id.Span.Start)
	return name, true
}

func (p *parser) delimitedLabel() (*Delimiters, *NodeLabel, bool) {
	open, _ := p.take()
	p.openings = append(p.openings, open)
	label, ok := p.label()
	if !ok {
		return nil, nil, false
	}
	closeKind := "RBRACKET"
	if open.Kind == "LPAREN" {
		closeKind = "RPAREN"
	}
	closing, ok := p.expect(closeKind)
	if !ok {
		return nil, nil, false
	}
	p.popOpening()
	return &Delimiters{Open: open, Close: closing}, &label, true
}

func (p *parser) label() (NodeLabel, bool) {
	first := p.peek(0)
	if first == nil {
		p.unexpected("LABEL_TEXT", "MARKDOWN_STRING", "PLAIN_STRING")
		return NodeLabel{}, false
	}
	head := *first
	var tokens []Token
	if head.Kind == "PLAIN_STRING" || head.Kind == "MARKDOWN_STRING" {
		token, _ := p.take()
		tokens = append(tokens, token)
	} else {
		for isLabel(p.kind()) {
			token, _ := p.take()
			tokens = append(tokens, token)
		}
	}
	if len(tokens) == 0 {
		p.unexpected("LABEL_TEXT", "MARKDOWN_STRING", "PLAIN_STRING")
		return NodeLabel{}, false
	}
	return p.nodeLabel(head, tokens, p.span(head.Span.Start)), true
}

func (p *parser) nodeLabel(first Token, tokens []Token, span source.Span) NodeLabel {
	content := span
	if len(tokens) == 1 {
		content = contentSpan(first)
	}
	kind := LabelPlain
	switch first.Kind {
	case "MARKDOWN_STRING":
		kind = LabelMarkdown
	case "PLAIN_STRING":
		kind = LabelQuoted
	}
	return NodeLabel{Span: span, Text: p.text(content), ContentSpan: content, Kind: kind, Tokens: tokens}
}

func (p *parser) actorItem() (ActorItem, bool) {
	name, ok := p.baseName("LPAREN")
	if !ok {
		return ActorItem{}, false
	}
	item := ActorItem{Name: name}
	if p.kind() == "METADATA_START" {
		metadata, ok := p.metadata()
		if !ok {
			return ActorItem{}, false
		}
		item.Metadata = &metadata
	}
	if item.Stereotype, ok = p.optionalStereotype(); !ok {
		return ActorItem{}, false
	}
	if item.Classes, ok = p.optionalClasses(); !ok {
		return ActorItem{}, false
	}
	item.Span = p.span(name.Span.Start)
	return item, true
}

func (p *parser) entity() (EntityName, bool) {
	base, ok := p.baseName("LPAREN", "LBRACKET")
	if !ok {
		return EntityName{}, false
	}
	name := EntityName{ID: base.ID, IDContentSpan: base.IDContentSpan, Label: base.Label, Delimiters: base.Delimiters}
	if p.kind() == "METADATA_START" {
		metadata, ok := p.metadata()
		if !ok {
			return EntityName{}, false
		}
		name.Metadata = &UseCaseMetadata{Span: metadata.Span, Metadata: metadata}
	}
	if name.Stereotype, ok = p.optionalStereotype(); !ok {
		return EntityName{}, false
	}
	if name.Classes, ok = p.optionalClasses(); !ok {
		return EntityName{}, false
	}
	name.Span = p.span(base.Span.Start)
	return name, true
}

func (p *parser) optionalStereotype() (*Stereotype, bool) {
	if p.kind() != "STEREOTYPE_START" {
		return nil, true
	}
	open, _ := p.take()
	p.openings = append(p.openings, open)
	content, ok := p.expect("STEREOTYPE_TEXT")
	if !ok {
		return nil, false
	}
	start := p.cleaned.Index(content.Span.Start) + len(content.Text) - len(strings.TrimLeftFunc(content.Text, unicode.IsSpace))
	contentSpan := p.cleaned.Span(start, start+len(strings.TrimSpace(content.Text)))
	closing, ok := p.expect("STEREOTYPE_END")
	if !ok {
		return nil, false
	}
	p.popOpening()
	return &Stereotype{Span: p.span(open.Span.Start), Open: open, Content: content, ContentSpan: contentSpan, Close: closing}, true
}

func (p *parser) optionalClasses() (*ClassSuffix, bool) {
	if p.kind() != "CLASS_SEPARATOR" {
		return nil, true
	}
	separator, _ := p.take()
	classes, ok := p.identifiers()
	if !ok {
		return nil, false
	}
	return &ClassSuffix{Span: p.span(separator.Span.Start), Separator: separator, Classes: classes}, true
}

func (p *parser) identifiers() ([]Token, bool) {
	id, ok := p.expect("IDENTIFIER")
	if !ok {
		return nil, false
	}
	ids := []Token{id}
	for p.kind() == "COMMA" {
		p.at++
		if id, ok = p.expect("IDENTIFIER"); !ok {
			return nil, false
		}
		ids = append(ids, id)
	}
	return ids, true
}

func (p *parser) metadata() (Metadata, bool) {
	open, ok := p.expect("METADATA_START")
	if !ok {
		return Metadata{}, false
	}
	p.openings = append(p.openings, open)
	p.skipNewlines()
	metadata := Metadata{Open: open}
	for k := p.kind(); k != "RBRACE" && k != "EOF"; k = p.kind() {
		property, ok := p.metadataProperty()
		if !ok {
			return Metadata{}, false
		}
		metadata.Properties = append(metadata.Properties, property)
		if p.kind() == "RBRACE" {
			break
		}
		separator, ok := p.metadataSeparator()
		if !ok {
			return Metadata{}, false
		}
		metadata.Separators = append(metadata.Separators, separator)
	}
	if metadata.Close, ok = p.expect("RBRACE"); !ok {
		return Metadata{}, false
	}
	p.popOpening()
	metadata.Span = p.span(open.Span.Start)
	return metadata, true
}

func (p *parser) skipNewlines() {
	for p.kind() == "NEWLINE" {
		p.at++
	}
}

func (p *parser) metadataProperty() (MetadataProperty, bool) {
	key, ok := p.oneOf("IDENTIFIER", "PLAIN_STRING")
	if !ok {
		return MetadataProperty{}, false
	}
	if _, ok = p.expect("COLON"); !ok {
		return MetadataProperty{}, false
	}
	value, ok := p.oneOf("IDENTIFIER", "PLAIN_STRING", "TRUE", "FALSE")
	if !ok {
		return MetadataProperty{}, false
	}
	return MetadataProperty{Span: p.span(key.Span.Start), Key: key, Value: value, KeyContentSpan: contentSpan(key), ValueContentSpan: contentSpan(value)}, true
}

func (p *parser) metadataSeparator() (MetadataSeparator, bool) {
	start := p.here().Start
	var tokens []Token
	take := func(kind string) {
		for p.kind() == kind {
			token, _ := p.take()
			tokens = append(tokens, token)
			if kind == "COMMA" {
				return
			}
		}
	}
	take("COMMA")
	take("NEWLINE")
	if len(tokens) > 0 && tokens[0].Kind == "NEWLINE" {
		take("COMMA")
	}
	take("NEWLINE")
	if len(tokens) == 0 {
		p.unexpected("COMMA", "NEWLINE", "RBRACE")
		return MetadataSeparator{}, false
	}
	return MetadataSeparator{Span: p.span(start), Tokens: tokens}, true
}

func contentSpan(t Token) source.Span {
	n := 0
	switch t.Kind {
	case "PLAIN_STRING":
		n = 1
	case "MARKDOWN_STRING":
		n = 2
	}
	return source.Span{Start: t.Span.Start + n, End: max(t.Span.End-n, 0)}
}
