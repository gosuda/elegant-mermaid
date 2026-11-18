package eventmodeling

import (
	"slices"
	"sort"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "eventmodeling/unexpected-token"
	codeUnknown      = "eventmodeling/unknown-statement"
	codeUnterminated = "eventmodeling/unterminated"
	tickKind         = "`"
)

var (
	entityTypes = []string{"cmd", "command", "evt", "event", "pcr", "processor", "readmodel", "rmo", "ui"}
	dataTypes   = []string{"figma", "html", "jsobj", "json", "md", "salt", "text", "uri"}
	openers     = []string{"tf", "timeframe", "rf", "resetframe", "entity", "data", "note", "gwt"}
)

func Parse(src []byte, removed []source.Span) (*EventModel, []diag.Diagnostic) {
	text := string(src)
	tokens, breaks := lex(text, removed)
	p := &parser{src: text, tokens: tokens, breaks: breaks}
	model := &EventModel{}
	model.Header = p.header()
	p.statements(model)
	model.Span = source.Span{Start: model.Header.Span.Start, End: len(text)}
	return model, p.diags
}

type parser struct {
	src    string
	tokens []Token
	breaks []int
	at     int
	diags  []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: kindEOF, Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string { return p.token().Kind }

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
	t := p.token()
	if t.Kind == kindUnclosed {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.src[t.Span.Start:t.Span.End]+", expected one of: "+strings.Join(names, ", "), t.Span)
}

func (p *parser) unclosed(opener Token) {
	p.issue(codeUnterminated, "unterminated "+opener.Text, source.Span{Start: opener.Span.Start, End: len(p.src)})
}

func (p *parser) insideFailure(opener Token, expected ...string) {
	if p.kind() == kindEOF {
		p.unclosed(opener)
		return
	}
	p.unexpected(expected...)
}

func (p *parser) lineEnd(from int) int {
	i := sort.SearchInts(p.breaks, from)
	if i < len(p.breaks) {
		return p.breaks[i]
	}
	return len(p.src)
}

func (p *parser) recover() {
	p.recoverTo(p.lineEnd(p.token().Span.Start))
}

func (p *parser) recoverTo(limit int) int {
	for {
		t := p.token()
		switch {
		case t.Kind == kindEOF || t.Kind == kindUnclosed || slices.Contains(openers, t.Kind):
			return min(limit, t.Span.Start)
		case t.Span.Start >= limit:
			return limit
		}
		p.take()
	}
}

func (p *parser) header() Token {
	if p.kind() == headerKind {
		return p.take()
	}
	p.unexpected(headerKind)
	p.recover()
	return Token{}
}

func (p *parser) statements(model *EventModel) {
	for {
		switch p.kind() {
		case kindEOF:
			return
		case kindUnclosed:
			p.unclosed(p.token())
			return
		case "tf", "timeframe":
			p.timeFrame(model)
		case "rf", "resetframe":
			p.resetFrame(model)
		case "entity":
			p.entity(model)
		case "data":
			p.data(model)
		case "note":
			p.note(model)
		case "gwt":
			p.gwt(model)
		default:
			p.unknown()
		}
	}
}

func (p *parser) unknown() {
	first := p.take()
	boundary := p.recoverTo(p.lineEnd(first.Span.Start))
	end := max(boundary, p.lastEnd())
	p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: end})
}

func (p *parser) valueOf(kind string) (Value, bool) {
	if p.kind() != kind {
		p.unexpected(kind)
		return Value{}, false
	}
	t := p.take()
	return Value{Text: t.Text, Span: t.Span}, true
}

func (p *parser) oneOf(kinds []string) (Value, bool) {
	if !slices.Contains(kinds, p.kind()) {
		p.unexpected(kinds...)
		return Value{}, false
	}
	t := p.take()
	return Value{Text: t.Text, Span: t.Span}, true
}

func (p *parser) qualifiedName() (Value, bool) {
	first, ok := p.valueOf(kindID)
	if !ok {
		return Value{}, false
	}
	name := first
	for p.kind() == "." {
		p.take()
		part, ok := p.valueOf(kindID)
		if !ok {
			return Value{}, false
		}
		name = Value{Text: name.Text + "." + part.Text, Span: source.Span{Start: name.Span.Start, End: part.Span.End}}
	}
	return name, true
}

func (p *parser) timeFrame(model *EventModel) {
	if fields, ok := p.frame(); ok {
		model.Frames = append(model.Frames, &EmTimeFrame{fields})
	}
}

func (p *parser) resetFrame(model *EventModel) {
	if fields, ok := p.frame(); ok {
		model.Frames = append(model.Frames, &EmResetFrame{fields})
	}
}

func (p *parser) frame() (FrameFields, bool) {
	keyword := p.take()
	fields := FrameFields{Keyword: keyword.Span}
	if !p.frameHead(&fields) || !p.frameTail(&fields) {
		p.recover()
		return FrameFields{}, false
	}
	fields.Span = source.Span{Start: keyword.Span.Start, End: p.lastEnd()}
	return fields, true
}

func (p *parser) frameHead(fields *FrameFields) bool {
	var ok bool
	if fields.Name, ok = p.valueOf(kindFID); !ok {
		return false
	}
	if fields.ModelEntityType, ok = p.oneOf(entityTypes); !ok {
		return false
	}
	fields.EntityIdentifier, ok = p.qualifiedName()
	return ok
}

func (p *parser) frameTail(fields *FrameFields) bool {
	for p.kind() == "->>" {
		p.take()
		source, ok := p.valueOf(kindFID)
		if !ok {
			return false
		}
		fields.SourceFrames = append(fields.SourceFrames, source)
	}
	if p.kind() == "[[" {
		ref, ok := p.reference()
		if !ok {
			return false
		}
		fields.DataReference = &ref
	}
	if p.kind() != tickKind && p.kind() != kindInline {
		return true
	}
	dataType, payload, ok := p.payload(kindInline)
	fields.DataType, fields.DataInlineValue = dataType, &payload
	return ok
}

func (p *parser) reference() (Value, bool) {
	opener := p.take()
	if p.kind() != kindID {
		p.insideFailure(opener, kindID)
		return Value{}, false
	}
	t := p.take()
	if p.kind() != "]]" {
		p.insideFailure(opener, "]]")
		return Value{}, false
	}
	p.take()
	return Value{Text: t.Text, Span: t.Span}, true
}

func (p *parser) payload(kind string) (*Value, Value, bool) {
	var dataType *Value
	if p.kind() == tickKind {
		opener := p.take()
		if !slices.Contains(dataTypes, p.kind()) {
			p.insideFailure(opener, dataTypes...)
			return nil, Value{}, false
		}
		t := p.take()
		dataType = &Value{Text: t.Text, Span: t.Span}
		if p.kind() != tickKind {
			p.insideFailure(opener, tickKind)
			return nil, Value{}, false
		}
		p.take()
		return p.typed(dataType, kind)
	}
	if p.kind() != kind {
		p.unexpected(tickKind, kind)
		return nil, Value{}, false
	}
	return p.typed(nil, kind)
}

func (p *parser) typed(dataType *Value, kind string) (*Value, Value, bool) {
	if p.kind() != kind {
		p.unexpected(kind)
		return dataType, Value{}, false
	}
	t := p.take()
	return dataType, Value{Text: t.Text, Span: t.Span}, true
}

func (p *parser) entity(model *EventModel) {
	keyword := p.take()
	name, ok := p.qualifiedName()
	if !ok {
		p.recover()
		return
	}
	model.ModelEntities = append(model.ModelEntities, EmModelEntity{Span: source.Span{Start: keyword.Span.Start, End: p.lastEnd()}, Keyword: keyword.Span, Name: name})
}

func (p *parser) data(model *EventModel) {
	keyword := p.take()
	name, ok := p.valueOf(kindID)
	if !ok {
		p.recover()
		return
	}
	dataType, block, ok := p.payload(kindBlock)
	if !ok {
		p.recover()
		return
	}
	model.DataEntities = append(model.DataEntities, EmDataEntity{Span: source.Span{Start: keyword.Span.Start, End: p.lastEnd()}, Keyword: keyword.Span, Name: name, DataType: dataType, DataBlockValue: block})
}

func (p *parser) note(model *EventModel) {
	keyword := p.take()
	frame, ok := p.valueOf(kindFID)
	if !ok {
		p.recover()
		return
	}
	dataType, block, ok := p.payload(kindBlock)
	if !ok {
		p.recover()
		return
	}
	model.NoteEntities = append(model.NoteEntities, EmNoteEntity{Span: source.Span{Start: keyword.Span.Start, End: p.lastEnd()}, Keyword: keyword.Span, SourceFrame: frame, DataType: dataType, DataBlockValue: block})
}

func (p *parser) gwt(model *EventModel) {
	keyword := p.take()
	node := EmGwt{Keyword: keyword.Span}
	if !p.gwtHead(&node) || !p.gwtBody(&node) {
		p.recover()
		return
	}
	node.Span = source.Span{Start: keyword.Span.Start, End: p.lastEnd()}
	model.GwtEntities = append(model.GwtEntities, node)
}

func (p *parser) gwtHead(node *EmGwt) bool {
	var ok bool
	if node.SourceFrame, ok = p.valueOf(kindFID); !ok {
		return false
	}
	if p.kind() != "given" {
		p.unexpected("given")
		return false
	}
	p.take()
	return true
}

func (p *parser) gwtBody(node *EmGwt) bool {
	var ok bool
	if node.GivenStatements, ok = p.gwtStatements(entityTypes); !ok {
		return false
	}
	if p.kind() == "when" {
		p.take()
		if node.WhenStatements, ok = p.gwtStatements(entityTypes); !ok {
			return false
		}
	}
	if p.kind() != "then" {
		next := append(slices.Clone(entityTypes), "then")
		if node.WhenStatements == nil {
			next = append(next, "when")
		}
		p.unexpected(next...)
		return false
	}
	p.take()
	node.ThenStatements, ok = p.gwtStatements(entityTypes)
	return ok
}

func (p *parser) gwtStatements(first []string) ([]EmGwtStatement, bool) {
	var statements []EmGwtStatement
	for len(statements) == 0 || slices.Contains(entityTypes, p.kind()) {
		kind, ok := p.oneOf(first)
		if !ok {
			return nil, false
		}
		identifier, ok := p.valueOf(kindID)
		if !ok {
			return nil, false
		}
		statements = append(statements, EmGwtStatement{Span: source.Span{Start: kind.Span.Start, End: identifier.Span.End}, ModelEntityType: kind, EntityIdentifier: identifier})
	}
	return statements, true
}
