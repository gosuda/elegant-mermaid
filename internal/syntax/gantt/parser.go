package gantt

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "gantt/unexpected-token"
	codeUnknown      = "gantt/unknown-statement"
	codeUnterminated = "gantt/unterminated"
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, scan: newScanner(text, removed)}
	p.advance()
	return p.start(), p.diags
}

type parser struct {
	src   string
	scan  *scanner
	tok   Token
	diags []diag.Diagnostic
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	d := diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span}
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code != code {
			continue
		}
		d.Help = gen.Diagnostics[i].Help
		switch gen.Diagnostics[i].Severity {
		case "warning":
			d.Severity = diag.SeverityWarning
		case "info":
			d.Severity = diag.SeverityInfo
		}
	}
	return d
}

func (p *parser) advance() { p.tok = p.scan.next() }

func (p *parser) take() Token {
	t := p.tok
	p.advance()
	return t
}

func (p *parser) describe(t Token) string {
	if t.Span.Start == t.Span.End {
		return "end of input"
	}
	return p.src[t.Span.Start:t.Span.End]
}

func (p *parser) unexpected(expected []string) {
	if p.tok.Kind == kindOpen {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	message := "unexpected " + p.describe(p.tok) + ", expected one of: " + strings.Join(names, ", ")
	p.diags = append(p.diags, Diagnostic(codeUnexpected, message, p.tok.Span))
}

func (p *parser) discard() {
	switch p.tok.Kind {
	case KindNewline, KindEOF, kindOpen:
		return
	}
	p.scan.skipLine(p.tok.Span.End)
	p.advance()
}

func (p *parser) start() *Start {
	for p.tok.Kind == KindNewline {
		p.advance()
	}
	if p.tok.Kind != KindGantt {
		p.unexpected([]string{KindGantt})
		return &Start{Span: source.Span{Start: p.tok.Span.Start, End: len(p.src)}}
	}
	header := p.take()
	document := p.document()
	return &Start{Span: source.Span{Start: header.Span.Start, End: max(document.Span.End, header.Span.End)}, Header: header, Document: document}
}

func (p *parser) document() Document {
	doc := Document{Span: source.Span{Start: p.tok.Span.Start, End: p.tok.Span.Start}}
	for p.tok.Kind != KindEOF {
		if line, ok := p.line(); ok {
			doc.Lines = append(doc.Lines, line)
			doc.Span.End = max(doc.Span.End, line.Span.End)
		}
	}
	return doc
}

func (p *parser) line() (Line, bool) {
	switch p.tok.Kind {
	case KindNewline:
		separator := p.take()
		return Line{Span: separator.Span, Separator: &separator}, true
	case kindOpen:
		t := p.take()
		p.diags = append(p.diags, Diagnostic(codeUnterminated, "unterminated "+t.Text, t.Span))
		return Line{}, false
	}
	statement, ok := p.statement()
	if !ok {
		return Line{}, false
	}
	return Line{Span: statement.Span, Statement: &statement}, true
}

func (p *parser) simple(build func(Token) StatementKind) (Statement, bool) {
	t := p.take()
	return Statement{Span: t.Span, Kind: build(t)}, true
}

func (p *parser) statement() (Statement, bool) {
	kind := p.tok.Kind
	switch {
	case strings.HasPrefix(kind, KindWeekdayPrefix):
		return p.simple(func(t Token) StatementKind {
			return &Weekday{Token: t, Name: strings.TrimPrefix(kind, KindWeekdayPrefix)}
		})
	case strings.HasPrefix(kind, KindWeekendPrefix):
		return p.simple(func(t Token) StatementKind {
			return &Weekend{Token: t, Name: strings.TrimPrefix(kind, KindWeekendPrefix)}
		})
	}
	if build, ok := simpleStatements[kind]; ok {
		return p.simple(build)
	}
	switch kind {
	case KindAccBlockValue:
		v := p.take()
		return Statement{Span: source.Span{Start: v.Open.Start, End: v.Close.End}, Kind: &AccDescrBlock{Value: v}}, true
	case KindAccTitle:
		return p.accessibility(KindAccTitleValue, func(o, v Token) StatementKind { return &AccTitle{Opener: o, Value: v} })
	case KindAccDescr:
		return p.accessibility(KindAccDescrValue, func(o, v Token) StatementKind { return &AccDescr{Opener: o, Value: v} })
	case KindClick:
		return p.click()
	case KindTaskText:
		return p.task()
	}
	p.unknown()
	return Statement{}, false
}

var simpleStatements = map[string]func(Token) StatementKind{
	KindDateFormat:        func(t Token) StatementKind { return &DateFormat{Token: t} },
	KindInclusiveEndDates: func(t Token) StatementKind { return &InclusiveEndDates{Token: t} },
	KindTopAxis:           func(t Token) StatementKind { return &TopAxis{Token: t} },
	KindAxisFormat:        func(t Token) StatementKind { return &AxisFormat{Token: t} },
	KindTickInterval:      func(t Token) StatementKind { return &TickInterval{Token: t} },
	KindExcludes:          func(t Token) StatementKind { return &Excludes{Token: t} },
	KindIncludes:          func(t Token) StatementKind { return &Includes{Token: t} },
	KindTodayMarker:       func(t Token) StatementKind { return &TodayMarker{Token: t} },
	KindTitle:             func(t Token) StatementKind { return &Title{Token: t} },
	KindSection:           func(t Token) StatementKind { return &Section{Token: t} },
}

func (p *parser) accessibility(value string, build func(opener, value Token) StatementKind) (Statement, bool) {
	opener := p.take()
	if p.tok.Kind != value {
		p.unexpected([]string{value})
		p.discard()
		return Statement{}, false
	}
	v := p.take()
	return Statement{Span: source.Span{Start: opener.Span.Start, End: max(opener.Span.End, v.Span.End)}, Kind: build(opener, v)}, true
}

func (p *parser) task() (Statement, bool) {
	text := p.take()
	if p.tok.Kind != KindTaskData {
		p.unexpected([]string{KindTaskData})
		p.discard()
		return Statement{}, false
	}
	data := p.take()
	return Statement{Span: source.Span{Start: text.Span.Start, End: data.Span.End}, Kind: &Task{Text: text, Data: data}}, true
}

func (p *parser) click() (Statement, bool) {
	c := &ClickStatement{Click: p.take()}
	end := c.Click.Span.End
	grab := func(kind string) *Token {
		if p.tok.Kind != kind {
			return nil
		}
		t := p.take()
		c.Order = append(c.Order, kind)
		end = max(end, t.Span.End)
		return &t
	}
	switch p.tok.Kind {
	case KindCallbackName:
		c.Callback = grab(KindCallbackName)
		c.Args = grab(KindCallbackArgs)
		c.Href = grab(KindHref)
	case KindHref:
		c.Href = grab(KindHref)
		if c.Callback = grab(KindCallbackName); c.Callback != nil {
			c.Args = grab(KindCallbackArgs)
		}
	default:
		p.unexpected([]string{KindCallbackName, KindHref})
		p.discard()
		return Statement{}, false
	}
	return Statement{Span: source.Span{Start: c.Click.Span.Start, End: end}, Kind: c}, true
}

func (p *parser) unknown() {
	first := p.tok
	end := p.scan.skipLine(first.Span.End)
	p.advance()
	p.diags = append(p.diags, Diagnostic(codeUnknown, "unknown statement "+p.describe(first), source.Span{Start: first.Span.Start, End: end}))
}
