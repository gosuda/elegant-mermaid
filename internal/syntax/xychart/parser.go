package xychart

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "xychart/unexpected-token"
	codeUnknown      = "xychart/unknown-statement"
	codeUnterminated = "xychart/unterminated"
)

var textStarts = []string{"ALPHA", "AMP", "BRKT", "DOT", "EQUALS", "MD_STR", "MINUS", "MULT", "NUM", "PLUS", "STR", "UNDERSCORE"}

var alphaNumTokens = []string{"AMP", "NUM", "ALPHA", "PLUS", "EQUALS", "MULT", "DOT", "BRKT", "MINUS", "UNDERSCORE"}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	start := p.start()
	return start, p.diags
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

func (p *parser) raw(span source.Span) string { return sub(p.src, span.Start, span.End) }

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
	return strings.ContainsAny(sub(p.src, min(from, to), to), "\n\r")
}

func (p *parser) boundary(prevEnd int) bool {
	t := p.token()
	switch t.Kind {
	case "NEWLINE", "SEMI", "EOF", "UNTERMINATED":
		return true
	}
	return p.lineBreakBetween(prevEnd, t.Span.Start)
}

func (p *parser) recover(prevEnd int) {
	for !p.boundary(prevEnd) {
		prevEnd = p.take().Span.End
	}
}

func (p *parser) start() *Start {
	first := p.token().Span.Start
	var headers []Header
	for {
		switch p.kind() {
		case "NEWLINE", "SEMI":
			p.take()
			continue
		case "XYCHART":
			headers = append(headers, p.header())
			continue
		}
		break
	}
	document := p.document()
	return &Start{Span: source.Span{Start: first, End: len(p.src)}, Headers: headers, Document: document}
}

func (p *parser) header() Header {
	keyword := p.take()
	h := Header{Span: keyword.Span, Keyword: keyword}
	if p.kind() == "CHART_ORIENTATION" {
		orientation := p.take()
		h.Orientation = &orientation
		h.Span.End = orientation.Span.End
	}
	return h
}

func (p *parser) document() Document {
	start := p.token().Span.Start
	var statements []Statement
	for {
		switch p.kind() {
		case "EOF":
			return Document{Span: source.Span{Start: start, End: documentEnd(statements, start)}, Statements: statements}
		case "UNTERMINATED":
			p.unterminated(p.token())
			continue
		case "NEWLINE", "SEMI":
			p.take()
			continue
		}
		before := p.at
		if kind := p.statement(); kind != nil {
			statements = append(statements, Statement{Span: statementSpan(kind), Kind: kind})
		} else if p.at == before {
			p.unknownStatement()
		}
	}
}

func documentEnd(statements []Statement, start int) int {
	end := start
	for _, s := range statements {
		end = max(end, s.Span.End)
	}
	return end
}

func statementSpan(kind StatementKind) source.Span {
	switch k := kind.(type) {
	case *Title:
		return k.Span
	case *AxisStatement:
		return k.Span
	case *PlotStatement:
		return k.Span
	case *Accessibility:
		return k.Span
	}
	return source.Span{}
}

func (p *parser) unknownStatement() {
	first := p.take()
	end := first.Span.End
	for !p.boundary(end) {
		end = p.take().Span.End
	}
	p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: end})
}

func (p *parser) statement() StatementKind {
	switch p.kind() {
	case "title":
		return nonNil(p.title())
	case "X_AXIS", "Y_AXIS":
		return nonNil(p.axis())
	case "LINE", "BAR":
		return nonNil(p.plot())
	case "acc_title", "acc_descr":
		return nonNil(p.accessibility())
	case "acc_descr_multiline_value":
		value := p.take()
		return &Accessibility{Span: value.Span, Multiline: true, Value: value}
	}
	return nil
}

func nonNil[P interface {
	StatementKind
	comparable
}](node P) StatementKind {
	var zero P
	if node == zero {
		return nil
	}
	return node
}

func (p *parser) accessibility() *Accessibility {
	keyword := p.take()
	if p.kind() != keyword.Kind+"_value" {
		p.unexpected(keyword.Kind + "_value")
		return nil
	}
	value := p.take()
	return &Accessibility{Span: source.Span{Start: keyword.Span.Start, End: value.Span.End}, Title: keyword.Kind == "acc_title", Value: value}
}

func (p *parser) title() *Title {
	keyword := p.take()
	text, ok := p.text(textStarts)
	if !ok {
		return nil
	}
	return &Title{Span: source.Span{Start: keyword.Span.Start, End: text.Span.End}, Text: text}
}

func (p *parser) text(expected []string) (Text, bool) {
	switch p.kind() {
	case "STR", "MD_STR":
		token := p.take()
		return Text{Span: token.Span, Value: token.Text, Markdown: token.Kind == "MD_STR"}, true
	}
	if !slices.Contains(alphaNumTokens, p.kind()) {
		p.unexpected(expected...)
		return Text{}, false
	}
	first := p.token()
	var value strings.Builder
	end := first.Span.End
	for slices.Contains(alphaNumTokens, p.kind()) {
		token := p.take()
		value.WriteString(token.Text)
		end = token.Span.End
	}
	return Text{Span: source.Span{Start: first.Span.Start, End: end}, Value: value.String()}, true
}

func (p *parser) startsText() bool {
	return slices.Contains(textStarts, p.kind())
}

func (p *parser) axis() *AxisStatement {
	keyword := p.take()
	axis := &AxisStatement{Y: keyword.Kind == "Y_AXIS", Span: keyword.Span}
	if !p.axisStarts(axis) {
		p.unexpected(axisExpected(axis)...)
		return nil
	}
	if p.startsText() && !p.axisTitle(axis) {
		return nil
	}
	if !p.axisData(axis) {
		return nil
	}
	return axis
}

func axisExpected(axis *AxisStatement) []string {
	expected := append([]string{"NUMBER_WITH_DECIMAL"}, textStarts...)
	if !axis.Y {
		expected = append(expected, "SQUARE_BRACES_START")
	}
	return expected
}

func (p *parser) axisStarts(axis *AxisStatement) bool {
	return p.startsText() || p.kind() == "NUMBER_WITH_DECIMAL" || (!axis.Y && p.kind() == "SQUARE_BRACES_START")
}

func (p *parser) axisTitle(axis *AxisStatement) bool {
	title, ok := p.text(textStarts)
	if !ok {
		return false
	}
	axis.Title = &title
	axis.Span.End = title.Span.End
	return true
}

func (p *parser) axisData(axis *AxisStatement) bool {
	switch {
	case p.kind() == "NUMBER_WITH_DECIMAL":
		r, ok := p.rangeData()
		if !ok {
			return false
		}
		axis.Range = &r
		axis.Span.End = r.Span.End
	case !axis.Y && p.kind() == "SQUARE_BRACES_START":
		band, ok := p.bandData()
		if !ok {
			return false
		}
		axis.Band = &band
		axis.Span.End = band.Span.End
	}
	return true
}

func (p *parser) number() (Number, bool) {
	if p.kind() != "NUMBER_WITH_DECIMAL" {
		p.unexpected("NUMBER_WITH_DECIMAL")
		return Number{}, false
	}
	token := p.take()
	return Number{Span: token.Span, Text: token.Text}, true
}

func (p *parser) rangeData() (Range, bool) {
	low, ok := p.number()
	if !ok {
		return Range{}, false
	}
	if p.kind() != "ARROW_DELIMITER" {
		p.unexpected("ARROW_DELIMITER")
		return Range{}, false
	}
	p.take()
	high, ok := p.number()
	if !ok {
		return Range{}, false
	}
	return Range{Span: source.Span{Start: low.Span.Start, End: high.Span.End}, Min: low, Max: high}, true
}

func (p *parser) bandData() (BandData, bool) {
	open := p.take()
	band := BandData{Span: open.Span}
	for {
		if p.kind() == "EOF" {
			p.unterminatedList(open)
			return BandData{}, false
		}
		text, ok := p.text(textStarts)
		if !ok {
			return BandData{}, false
		}
		band.Categories = append(band.Categories, text)
		switch p.kind() {
		case "COMMA":
			p.take()
			continue
		case "SQUARE_BRACES_END":
			band.Span.End = p.take().Span.End
			return band, true
		}
		p.unterminatedList(open, "COMMA", "SQUARE_BRACES_END")
		return BandData{}, false
	}
}

func (p *parser) unterminatedList(open Token, expected ...string) {
	if p.kind() == "EOF" {
		p.issue(codeUnterminated, "unterminated "+open.Text, source.Span{Start: open.Span.Start, End: len(p.src)})
		return
	}
	p.unexpected(expected...)
}

func (p *parser) plot() *PlotStatement {
	keyword := p.take()
	plot := &PlotStatement{Line: keyword.Kind == "LINE", Span: keyword.Span}
	if p.startsText() {
		title, ok := p.text(textStarts)
		if !ok {
			return nil
		}
		plot.Title = &title
	}
	if p.kind() != "SQUARE_BRACES_START" {
		p.unexpected("SQUARE_BRACES_START")
		return nil
	}
	data, ok := p.plotData()
	if !ok {
		return nil
	}
	plot.Data = data
	plot.Span.End = data.Span.End
	return plot
}

func (p *parser) plotData() (PlotData, bool) {
	open := p.take()
	data := PlotData{Span: open.Span}
	for {
		point, ok := p.dataPoint(open)
		if !ok {
			return PlotData{}, false
		}
		data.Points = append(data.Points, point)
		switch p.kind() {
		case "COMMA":
			p.take()
			continue
		case "SQUARE_BRACES_END":
			data.Span.End = p.take().Span.End
			return data, true
		}
		p.unterminatedList(open, "COMMA", "SQUARE_BRACES_END")
		return PlotData{}, false
	}
}

func (p *parser) dataPoint(open Token) (DataPoint, bool) {
	if p.kind() == "EOF" {
		p.unterminatedList(open)
		return DataPoint{}, false
	}
	number, ok := p.number()
	if !ok {
		return DataPoint{}, false
	}
	point := DataPoint{Span: number.Span, Number: number}
	if p.kind() == "STR" {
		token := p.take()
		label := Text{Span: token.Span, Value: token.Text}
		point.Label = &label
		point.Span.End = token.Span.End
	}
	return point, true
}
