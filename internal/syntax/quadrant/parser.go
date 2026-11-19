package quadrant

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "quadrant/unexpected-token"
	codeUnknown      = "quadrant/unknown-statement"
	codeUnterminated = "quadrant/unterminated"
)

var (
	alphaNumTokens  = []string{"ALPHA", "AMP", "BRKT", "COMMA", "DOT", "EQUALS", "MULT", "NUM", "PLUS", "PUNCTUATION", "UNDERSCORE", "UNICODE_TEXT"}
	textTailTokens  = append(slices.Clone(alphaNumTokens), "MINUS", "SPACE")
	textStarts      = append(slices.Clone(alphaNumTokens), "MD_STR", "STR")
	styleComponents = []string{"ALPHA", "BRKT", "COLON", "MINUS", "NUM", "SPACE"}
	idStringTokens  = []string{"ALPHA", "AMP", "BRKT", "COLON", "COMMA", "MINUS", "MULT", "NUM", "UNICODE_TEXT"}
	endOfLine       = []string{"EOF", "NEWLINE", "SEMI"}
)

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
	end := source.Span{Start: len(p.src), End: len(p.src)}
	return Token{Kind: "EOF", Span: end, Content: end}
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

func (p *parser) is(kinds []string) bool { return slices.Contains(kinds, p.kind()) }

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

func (p *parser) describe(t Token) string {
	switch {
	case t.Kind == "EOF":
		return "end of input"
	case t.Kind == "INVALID" && t.Span.Start == t.Span.End:
		return "end of line"
	}
	return sub(p.src, t.Span.Start, t.Span.End)
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		p.unterminated(token)
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	names = slices.Compact(names)
	p.issue(codeUnexpected, "unexpected "+p.describe(token)+", expected one of: "+strings.Join(names, ", "), token.Span)
	p.recover(p.lastEnd())
}

func (p *parser) unterminated(token Token) {
	p.issue(codeUnterminated, "unterminated "+token.Text, token.Span)
	p.take()
}

func (p *parser) boundary(prevEnd int) bool {
	t := p.token()
	switch t.Kind {
	case "NEWLINE", "SEMI", "EOF", "UNTERMINATED":
		return true
	}
	return strings.ContainsAny(sub(p.src, min(prevEnd, t.Span.Start), t.Span.Start), "\n\r")
}

func (p *parser) recover(prevEnd int) {
	for !p.boundary(prevEnd) {
		prevEnd = p.take().Span.End
	}
}

func (p *parser) start() *Start {
	first := p.token().Span.Start
	for p.kind() == "NEWLINE" || p.kind() == "SEMI" || p.kind() == "SPACE" {
		p.take()
	}
	if p.kind() != "QUADRANT" {
		p.unexpected("QUADRANT", "NEWLINE", "SEMI", "SPACE")
		return &Start{Span: source.Span{Start: first, End: len(p.src)}, Document: Document{Span: source.Span{Start: len(p.src), End: len(p.src)}}}
	}
	header := p.take()
	document := p.document()
	return &Start{Span: source.Span{Start: first, End: len(p.src)}, Header: header, Document: document}
}

func (p *parser) document() Document {
	start := p.token().Span.Start
	end := start
	var lines []Line
	for p.kind() != "EOF" {
		if p.kind() == "UNTERMINATED" {
			p.unterminated(p.token())
			continue
		}
		line := p.line()
		lines = append(lines, line)
		end = max(end, line.Span.End)
	}
	return Document{Span: source.Span{Start: start, End: end}, Lines: lines}
}

func (p *parser) line() Line {
	statement, ok := p.statement()
	line := Line{Statement: statement, Span: source.Span{Start: statement.Span.Start, End: statement.Span.End}}
	if !ok {
		p.terminate(&line)
		return line
	}
	if !p.is(endOfLine) {
		p.unexpected(endOfLine...)
	}
	p.terminate(&line)
	return line
}

func (p *parser) terminate(line *Line) {
	switch p.kind() {
	case "NEWLINE", "SEMI":
		line.Eol = p.take()
	case "EOF":
		line.Eol = p.token()
	default:
		end := source.Span{Start: p.lastEnd(), End: p.lastEnd()}
		line.Eol = Token{Kind: "EOF", Span: end, Content: end}
		return
	}
	line.Span.End = max(line.Span.End, line.Eol.Span.End)
}

func (p *parser) statement() (Statement, bool) {
	first := p.token().Span.Start
	for p.kind() == "SPACE" {
		p.take()
	}
	at := p.at
	kind, ok := p.statementKind()
	end := p.lastEnd()
	if p.at == at {
		end = max(first, p.lastEnd())
		if p.at == 0 || end < first {
			end = first
		}
	}
	return Statement{Span: source.Span{Start: first, End: end}, Kind: kind}, ok
}

func (p *parser) statementKind() (StatementKind, bool) {
	switch p.kind() {
	case "CLASSDEF":
		return result(p.classDef())
	case "X-AXIS", "Y-AXIS":
		return result(p.axis())
	case "QUADRANT_1", "QUADRANT_2", "QUADRANT_3", "QUADRANT_4":
		return result(p.quadrantDetails())
	case "title":
		return result(p.title())
	case "acc_title", "acc_descr":
		return result(p.accessibility())
	case "acc_descr_multiline_value":
		value := p.take()
		return &Accessibility{Span: value.Span, Multiline: true, Value: value}, true
	case "NEWLINE", "SEMI", "EOF", "UNTERMINATED":
		return nil, true
	}
	if p.is(textStarts) {
		return result(p.points())
	}
	p.unknownStatement()
	return nil, false
}

func result[P interface {
	StatementKind
	comparable
}](node P) (StatementKind, bool) {
	var zero P
	if node == zero {
		return nil, false
	}
	return node, true
}

func (p *parser) unknownStatement() {
	first := p.take()
	end := first.Span.End
	for !p.boundary(end) {
		end = p.take().Span.End
	}
	p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: end})
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
	if p.kind() != "title_value" {
		p.unexpected("title_value")
		return nil
	}
	value := p.take()
	return &Title{Span: source.Span{Start: keyword.Span.Start, End: value.Span.End}, Value: value}
}

func (p *parser) text(expected []string) (Text, bool) {
	if !p.is(textStarts) {
		p.unexpected(expected...)
		return Text{}, false
	}
	first := p.take()
	value := first.Text
	end := first.Span.End
	contentEnd := first.Content.End
	for p.is(textTailTokens) {
		token := p.take()
		value += token.Text
		end, contentEnd = token.Span.End, token.Span.End
	}
	return Text{
		Span:     source.Span{Start: first.Span.Start, End: end},
		Content:  source.Span{Start: first.Content.Start, End: contentEnd},
		Value:    value,
		Markdown: first.Kind == "MD_STR",
	}, true
}

func (p *parser) axis() *AxisDetails {
	keyword := p.take()
	axis := &AxisDetails{Y: keyword.Kind == "Y-AXIS", Span: keyword.Span}
	first, ok := p.text(textStarts)
	if !ok {
		return nil
	}
	axis.First, axis.Span.End = first, first.Span.End
	if p.kind() != "AXIS-TEXT-DELIMITER" {
		return axis
	}
	delimiter := p.take()
	axis.Delimiter, axis.Span.End = &delimiter, delimiter.Span.End
	if !p.is(textStarts) {
		return axis
	}
	second, ok := p.text(textStarts)
	if !ok {
		return nil
	}
	axis.Second, axis.Span.End = &second, second.Span.End
	return axis
}

func (p *parser) quadrantDetails() *QuadrantDetails {
	keyword := p.take()
	text, ok := p.text(textStarts)
	if !ok {
		return nil
	}
	number := int(keyword.Kind[len(keyword.Kind)-1] - '0')
	return &QuadrantDetails{Span: source.Span{Start: keyword.Span.Start, End: text.Span.End}, Number: number, Text: text}
}

func (p *parser) classDef() *ClassDefStatement {
	keyword := p.take()
	if p.kind() != "SPACE" {
		p.unexpected("SPACE")
		return nil
	}
	p.take()
	name, ok := p.idString()
	if !ok {
		return nil
	}
	if p.kind() != "SPACE" {
		p.unexpected(append(slices.Clone(idStringTokens), "SPACE")...)
		return nil
	}
	p.take()
	styles, ok := p.stylesOpt()
	if !ok {
		return nil
	}
	return &ClassDefStatement{Span: source.Span{Start: keyword.Span.Start, End: styles.Span.End}, Name: name, Styles: styles}
}

func (p *parser) idString() (IdString, bool) {
	if !p.is(idStringTokens) {
		p.unexpected(idStringTokens...)
		return IdString{}, false
	}
	first := p.token()
	var value strings.Builder
	end := first.Span.End
	for p.is(idStringTokens) {
		token := p.take()
		value.WriteString(token.Text)
		end = token.Span.End
	}
	return IdString{Span: source.Span{Start: first.Span.Start, End: end}, Text: value.String()}, true
}

func (p *parser) stylesOpt() (StylesOpt, bool) {
	first := p.token().Span.Start
	opt := StylesOpt{Span: source.Span{Start: first, End: first}}
	for {
		style, ok := p.style()
		if !ok {
			return StylesOpt{}, false
		}
		opt.Styles = append(opt.Styles, style)
		opt.Span.End = style.Span.End
		if p.kind() != "COMMA" {
			return opt, true
		}
		p.take()
	}
}

func (p *parser) style() (Style, bool) {
	if !p.is(styleComponents) {
		p.unexpected(styleComponents...)
		return Style{}, false
	}
	first := p.token()
	var value strings.Builder
	end := first.Span.End
	for p.is(styleComponents) {
		token := p.take()
		value.WriteString(token.Text)
		end = token.Span.End
	}
	return Style{Span: source.Span{Start: first.Span.Start, End: end}, Text: value.String()}, true
}

func (p *parser) points() *Points {
	text, ok := p.text(textStarts)
	if !ok {
		return nil
	}
	point := &Points{Text: text, Span: text.Span}
	if p.kind() == "class_name" {
		class := p.take()
		point.Class = &class
	}
	if p.kind() != "point_start" {
		expected := []string{"point_start"}
		if point.Class == nil {
			expected = append(expected, "class_name")
			expected = append(expected, textTailTokens...)
		}
		p.unexpected(expected...)
		return nil
	}
	p.take()
	if p.kind() != "point_x" {
		p.unexpected("point_x")
		return nil
	}
	point.PointX = p.take()
	if p.kind() != "point_y" {
		p.unexpected("point_y")
		return nil
	}
	point.PointY = p.take()
	point.Span.End = point.PointY.Span.End
	if !p.is(styleComponents) {
		return point
	}
	styles, ok := p.stylesOpt()
	if !ok {
		return nil
	}
	point.Styles = &styles
	point.Span.End = styles.Span.End
	return point
}
