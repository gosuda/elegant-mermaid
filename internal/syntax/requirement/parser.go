package requirement

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	statementsExpected        = "CLASS, CLASSDEF, DESIGN_CONSTRAINT, ELEMENT, EOF, FUNCTIONAL_REQUIREMENT, INTERFACE_REQUIREMENT, NEWLINE, PERFORMANCE_REQUIREMENT, PHYSICAL_REQUIREMENT, REQUIREMENT, STYLE, acc_descr, acc_descr_multiline_value, acc_title, direction_bt, direction_lr, direction_rl, direction_tb, qString, unqString"
	styleComponentsExpected   = "ALPHA, BRKT, COLON, LABEL, MINUS, NUM, PCT, SEMICOLON, SPACE, UNIT"
	riskExpected              = "HIGH_RISK, LOW_RISK, MED_RISK"
	verifyExpected            = "VERIFY_ANALYSIS, VERIFY_DEMONSTRATION, VERIFY_INSPECTION, VERIFY_TEST"
	relationsExpected         = "CONTAINS, COPIES, DERIVES, REFINES, SATISFIES, TRACES, VERIFIES"
	requirementFieldsExpected = "ID, NEWLINE, RISK, STRUCT_STOP, TEXT, VERIFYMTHD"
	elementFieldsExpected     = "DOCREF, NEWLINE, STRUCT_STOP, TYPE"
	namesExpected             = "ALPHA, qString, unqString"
	valuesExpected            = "qString, unqString"
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	cleaned := source.Clean(src, removed)
	p := parser{src: string(src), cleaned: cleaned, tokens: lex(cleaned)}
	p.newlines()
	var directives []Directive
	for isDirective(p.kind()) {
		if d, ok := p.directive(); ok {
			directives = append(directives, d)
		}
		p.newlines()
	}
	header := p.header()
	diagram := p.diagram(p.end())
	start := header.Span.Start
	if len(directives) > 0 {
		start = directives[0].Span.Start
	}
	document := &Start{
		Span:       source.Span{Start: start, End: len(src)},
		Header:     header,
		Diagram:    diagram,
		Directives: directives,
	}
	return document, p.diags
}

type parser struct {
	src     string
	cleaned *source.Cleaned
	tokens  []Token
	at      int
	diags   []diag.Diagnostic
}

func (p *parser) kind() string {
	if p.at >= len(p.tokens) {
		return "EOF"
	}
	return p.tokens[p.at].Kind
}

func (p *parser) peek() Token {
	if p.at >= len(p.tokens) {
		return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
	}
	return p.tokens[p.at]
}

func (p *parser) take() (Token, bool) {
	if p.at >= len(p.tokens) {
		return Token{}, false
	}
	t := p.tokens[p.at]
	p.at++
	return t, true
}

func (p *parser) span() source.Span { return p.peek().Span }

func (p *parser) end() int {
	if p.at == 0 {
		return 0
	}
	return p.tokens[p.at-1].Span.End
}

func (p *parser) since(start int) source.Span {
	return source.Span{Start: start, End: p.end()}
}

func (p *parser) newlines() {
	for p.kind() == "NEWLINE" {
		p.at++
	}
}

func (p *parser) header() Token {
	header, ok := p.expect("RD")
	if !ok {
		return Token{Kind: "RD", Span: p.span()}
	}
	p.expect("NEWLINE")
	return header
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take()
	}
	p.reject(kind)
	return Token{}, false
}

func (p *parser) reject(expected string) {
	if p.kind() == "UNTERMINATED" {
		p.unterminated()
		return
	}
	p.unexpected(expected)
}

func (p *parser) unexpected(expected string) {
	span := p.span()
	text := ""
	if span.Start < len(p.src) {
		if span.End > len(p.src) {
			span.End = len(p.src)
		}
		text = string(p.cleaned.Slice(span))
	}
	p.emit("requirement/unexpected-token", "unexpected "+text+", expected one of: "+expected, span)
}

func (p *parser) unterminated() {
	t, ok := p.take()
	if !ok {
		return
	}
	p.emit("requirement/unterminated", "unterminated "+t.Text, t.Span)
}

func (p *parser) emit(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: diagnosticHelp(code)})
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) lineBreak(start, end int) bool {
	if start < 0 || end > len(p.src) || start >= end {
		return false
	}
	return strings.ContainsAny(string(p.cleaned.Slice(source.Span{Start: start, End: end})), "\r\n")
}

func (p *parser) recover() {
	if p.lineBreak(p.end(), p.span().Start) {
		return
	}
	for p.kind() != "EOF" && p.kind() != "NEWLINE" && p.kind() != "STRUCT_STOP" {
		end := p.span().End
		if p.kind() == "UNTERMINATED" {
			p.unterminated()
		} else {
			p.at++
		}
		if p.lineBreak(end, p.span().Start) {
			break
		}
	}
}

func (p *parser) unknown() {
	t, ok := p.take()
	if !ok {
		return
	}
	end := t.Span.End
	if !p.lineBreak(t.Span.End, p.span().Start) {
		p.recover()
		end = p.end()
	}
	p.emit("requirement/unknown-statement", "unknown statement "+t.Text, source.Span{Start: t.Span.Start, End: end})
}

func (p *parser) diagram(bodyStart int) Diagram {
	var statements []Statement
	for p.kind() != "EOF" {
		p.newlines()
		if p.kind() == "EOF" {
			break
		}
		before := p.at
		if s, ok := p.statement(); ok {
			statements = append(statements, s)
		} else {
			p.recover()
		}
		if p.at == before {
			p.at++
		}
	}
	span := source.Span{Start: bodyStart, End: bodyStart}
	if len(statements) > 0 {
		span = source.Span{Start: statements[0].Span.Start, End: statements[len(statements)-1].Span.End}
	}
	return Diagram{Span: span, Statements: statements}
}

func (p *parser) statement() (Statement, bool) {
	start := p.span().Start
	kind, ok := p.statementKind()
	if !ok {
		return Statement{}, false
	}
	return Statement{Span: p.since(start), Kind: kind}, true
}

func (p *parser) statementKind() (StatementKind, bool) {
	switch kind := p.kind(); {
	case requirementType(kind) != "":
		return p.requirementStatement()
	case kind == "ELEMENT":
		return p.elementStatement()
	case kind == "unqString" || kind == "qString":
		return p.named()
	case kind == "STYLE" || kind == "CLASSDEF" || kind == "CLASS":
		return p.styled()
	}
	return p.accessoryStatement()
}

func (p *parser) requirementStatement() (StatementKind, bool) {
	def, ok := p.requirement()
	if !ok {
		return StatementKind{}, false
	}
	return StatementKind{Kind: "Requirement", Requirement: def}, true
}

func (p *parser) elementStatement() (StatementKind, bool) {
	def, ok := p.element()
	if !ok {
		return StatementKind{}, false
	}
	return StatementKind{Kind: "Element", Element: def}, true
}

func (p *parser) accessoryStatement() (StatementKind, bool) {
	switch kind := p.kind(); {
	case isDirective(kind):
		return p.directiveStatement()
	case kind == "direction_tb" || kind == "direction_bt" || kind == "direction_rl" || kind == "direction_lr":
		return StatementKind{Kind: "Direction", Direction: p.directionStatement()}, true
	case kind == "title":
		p.unexpected(statementsExpected)
		p.at++
		return StatementKind{}, false
	case kind == "UNTERMINATED":
		p.unterminated()
		return StatementKind{}, false
	}
	p.unknown()
	return StatementKind{}, false
}

func (p *parser) directiveStatement() (StatementKind, bool) {
	d, ok := p.directive()
	if !ok {
		return StatementKind{}, false
	}
	return StatementKind{Kind: "Directive", Directive: &d}, true
}

func (p *parser) value() (Token, bool) {
	if p.kind() == "unqString" || p.kind() == "qString" {
		return p.take()
	}
	p.reject(valuesExpected)
	return Token{}, false
}

func (p *parser) id() (Id, bool) {
	t, ok := p.value()
	if !ok {
		return Id{}, false
	}
	return Id{Span: t.Span, Quoted: t.Kind == "qString", Value: t.Text}, true
}

func (p *parser) listName() (Id, bool) {
	kind := p.kind()
	if kind != "ALPHA" && kind != "unqString" && kind != "qString" {
		p.reject(namesExpected)
		return Id{}, false
	}
	t, _ := p.take()
	return Id{Span: t.Span, Quoted: t.Kind == "qString", Value: t.Text}, true
}

func (p *parser) idList() (IdList, bool) {
	first, ok := p.listName()
	if !ok {
		return IdList{}, false
	}
	list := IdList{Span: first.Span, Names: []Id{first}}
	for p.kind() == "COMMA" {
		p.at++
		name, ok := p.listName()
		if !ok {
			return IdList{}, false
		}
		list.Names = append(list.Names, name)
	}
	list.Span.End = p.end()
	return list, true
}

func (p *parser) inlineClasses() (*IdList, bool) {
	if p.kind() != "STYLE_SEPARATOR" {
		return nil, true
	}
	p.at++
	classes, ok := p.idList()
	if !ok {
		return nil, false
	}
	return &classes, true
}

func (p *parser) openBody() (Token, bool) {
	open, ok := p.expect("STRUCT_START")
	if !ok {
		return Token{}, false
	}
	if p.kind() == "EOF" {
		p.closeBody(open.Span)
		return Token{}, false
	}
	if _, ok := p.expect("NEWLINE"); !ok {
		return Token{}, false
	}
	return open, true
}

func (p *parser) closeBody(opening source.Span) (Token, bool) {
	if p.kind() != "EOF" {
		return p.expect("STRUCT_STOP")
	}
	if len(p.diags) == 0 || p.diags[len(p.diags)-1].Code != "requirement/unterminated" {
		p.emit("requirement/unterminated", "unterminated {", source.Span{Start: opening.Start, End: len(p.src)})
	}
	return Token{}, false
}

func (p *parser) requirement() (*RequirementDef, bool) {
	keyword, ok := p.take()
	if !ok {
		return nil, false
	}
	nameToken, ok := p.value()
	if !ok {
		return nil, false
	}
	classes, ok := p.inlineClasses()
	if !ok {
		return nil, false
	}
	open, ok := p.openBody()
	if !ok {
		return nil, false
	}
	body, ok := p.requirementBody(open.Span)
	if !ok {
		return nil, false
	}
	return &RequirementDef{
		Span:            p.since(keyword.Span.Start),
		RequirementType: RequirementType{Span: keyword.Span, Value: requirementType(keyword.Kind)},
		Name:            RequirementName{Span: nameToken.Span, Quoted: nameToken.Kind == "qString", Value: nameToken.Text},
		Classes:         classes,
		Body:            body,
		Delimiters:      [2]source.Span{open.Span, p.tokens[p.at-1].Span},
	}, true
}

func (p *parser) requirementBody(opening source.Span) (RequirementBody, bool) {
	var fields []RequirementField
	for p.kind() != "STRUCT_STOP" && p.kind() != "EOF" {
		p.newlines()
		if p.kind() == "STRUCT_STOP" || p.kind() == "EOF" {
			break
		}
		before := p.at
		if field, ok := p.requirementField(); ok {
			fields = append(fields, field)
		} else {
			p.recover()
		}
		if p.at == before {
			p.at++
		}
	}
	close, ok := p.closeBody(opening)
	if !ok {
		return RequirementBody{}, false
	}
	start := close.Span.Start
	if len(fields) > 0 {
		start = fields[0].Span.Start
	}
	return RequirementBody{Span: source.Span{Start: start, End: close.Span.End}, Fields: fields}, true
}

func (p *parser) requirementField() (RequirementField, bool) {
	if !p.oneOf("ID", "TEXT", "RISK", "VERIFYMTHD") {
		p.reject(requirementFieldsExpected)
		return RequirementField{}, false
	}
	keyword, _ := p.take()
	colon, ok := p.expect("COLONSEP")
	if !ok {
		return RequirementField{}, false
	}
	value, ok := p.requirementValue(keyword.Kind)
	if !ok {
		return RequirementField{}, false
	}
	span := p.since(keyword.Span.Start)
	if _, ok := p.expect("NEWLINE"); !ok {
		return RequirementField{}, false
	}
	return RequirementField{Span: span, Keyword: keyword, Colon: colon.Span, Value: value}, true
}

func (p *parser) requirementValue(kind string) (RequirementFieldValue, bool) {
	switch kind {
	case "ID":
		id, ok := p.id()
		if !ok {
			return RequirementFieldValue{}, false
		}
		return RequirementFieldValue{Kind: "Id", Id: id}, true
	case "TEXT":
		t, ok := p.value()
		if !ok {
			return RequirementFieldValue{}, false
		}
		return RequirementFieldValue{Kind: "Text", Text: Text{Span: t.Span, Quoted: t.Kind == "qString", Value: t.Text}}, true
	case "RISK":
		risk, ok := p.risk()
		if !ok {
			return RequirementFieldValue{}, false
		}
		return RequirementFieldValue{Kind: "Risk", Risk: risk}, true
	}
	verify, ok := p.verify()
	if !ok {
		return RequirementFieldValue{}, false
	}
	return RequirementFieldValue{Kind: "Verify", Verify: verify}, true
}

func (p *parser) risk() (RiskLevel, bool) {
	value := ""
	switch p.kind() {
	case "LOW_RISK":
		value = "Low"
	case "MED_RISK":
		value = "Medium"
	case "HIGH_RISK":
		value = "High"
	default:
		p.reject(riskExpected)
		return RiskLevel{}, false
	}
	t, _ := p.take()
	return RiskLevel{Span: t.Span, Value: value}, true
}

func (p *parser) verify() (VerifyType, bool) {
	value := ""
	switch p.kind() {
	case "VERIFY_ANALYSIS":
		value = "Analysis"
	case "VERIFY_DEMONSTRATION":
		value = "Demonstration"
	case "VERIFY_INSPECTION":
		value = "Inspection"
	case "VERIFY_TEST":
		value = "Test"
	default:
		p.reject(verifyExpected)
		return VerifyType{}, false
	}
	t, _ := p.take()
	return VerifyType{Span: t.Span, Value: value}, true
}

func (p *parser) element() (*ElementDef, bool) {
	keyword, ok := p.take()
	if !ok {
		return nil, false
	}
	nameToken, ok := p.value()
	if !ok {
		return nil, false
	}
	classes, ok := p.inlineClasses()
	if !ok {
		return nil, false
	}
	open, ok := p.openBody()
	if !ok {
		return nil, false
	}
	body, ok := p.elementBody(open.Span)
	if !ok {
		return nil, false
	}
	return &ElementDef{
		Span:       p.since(keyword.Span.Start),
		Name:       ElementName{Span: nameToken.Span, Quoted: nameToken.Kind == "qString", Value: nameToken.Text},
		Classes:    classes,
		Body:       body,
		Delimiters: [2]source.Span{open.Span, p.tokens[p.at-1].Span},
	}, true
}

func (p *parser) elementBody(opening source.Span) (ElementBody, bool) {
	var fields []ElementField
	for p.kind() != "STRUCT_STOP" && p.kind() != "EOF" {
		p.newlines()
		if p.kind() == "STRUCT_STOP" || p.kind() == "EOF" {
			break
		}
		before := p.at
		if field, ok := p.elementField(); ok {
			fields = append(fields, field)
		} else {
			p.recover()
		}
		if p.at == before {
			p.at++
		}
	}
	close, ok := p.closeBody(opening)
	if !ok {
		return ElementBody{}, false
	}
	start := close.Span.Start
	if len(fields) > 0 {
		start = fields[0].Span.Start
	}
	return ElementBody{Span: source.Span{Start: start, End: close.Span.End}, Fields: fields}, true
}

func (p *parser) elementField() (ElementField, bool) {
	if !p.oneOf("TYPE", "DOCREF") {
		p.reject(elementFieldsExpected)
		return ElementField{}, false
	}
	keyword, _ := p.take()
	colon, ok := p.expect("COLONSEP")
	if !ok {
		return ElementField{}, false
	}
	t, ok := p.value()
	if !ok {
		return ElementField{}, false
	}
	value := ElementFieldValue{Kind: "Ref", Ref: Ref{Span: t.Span, Quoted: t.Kind == "qString", Value: t.Text}}
	if keyword.Kind == "TYPE" {
		value = ElementFieldValue{Kind: "Type", Type: Type{Span: t.Span, Quoted: t.Kind == "qString", Value: t.Text}}
	}
	span := p.since(keyword.Span.Start)
	if _, ok := p.expect("NEWLINE"); !ok {
		return ElementField{}, false
	}
	return ElementField{Span: span, Keyword: keyword, Colon: colon.Span, Value: value}, true
}

func (p *parser) named() (StatementKind, bool) {
	next := "EOF"
	if p.at+1 < len(p.tokens) {
		next = p.tokens[p.at+1].Kind
	}
	if next != "STYLE_SEPARATOR" && next != "LINE" && next != "END_ARROW_L" {
		p.unknown()
		return StatementKind{}, false
	}
	left, ok := p.id()
	if !ok {
		return StatementKind{}, false
	}
	if p.kind() == "STYLE_SEPARATOR" {
		separator, _ := p.take()
		classes, ok := p.idList()
		if !ok {
			return StatementKind{}, false
		}
		sep := separator.Span
		return StatementKind{Kind: "Class", Class: &ClassStatement{
			Span:      p.since(left.Span.Start),
			Targets:   IdList{Span: left.Span, Names: []Id{left}},
			Classes:   classes,
			Separator: &sep,
		}}, true
	}
	relation, ok := p.relationship(left)
	if !ok {
		return StatementKind{}, false
	}
	return StatementKind{Kind: "Relationship", Relationship: relation}, true
}

func (p *parser) relationship(left Id) (*RelationshipDef, bool) {
	first, ok := p.take()
	if !ok {
		return nil, false
	}
	relation, ok := p.relationKind()
	if !ok {
		return nil, false
	}
	var arrow Token
	var line source.Span
	arrow, line, ok = p.arrowLine(first)
	if !ok {
		return nil, false
	}
	right, ok := p.id()
	if !ok {
		return nil, false
	}
	return &RelationshipDef{
		Span:         p.since(left.Span.Start),
		Left:         left,
		Right:        right,
		Relationship: relation,
		Arrow:        arrow,
		Line:         line,
		Reversed:     arrow.Kind == "END_ARROW_L",
	}, true
}

func (p *parser) arrowLine(first Token) (Token, source.Span, bool) {
	if first.Kind == "END_ARROW_L" {
		line, ok := p.expect("LINE")
		return first, line.Span, ok
	}
	arrow, ok := p.expect("END_ARROW_R")
	return arrow, first.Span, ok
}

func (p *parser) relationKind() (Relationship, bool) {
	value := ""
	switch p.kind() {
	case "CONTAINS":
		value = "contains"
	case "COPIES":
		value = "copies"
	case "DERIVES":
		value = "derives"
	case "SATISFIES":
		value = "satisfies"
	case "VERIFIES":
		value = "verifies"
	case "REFINES":
		value = "refines"
	case "TRACES":
		value = "traces"
	default:
		p.reject(relationsExpected)
		return Relationship{}, false
	}
	t, _ := p.take()
	return Relationship{Span: t.Span, Value: value}, true
}

func (p *parser) directive() (Directive, bool) {
	first, ok := p.take()
	if !ok {
		return Directive{}, false
	}
	value := first
	switch first.Kind {
	case "acc_title":
		t, ok := p.expect("acc_title_value")
		if !ok {
			return Directive{}, false
		}
		value = t
	case "acc_descr":
		t, ok := p.expect("acc_descr_value")
		if !ok {
			return Directive{}, false
		}
		value = t
	}
	return Directive{
		Span:      p.since(first.Span.Start),
		Title:     first.Kind == "acc_title",
		Multiline: first.Kind == "acc_descr_multiline_value",
		Value:     value,
	}, true
}

func (p *parser) directionStatement() Direction {
	t, _ := p.take()
	value := "LR"
	switch t.Kind {
	case "direction_tb":
		value = "TB"
	case "direction_bt":
		value = "BT"
	case "direction_rl":
		value = "RL"
	}
	return Direction{Span: t.Span, Value: value}
}

func (p *parser) styled() (StatementKind, bool) {
	keyword, ok := p.take()
	if !ok {
		return StatementKind{}, false
	}
	ids, ok := p.idList()
	if !ok {
		return StatementKind{}, false
	}
	if keyword.Kind == "CLASS" {
		classes, ok := p.idList()
		if !ok {
			return StatementKind{}, false
		}
		return StatementKind{Kind: "Class", Class: &ClassStatement{Span: p.since(keyword.Span.Start), Targets: ids, Classes: classes}}, true
	}
	styles, ok := p.styles()
	if !ok {
		return StatementKind{}, false
	}
	span := p.since(keyword.Span.Start)
	if keyword.Kind == "CLASSDEF" {
		return StatementKind{Kind: "ClassDef", ClassDef: &ClassDefStatement{Span: span, Ids: ids, Styles: styles}}, true
	}
	return StatementKind{Kind: "Style", Style: &StyleStatement{Span: span, Ids: ids, Styles: styles}}, true
}

func (p *parser) styles() (StylesOpt, bool) {
	first, ok := p.style()
	if !ok {
		return StylesOpt{}, false
	}
	opt := StylesOpt{Span: first.Span, Styles: []Style{first}}
	for p.kind() == "COMMA" && !p.lineBreak(p.end(), p.span().Start) {
		p.at++
		style, ok := p.style()
		if !ok {
			return StylesOpt{}, false
		}
		opt.Styles = append(opt.Styles, style)
	}
	if p.kind() != "EOF" && p.kind() != "NEWLINE" && !p.lineBreak(p.end(), p.span().Start) {
		p.reject(styleComponentsExpected)
		return StylesOpt{}, false
	}
	opt.Span.End = p.end()
	return opt, true
}

func (p *parser) style() (Style, bool) {
	start := p.span().Start
	var components []StyleComponent
	for isComponent(p.kind()) && !p.lineBreak(p.end(), p.span().Start) {
		t, _ := p.take()
		components = append(components, StyleComponent{Span: t.Span, Kind: t.Kind, Text: t.Text})
	}
	if len(components) == 0 {
		p.reject(styleComponentsExpected)
		return Style{}, false
	}
	return Style{Span: p.since(start), Components: components}, true
}

func (p *parser) oneOf(kinds ...string) bool {
	kind := p.kind()
	for _, k := range kinds {
		if k == kind {
			return true
		}
	}
	return false
}

func isDirective(kind string) bool {
	return kind == "acc_title" || kind == "acc_descr" || kind == "acc_descr_multiline_value"
}

func isComponent(kind string) bool {
	switch kind {
	case "ALPHA", "NUM", "COLON", "UNIT", "SPACE", "BRKT", "PCT", "MINUS", "LABEL", "SEMICOLON":
		return true
	}
	return false
}

func requirementType(kind string) string {
	switch kind {
	case "REQUIREMENT":
		return "Requirement"
	case "FUNCTIONAL_REQUIREMENT":
		return "Functional Requirement"
	case "INTERFACE_REQUIREMENT":
		return "Interface Requirement"
	case "PERFORMANCE_REQUIREMENT":
		return "Performance Requirement"
	case "PHYSICAL_REQUIREMENT":
		return "Physical Requirement"
	case "DESIGN_CONSTRAINT":
		return "Design Constraint"
	}
	return ""
}
