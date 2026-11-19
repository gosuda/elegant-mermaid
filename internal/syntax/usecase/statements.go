package usecase

import (
	"slices"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var unsupportedStatements = [...]string{"allowmixing", "newpage", "package", "rectangle", "skinparam"}

var (
	arrowKinds      = []string{"DEPENDENCY_ARROW", "GENERALIZATION", "FORWARD_SOLID", "BACKWARD_SOLID", "MARKERLESS_SOLID", "FORWARD_CIRCLE", "BACKWARD_CIRCLE", "FORWARD_CROSS", "BACKWARD_CROSS"}
	solidAllowed    = []string{"FORWARD_SOLID", "MARKERLESS_SOLID", "FORWARD_CIRCLE", "FORWARD_CROSS"}
	backwardAllowed = []string{"MARKERLESS_SOLID"}
)

func (p *parser) statement() (Statement, bool) {
	var st Statement
	switch k := p.kind(); k {
	case "ACC_TITLE_LINE", "ACC_DESCR_LINE", "ACC_DESCR_BLOCK":
		return st, p.accessibility(&st)
	case "DIRECTION":
		st.Direction = p.direction()
		return st, st.Direction != nil
	case "ACTOR":
		st.Actor = p.actors()
		return st, st.Actor != nil
	case "SYSTEM_BOUNDARY":
		st.SystemBoundary = p.boundary()
		return st, st.SystemBoundary != nil
	case "NOTE":
		st.Note = p.note()
		return st, st.Note != nil
	case "JSON_DECLARATION_START":
		st.JSON = p.jsonStatement()
		return st, st.JSON != nil
	case "CLASS_DEF", "CLASS", "STYLE":
		return st, p.styleStatement(&st)
	case "IDENTIFIER", "PLAIN_STRING", "MARKDOWN_STRING":
		return st, p.namedStatement(&st)
	default:
		if strings.HasPrefix(k, "UNCLOSED_") {
			p.unexpected("STATEMENT")
		} else {
			p.unknown()
		}
		return st, false
	}
}

func (p *parser) unknown() {
	token, ok := p.take()
	if !ok {
		return
	}
	p.recover()
	p.issue("usecase/unknown-statement", "unknown statement "+token.Text, p.span(token.Span.Start))
}

func (p *parser) namedStatement(st *Statement) bool {
	if t := p.peek(1); t != nil && t.Kind == "METADATA_START" {
		st.MetadataAssignment = p.metadataAssignment()
		return st.MetadataAssignment != nil
	}
	head := p.peek(0)
	if head == nil {
		return false
	}
	for _, keyword := range unsupportedStatements {
		if equalASCIIFold(head.Text, keyword) {
			p.unknown()
			return false
		}
	}
	name, ok := p.entity()
	if !ok {
		return false
	}
	relation, ok := p.optionalRelation()
	if !ok {
		return false
	}
	st.Entity = &EntityStatement{Span: p.span(name.Span.Start), Name: name, Relation: relation}
	return true
}

func (p *parser) metadataAssignment() *MetadataAssignmentStatement {
	token, _ := p.take()
	target := MetadataAssignmentTarget{Span: token.Span, Token: token, ContentSpan: contentSpan(token)}
	metadata, ok := p.metadata()
	if !ok {
		return nil
	}
	return &MetadataAssignmentStatement{Span: p.span(target.Span.Start), Target: target, Metadata: metadata}
}

func (p *parser) accessibility(st *Statement) bool {
	token, _ := p.take()
	delimiter := byte(':')
	closing := 0
	if token.Kind == "ACC_DESCR_BLOCK" {
		delimiter = '{'
		closing = 1
	}
	i := strings.IndexByte(token.Text, delimiter)
	if i < 0 {
		return false
	}
	raw := ""
	if i+1 <= len(token.Text)-closing {
		raw = token.Text[i+1 : len(token.Text)-closing]
	}
	value := strings.TrimSpace(raw)
	lead := len(raw) - len(strings.TrimLeftFunc(raw, unicode.IsSpace))
	begin := p.cleaned.Index(token.Span.Start) + i + 1 + lead
	content := p.cleaned.Span(begin, begin+len(value))
	if token.Kind == "ACC_TITLE_LINE" {
		st.AccTitle = &AccTitleStatement{Span: token.Span, Token: token, Value: value, ContentSpan: content}
	} else {
		st.AccDescr = &AccDescrStatement{Span: token.Span, Token: token, Value: value, ContentSpan: content}
	}
	return true
}

func (p *parser) direction() *DirectionStatement {
	keyword, _ := p.take()
	direction, ok := p.oneOf("TD", "TB", "BT", "LR", "RL")
	if !ok {
		return nil
	}
	return &DirectionStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, Direction: direction}
}

func (p *parser) actors() *ActorStatement {
	keyword, ok := p.expect("ACTOR")
	if !ok {
		return nil
	}
	items, ok := p.actorItems()
	if !ok {
		return nil
	}
	var relation *RelationTail
	if p.kind() != "COMMA" && len(items) == 1 {
		if relation, ok = p.optionalRelation(); !ok {
			return nil
		}
	}
	return &ActorStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, Items: items, Relation: relation}
}

func (p *parser) actorItems() ([]ActorItem, bool) {
	item, ok := p.actorItem()
	if !ok {
		return nil, false
	}
	items := []ActorItem{item}
	for p.kind() == "COMMA" {
		p.at++
		if item, ok = p.actorItem(); !ok {
			return nil, false
		}
		items = append(items, item)
	}
	return items, true
}

func (p *parser) boundary() *SystemBoundaryStatement {
	keyword, ok := p.expect("SYSTEM_BOUNDARY")
	if !ok {
		return nil
	}
	p.openings = append(p.openings, keyword)
	name, ok := p.boundaryName()
	if !ok {
		return nil
	}
	statement := &SystemBoundaryStatement{Keyword: keyword, Name: name}
	if p.kind() == "METADATA_START" {
		metadata, ok := p.metadata()
		if !ok {
			return nil
		}
		statement.Metadata = &metadata
	}
	if statement.Classes, ok = p.optionalClasses(); !ok {
		return nil
	}
	if statement.LineEnd, ok = p.lineEnd(); !ok {
		return nil
	}
	statement.Content = p.boundaryContent()
	if statement.Close, ok = p.expect("END"); !ok {
		return nil
	}
	p.popOpening()
	statement.Span = p.span(keyword.Span.Start)
	return statement
}

func (p *parser) boundaryName() (SystemBoundaryName, bool) {
	base, ok := p.baseName("LPAREN", "LBRACKET")
	return SystemBoundaryName(base), ok
}

func (p *parser) boundaryContent() SystemBoundaryContent {
	start := p.here().Start
	var elements []BoundaryElement
	for k := p.kind(); k != "END" && k != "EOF"; k = p.kind() {
		before := p.at
		if element, ok := p.boundaryElement(); ok {
			elements = append(elements, element)
		} else {
			p.recover()
			if p.kind() == "NEWLINE" {
				p.at++
			}
		}
		p.truncateOpenings(1)
		if p.at == before {
			p.at++
		}
	}
	return SystemBoundaryContent{Span: source.Span{Start: start, End: p.here().Start}, Elements: elements}
}

func (p *parser) boundaryElement() (BoundaryElement, bool) {
	if line, ok := p.spacing(); ok {
		return BoundaryElement{Span: line.Span, Blank: line.Blank, Comment: line.Comment}, true
	}
	if p.kind() == "ACTOR" {
		return p.boundaryActor()
	}
	name, ok := p.entity()
	if !ok {
		return BoundaryElement{}, false
	}
	lineEnd, ok := p.lineEnd()
	if !ok {
		return BoundaryElement{}, false
	}
	return BoundaryElement{Span: name.Span, Entity: &BoundaryEntity{Name: name, LineEnd: lineEnd}}, true
}

func (p *parser) boundaryActor() (BoundaryElement, bool) {
	keyword, _ := p.take()
	items, ok := p.actorItems()
	if !ok {
		return BoundaryElement{}, false
	}
	span := p.span(keyword.Span.Start)
	lineEnd, ok := p.lineEnd()
	if !ok {
		return BoundaryElement{}, false
	}
	return BoundaryElement{Span: span, Actor: &ActorDeclarationOnly{Span: span, Keyword: keyword, Items: items, LineEnd: lineEnd}}, true
}

func (p *parser) note() *NoteStatement {
	keyword, ok := p.expect("NOTE")
	if !ok {
		return nil
	}
	forToken, ok := p.expect("FOR")
	if !ok {
		return nil
	}
	target, ok := p.expect("IDENTIFIER")
	if !ok {
		return nil
	}
	label, ok := p.label()
	if !ok {
		return nil
	}
	return &NoteStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, ForToken: forToken, Target: target, Label: label}
}

func (p *parser) styleStatement(st *Statement) bool {
	keyword, _ := p.take()
	switch keyword.Kind {
	case "CLASS":
		st.Class = p.classAssignment(keyword)
		return st.Class != nil
	case "CLASS_DEF":
		st.ClassDef = p.classDefinition(keyword)
		return st.ClassDef != nil
	}
	target, ok := p.expect("IDENTIFIER")
	if !ok {
		return false
	}
	styles, ok := p.styles()
	if !ok {
		return false
	}
	st.Style = &StyleStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, Target: target, Styles: styles}
	return true
}

func (p *parser) classAssignment(keyword Token) *ClassStatement {
	targets, ok := p.identifiers()
	if !ok {
		return nil
	}
	classes, ok := p.identifiers()
	if !ok {
		return nil
	}
	return &ClassStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, Targets: targets, Classes: classes}
}

func (p *parser) classDefinition(keyword Token) *ClassDefStatement {
	classes, ok := p.identifiers()
	if !ok {
		return nil
	}
	styles, ok := p.styles()
	if !ok {
		return nil
	}
	return &ClassDefStatement{Span: p.span(keyword.Span.Start), Keyword: keyword, Classes: classes, Styles: styles}
}

func (p *parser) styles() (Styles, bool) {
	start := p.here().Start
	value, ok := p.styleValue()
	if !ok {
		return Styles{}, false
	}
	values := []StyleValue{value}
	for p.kind() == "COMMA" {
		p.at++
		if value, ok = p.styleValue(); !ok {
			return Styles{}, false
		}
		values = append(values, value)
	}
	return Styles{Span: p.span(start), Values: values}, true
}

func (p *parser) styleValue() (StyleValue, bool) {
	start := p.here().Start
	var key []Token
	if p.kind() == "MARKERLESS_SOLID" {
		token, _ := p.take()
		key = append(key, token)
	}
	if k := p.kind(); !isWord(k) && k != "CSS_IDENTIFIER" {
		p.unexpected("CSS_IDENTIFIER", "MARKERLESS_SOLID", "WORD")
		return StyleValue{}, false
	}
	token, _ := p.take()
	key = append(key, token)
	if _, ok := p.expect("COLON"); !ok {
		return StyleValue{}, false
	}
	var components []StyleComponent
	for isStyleComponent(p.kind()) {
		token, _ := p.take()
		components = append(components, StyleComponent{Span: token.Span, Token: token})
	}
	if len(components) == 0 {
		p.unexpected("STYLE_COMPONENT")
		return StyleValue{}, false
	}
	return StyleValue{Span: p.span(start), Key: key, Components: components}, true
}

func isStyleComponent(kind string) bool {
	if isWord(kind) {
		return true
	}
	switch kind {
	case "PLAIN_STRING", "NUMBER", "HASH_COLOR", "CSS_IDENTIFIER", "CSS_ESCAPED_COMMA", "DASH", "DOT", "PERCENT", "CSS_PUNCTUATION", "COLON", "LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE", "AT", "MARKERLESS_SOLID":
		return true
	}
	return false
}

func (p *parser) optionalRelation() (*RelationTail, bool) {
	if k := p.kind(); k == "NEWLINE" || k == "EOF" {
		return nil, true
	}
	tail := &RelationTail{}
	start := p.here().Start
	if next := p.peek(1); p.kind() == "IDENTIFIER" && next != nil && next.Kind == "AT" {
		id, _ := p.take()
		at, _ := p.take()
		tail.ID, tail.At = &id, &at
	}
	var ok bool
	if tail.Arrow, ok = p.arrow(); !ok {
		return nil, false
	}
	if tail.Endpoint, ok = p.entity(); !ok {
		return nil, false
	}
	tail.Span = p.span(start)
	return tail, true
}

func (p *parser) arrow() (Arrow, bool) {
	token, ok := p.oneOf(arrowKinds...)
	if !ok {
		return Arrow{}, false
	}
	var arrow Arrow
	if token.Kind == "DEPENDENCY_ARROW" || token.Kind == "GENERALIZATION" {
		if arrow.Semantic, ok = p.semanticRelation(token); !ok {
			return Arrow{}, false
		}
	} else if arrow, ok = p.association(token); !ok {
		return Arrow{}, false
	}
	arrow.Span = p.span(token.Span.Start)
	return arrow, true
}

func (p *parser) semanticRelation(token Token) (*SemanticRelation, bool) {
	relation := &SemanticRelation{Operator: token}
	if token.Kind == "DEPENDENCY_ARROW" {
		colon, ok := p.expect("COLON")
		if !ok {
			return nil, false
		}
		kind, ok := p.oneOf("INCLUDE", "EXTEND")
		if !ok {
			return nil, false
		}
		relation.Colon, relation.Relation = &colon, &kind
	}
	relation.Span = p.span(token.Span.Start)
	return relation, true
}

func (p *parser) association(token Token) (Arrow, bool) {
	var label *EdgeLabel
	var right *Token
	if allowed := allowedRight(token); p.labeledRight(allowed) {
		text, ok := p.label()
		if !ok {
			return Arrow{}, false
		}
		closing, ok := p.oneOf(allowed...)
		if !ok {
			return Arrow{}, false
		}
		label, right = &EdgeLabel{Span: text.Span, Label: text}, &closing
	}
	return associationArrow(token, p.span(token.Span.Start), label, right), true
}

func allowedRight(token Token) []string {
	switch {
	case token.Kind == "MARKERLESS_SOLID" && token.Text == "--":
		return solidAllowed
	case token.Kind == "BACKWARD_SOLID" && token.Text == "<--", token.Kind == "BACKWARD_CIRCLE", token.Kind == "BACKWARD_CROSS":
		return backwardAllowed
	}
	return nil
}

func (p *parser) labeledRight(allowed []string) bool {
	for n := 0; ; n++ {
		t := p.peek(n)
		if t == nil {
			return false
		}
		if n > 0 && slices.Contains(allowed, t.Kind) {
			return true
		}
		if !isLabel(t.Kind) && t.Kind != "PLAIN_STRING" && t.Kind != "MARKDOWN_STRING" {
			return false
		}
	}
}

func associationArrow(token Token, span source.Span, label *EdgeLabel, right *Token) Arrow {
	var arrow Arrow
	switch token.Kind {
	case "FORWARD_SOLID":
		arrow.ForwardSolid = &ForwardSolidOperator{Span: span, Token: token}
	case "FORWARD_CIRCLE":
		arrow.ForwardCircle = &ForwardCircleOperator{Span: span, Token: token}
	case "FORWARD_CROSS":
		arrow.ForwardCross = &ForwardCrossOperator{Span: span, Token: token}
	case "BACKWARD_SOLID":
		arrow.BackwardSolid = &BackwardSolidOperator{Span: span, Token: token, Label: label, Right: right}
	case "BACKWARD_CIRCLE":
		arrow.BackwardCircle = &BackwardCircleOperator{Span: span, Token: token, Label: label, Right: right}
	case "BACKWARD_CROSS":
		arrow.BackwardCross = &BackwardCrossOperator{Span: span, Token: token, Label: label, Right: right}
	default:
		arrow.MarkerlessSolid = &MarkerlessSolidOperator{Span: span, Token: token, Label: label, Right: right}
	}
	return arrow
}
