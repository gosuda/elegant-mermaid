package wardley

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "wardley/unexpected-token"
	codeUnknown      = "wardley/unknown-statement"
	codeUnterminated = "wardley/unterminated"
)

var (
	nameKinds      = []string{"ID", "NAME_WITH_SPACES", "STRING"}
	coordinate     = []string{"INT", "WARDLEY_NUMBER"}
	decimal        = []string{"WARDLEY_NUMBER"}
	integer        = []string{"INT"}
	metadataFields = map[string]string{"ACC_DESCR": "accDescr", "ACC_TITLE": "accTitle", "TITLE": "title"}
)

var statementParsers = map[string]func(*parser) bool{
	"KW_SIZE": (*parser).size, "KW_EVOLUTION": (*parser).evolution, "KW_ANCHOR": (*parser).anchor,
	"KW_COMPONENT": (*parser).component, "KW_EVOLVE": (*parser).evolve, "KW_PIPELINE": (*parser).pipeline,
	"KW_NOTE": (*parser).note, "KW_ANNOTATIONS": (*parser).annotations, "KW_ANNOTATION": (*parser).annotation,
	"KW_ACCELERATOR": (*parser).accelerator, "KW_DEACCELERATOR": (*parser).deaccelerator,
	"ID": (*parser).link, "NAME_WITH_SPACES": (*parser).link, "STRING": (*parser).link,
	"ACC_DESCR": (*parser).metadata, "ACC_TITLE": (*parser).metadata, "TITLE": (*parser).metadata,
}

func Parse(src []byte, removed []source.Span) (*Wardley, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed), out: &Wardley{}}
	p.skipNewlines()
	p.header()
	p.statements()
	p.out.Span = source.Span{Start: p.out.Header.Span.Start, End: len(text)}
	return p.out, p.diags
}

type parser struct {
	src     string
	tokens  []Token
	at      int
	openers []Token
	diags   []diag.Diagnostic
	out     *Wardley
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string { return p.token().Kind }

func (p *parser) peekKind(ahead int) string {
	if p.at+ahead < len(p.tokens) {
		return p.tokens[p.at+ahead].Kind
	}
	return "EOF"
}

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

func (p *parser) span(start int) source.Span {
	end := start
	if p.at > 0 {
		end = p.tokens[p.at-1].Span.End
	}
	return source.Span{Start: start, End: end}
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
	switch {
	case token.Kind == "UNTERMINATED":
		return
	case token.Kind == "EOF" && len(p.openers) > 0:
		opener := p.openers[len(p.openers)-1]
		p.issue(codeUnterminated, "unterminated "+opener.Text, source.Span{Start: opener.Span.Start, End: len(p.src)})
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

func (p *parser) skipLine() { p.skipUntil() }

func (p *parser) skipMemberLine() { p.skipUntil("}") }

func (p *parser) skipUntil(stops ...string) {
	for {
		switch kind := p.kind(); {
		case kind == "EOF" || kind == "UNTERMINATED" || slices.Contains(stops, kind):
			return
		case kind == "NEWLINE":
			p.take()
			return
		}
		p.take()
	}
}

func (p *parser) header() {
	if p.kind() != "KW_WARDLEY" {
		p.unexpected("KW_WARDLEY")
		return
	}
	p.out.Header = p.take()
}

func (p *parser) statements() {
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
			p.statement()
		}
	}
}

func (p *parser) statement() {
	first := p.token()
	parse, known := statementParsers[first.Kind]
	if !known {
		p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(p.lineEnd(), first.Span.End)})
		p.skipLine()
		return
	}
	base := len(p.openers)
	ok := parse(p)
	p.openers = p.openers[:base]
	if !ok {
		p.skipLine()
	}
}

func (p *parser) eol(expected ...string) bool {
	switch p.kind() {
	case "NEWLINE":
		p.skipNewlines()
		return true
	case "EOF":
		return true
	}
	p.unexpected(append(slices.Clone(expected), "EOF", "NEWLINE")...)
	return false
}

func value(t Token) Value { return Value{Text: t.Text, Span: t.Span} }

func (p *parser) field(into *Value, kinds ...string) bool {
	if !slices.Contains(kinds, p.kind()) {
		p.unexpected(kinds...)
		return false
	}
	*into = value(p.take())
	return true
}

func (p *parser) name(into *Value, extra ...string) bool {
	return p.field(into, append(slices.Clone(extra), nameKinds...)...)
}

func (p *parser) punct(kind string) bool {
	if p.kind() != kind {
		p.unexpected(kind)
		return false
	}
	p.take()
	return true
}

func (p *parser) opener(kind string) bool {
	if p.kind() != kind {
		p.unexpected(kind)
		return false
	}
	p.openers = append(p.openers, p.take())
	return true
}

func (p *parser) closer(kind string) bool {
	if !p.punct(kind) {
		return false
	}
	p.openers = p.openers[:len(p.openers)-1]
	return true
}

func (p *parser) pair(x, y *Value, kinds []string) bool {
	return p.opener("[") && p.field(x, kinds...) && p.punct(",") && p.field(y, kinds...) && p.closer("]")
}

func (p *parser) namedPoint(name, visibility, evolution *Value) bool {
	return p.name(name) && p.pair(visibility, evolution, decimal)
}

func (p *parser) sizeBody(node *Size) bool {
	return p.opener("[") && p.field(&node.Width, integer...) && p.punct(",") && p.field(&node.Height, integer...) && p.closer("]")
}

func (p *parser) size() bool {
	start := p.take().Span.Start
	var node Size
	if !p.sizeBody(&node) {
		return false
	}
	node.Span = p.span(start)
	p.out.Size = &node
	return p.eol()
}

func (p *parser) evolution() bool {
	start := p.take().Span.Start
	var node Evolution
	for {
		stage, follow, ok := p.stage()
		if !ok {
			return false
		}
		node.Stages = append(node.Stages, stage)
		if p.kind() != "ARROW" {
			return p.finishEvolution(&node, start, follow)
		}
		p.take()
	}
}

func (p *parser) finishEvolution(node *Evolution, start int, follow []string) bool {
	if len(node.Stages) < 2 {
		p.unexpected(append(slices.Clone(follow), "ARROW")...)
		return false
	}
	node.Span = p.span(start)
	p.out.Evolution = node
	return p.eol(append(slices.Clone(follow), "ARROW")...)
}

func (p *parser) stage() (EvolutionStage, []string, bool) {
	var stage EvolutionStage
	if !p.name(&stage.Name) {
		return stage, nil, false
	}
	follow := []string{"@", "/"}
	if p.kind() == "@" {
		p.take()
		var boundary Value
		if !p.field(&boundary, decimal...) {
			return stage, nil, false
		}
		stage.Boundary, follow = &boundary, follow[1:]
	}
	if p.kind() == "/" {
		p.take()
		var second Value
		if !p.name(&second) {
			return stage, nil, false
		}
		stage.SecondName, follow = &second, nil
	}
	stage.Span = source.Span{Start: stage.Name.Span.Start, End: p.tokens[p.at-1].Span.End}
	return stage, follow, true
}

func (p *parser) anchor() bool {
	start := p.take().Span.Start
	var node Anchor
	if !p.namedPoint(&node.Name, &node.Visibility, &node.Evolution) {
		return false
	}
	node.Span = p.span(start)
	p.out.Anchors = append(p.out.Anchors, node)
	return p.eol()
}

func (p *parser) label() (*Label, bool) {
	start := p.take().Span.Start
	var node Label
	if !p.opener("[") || !p.signed(&node.NegX, &node.OffsetX) || !p.punct(",") || !p.signed(&node.NegY, &node.OffsetY) || !p.closer("]") {
		return nil, false
	}
	node.Span = p.span(start)
	return &node, true
}

func (p *parser) signed(negative *bool, into *Value) bool {
	if p.kind() == "-" {
		p.take()
		*negative = true
	}
	return p.field(into, integer...)
}

func (p *parser) component() bool {
	start := p.take().Span.Start
	var node Component
	if !p.namedPoint(&node.Name, &node.Visibility, &node.Evolution) {
		return false
	}
	follow, ok := p.componentTail(&node)
	if !ok {
		return false
	}
	node.Span = p.span(start)
	p.out.Components = append(p.out.Components, node)
	return p.eol(follow...)
}

func (p *parser) componentTail(node *Component) ([]string, bool) {
	follow := []string{"(", "KW_INERTIA", "KW_LABEL"}
	if p.kind() == "KW_LABEL" {
		label, ok := p.label()
		if !ok {
			return nil, false
		}
		node.Label, follow = label, follow[:2]
	}
	if p.kind() == "(" && p.peekKind(1) != "KW_INERTIA" {
		decorator, ok := p.decorator()
		if !ok {
			return nil, false
		}
		node.Decorator = decorator
	}
	switch p.kind() {
	case "KW_INERTIA":
		p.take()
		node.Inertia = true
		return nil, true
	case "(":
		node.Inertia = true
		return nil, p.inertiaGroup()
	}
	return follow, true
}

func (p *parser) decorator() (*Decorator, bool) {
	start := p.token().Span.Start
	var node Decorator
	matched := p.opener("(") && p.field(&node.Strategy, "STRATEGY") && p.closer(")")
	if !matched {
		return nil, false
	}
	node.Span = p.span(start)
	return &node, true
}

func (p *parser) inertiaGroup() bool {
	return p.opener("(") && p.punct("KW_INERTIA") && p.closer(")")
}

func (p *parser) link() bool {
	start := p.token().Span.Start
	var node Link
	p.name(&node.From)
	follow := []string{"ARROW", "LINK_ARROW", "LINK_PORT"}
	if p.kind() == "LINK_PORT" {
		port := value(p.take())
		node.FromPort, follow = &port, follow[:2]
	}
	if k := p.kind(); k == "LINK_ARROW" || k == "ARROW" {
		arrow := value(p.take())
		node.Arrow, follow = &arrow, nil
	}
	if !p.name(&node.To, follow...) {
		return false
	}
	trailing := []string{"LINK_LABEL", "LINK_PORT"}
	if p.kind() == "LINK_PORT" {
		port := value(p.take())
		node.ToPort, trailing = &port, trailing[:1]
	}
	if p.kind() == "LINK_LABEL" {
		label := value(p.take())
		node.LinkLabel, trailing = &label, nil
	}
	node.Span = p.span(start)
	p.out.Links = append(p.out.Links, node)
	return p.eol(trailing...)
}

func (p *parser) evolve() bool {
	start := p.take().Span.Start
	var node Evolve
	matched := p.name(&node.Component) && p.field(&node.Target, decimal...)
	if !matched {
		return false
	}
	node.Span = p.span(start)
	p.out.Evolves = append(p.out.Evolves, node)
	return p.eol()
}

func (p *parser) pipeline() bool {
	start := p.take().Span.Start
	var node Pipeline
	opened := p.name(&node.Parent) && p.opener("{")
	if !opened {
		return false
	}
	if p.kind() != "NEWLINE" {
		p.unexpected("NEWLINE")
		return false
	}
	p.skipNewlines()
	if !p.members(&node) {
		return false
	}
	if len(node.Components) == 0 {
		p.unexpected("KW_COMPONENT")
		return false
	}
	p.closer("}")
	node.Span = p.span(start)
	p.out.Pipelines = append(p.out.Pipelines, node)
	return p.eol()
}

func (p *parser) members(node *Pipeline) bool {
	for {
		switch p.kind() {
		case "}":
			return true
		case "NEWLINE":
			p.take()
		case "KW_COMPONENT":
			if !p.member(node) {
				return false
			}
		default:
			p.unexpected("KW_COMPONENT", "}")
			if k := p.kind(); k == "EOF" || k == "UNTERMINATED" {
				return false
			}
			p.skipMemberLine()
		}
	}
}

func (p *parser) member(node *Pipeline) bool {
	base := len(p.openers)
	child, ok := p.pipelineComponent()
	p.openers = p.openers[:base]
	if ok {
		node.Components = append(node.Components, child)
		return true
	}
	if k := p.kind(); k == "EOF" || k == "UNTERMINATED" {
		return false
	}
	p.skipMemberLine()
	return true
}

func (p *parser) pipelineComponent() (PipelineComponent, bool) {
	start := p.take().Span.Start
	var node PipelineComponent
	matched := p.name(&node.Name) && p.opener("[") && p.field(&node.Evolution, decimal...) && p.closer("]")
	if !matched {
		return node, false
	}
	follow := []string{"KW_LABEL"}
	if p.kind() == "KW_LABEL" {
		label, ok := p.label()
		if !ok {
			return node, false
		}
		node.Label, follow = label, nil
	}
	node.Span = p.span(start)
	return node, p.eol(follow...)
}

func (p *parser) note() bool {
	start := p.take().Span.Start
	var node Note
	matched := p.field(&node.Text, "STRING") && p.pair(&node.Visibility, &node.Evolution, decimal)
	if !matched {
		return false
	}
	node.Span = p.span(start)
	p.out.Notes = append(p.out.Notes, node)
	return p.eol()
}

func (p *parser) annotations() bool {
	start := p.take().Span.Start
	var node Annotations
	if !p.pair(&node.X, &node.Y, coordinate) {
		return false
	}
	node.Span = p.span(start)
	p.out.Annotations = append(p.out.Annotations, node)
	return p.eol()
}

func (p *parser) annotation() bool {
	start := p.take().Span.Start
	var node Annotation
	matched := p.field(&node.Number, integer...) && p.punct(",") && p.pair(&node.X, &node.Y, coordinate) && p.field(&node.Text, "STRING")
	if !matched {
		return false
	}
	node.Span = p.span(start)
	p.out.Annotation = append(p.out.Annotation, node)
	return p.eol()
}

func (p *parser) forceStatement() (Accelerator, bool) {
	start := p.take().Span.Start
	var node Accelerator
	if !p.namedPoint(&node.Name, &node.X, &node.Y) {
		return node, false
	}
	node.Span = p.span(start)
	return node, true
}

func (p *parser) accelerator() bool {
	node, ok := p.forceStatement()
	if !ok {
		return false
	}
	p.out.Accelerators = append(p.out.Accelerators, node)
	return p.eol()
}

func (p *parser) deaccelerator() bool {
	node, ok := p.forceStatement()
	if !ok {
		return false
	}
	p.out.Deaccelerators = append(p.out.Deaccelerators, Deaccelerator(node))
	return p.eol()
}

func (p *parser) metadata() bool {
	token := p.take()
	p.out.Metadata = append(p.out.Metadata, Metadata{Field: metadataFields[token.Kind], Value: token.Text, Span: token.Span})
	return p.eol()
}
