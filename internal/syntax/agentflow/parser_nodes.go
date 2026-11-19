package agentflow

import (
	"sort"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func (p *parser) id() *IdString {
	start := p.position()
	var tokens []Token
	for idKind(p.kind()) {
		if t := p.take(); t != nil {
			tokens = append(tokens, *t)
		} else {
			return nil
		}
	}
	if len(tokens) == 0 {
		p.unexpected("AMP, BRKT, COLON, COMMA, DEFAULT, DOWN, MINUS, MULT, NODE_STRING, NUM, UNICODE_TEXT")
		return nil
	}
	return &IdString{Span: p.span(start), Tokens: tokens}
}

func (p *parser) vertexStatement() *VertexStatement {
	start := p.position()
	first := p.node()
	if first == nil {
		return nil
	}
	nodes := []Node{*first}
	var links []Link
	p.spaces()
	for p.kind() == "LINK" || p.kind() == "LINK_ID" || p.kind() == "START_LINK" {
		link := p.link()
		if link == nil {
			return nil
		}
		links = append(links, *link)
		p.spaces()
		next := p.node()
		if next == nil {
			return nil
		}
		nodes = append(nodes, *next)
		p.spaces()
	}
	return &VertexStatement{Span: p.span(start), Nodes: nodes, Links: links}
}

func (p *parser) node() *Node {
	start := p.position()
	first := p.styledVertex()
	if first == nil {
		return nil
	}
	vertices := []StyledVertex{*first}
	for {
		spaces := p.spaces()
		if spaces == 0 || p.kind() != "AMP" {
			break
		}
		p.at++
		if p.spaces() == 0 {
			p.unexpected("SPACE")
			return nil
		}
		next := p.styledVertex()
		if next == nil {
			return nil
		}
		vertices = append(vertices, *next)
	}
	return &Node{Span: p.span(start), Vertices: vertices}
}

func (p *parser) styledVertex() *StyledVertex {
	vertex := p.vertex()
	if vertex == nil {
		return nil
	}
	start := vertex.Span.Start
	var class *IdString
	if p.kind() == "STYLE_SEPARATOR" {
		p.at++
		class = p.id()
		if class == nil {
			return nil
		}
	}
	metadata, ok := p.metadata()
	if !ok {
		return nil
	}
	return &StyledVertex{Span: p.span(start), Vertex: *vertex, Class: class, Metadata: metadata}
}

func (p *parser) vertex() *Vertex {
	id := p.id()
	if id == nil {
		return nil
	}
	start := id.Span.Start
	result := Vertex{Span: id.Span, ID: *id}
	switch {
	case p.kind() == "VERTEX_WITH_PROPS_START":
		if !p.vertexProperties(&result) {
			return nil
		}
	case opener(p.kind()) != "":
		label, shape, delimiters, ok := p.bracketShape()
		if !ok {
			return nil
		}
		result.Shape = shape
		result.Label = label
		result.Delimiters = delimiters
	}
	result.Span = p.span(start)
	return &result
}

func (p *parser) vertexProperties(result *Vertex) bool {
	open := p.take()
	key, colon := p.requireThen("NODE_STRING", "COLON")
	value, pipe := p.requireThen("NODE_STRING", "PIPE")
	if open == nil {
		return false
	}
	var label *Text
	if colon && pipe {
		label = p.labelText(open)
	}
	close := p.close(open, "SQE")
	if label == nil || close == nil {
		return false
	}
	result.Label = label
	result.Shape = "rect"
	result.Property = &[2]Token{*key, *value}
	result.Delimiters = &[2]source.Span{open.Span, close.Span}
	return true
}

func (p *parser) requireThen(kind, next string) (*Token, bool) {
	token := p.require(kind)
	if token == nil {
		return nil, false
	}
	return token, p.require(next) != nil
}

func (p *parser) bracketText() (*Text, string, [2]source.Span) {
	open := p.take()
	if open == nil {
		return nil, "", [2]source.Span{}
	}
	shape, closeKind := opener(open.Kind), closeFor(open.Kind)
	closers := 1
	if p.doubledOpen(open) {
		p.at++
		shape = doubledShape(open.Kind)
		closers = 2
	}
	label := p.labelText(open)
	if label == nil {
		return nil, "", [2]source.Span{}
	}
	if open.Kind == "TRAPSTART" || open.Kind == "INVTRAPSTART" {
		shape, closeKind = trapShape(open.Kind, p.kind())
	}
	close := p.closeRun(open, closeKind, closers)
	if close == nil {
		return nil, "", [2]source.Span{}
	}
	return label, shape, [2]source.Span{open.Span, close.Span}
}

func (p *parser) doubledOpen(open *Token) bool {
	return (open.Kind == "PS" || open.Kind == "DIAMOND_START") && p.kind() == open.Kind
}

func doubledShape(kind string) string {
	if kind == "PS" {
		return "circle"
	}
	return "hexagon"
}

func (p *parser) closeRun(open *Token, kind string, count int) *Token {
	var close *Token
	for range count {
		if close = p.close(open, kind); close == nil {
			return nil
		}
	}
	return close
}

func (p *parser) bracketShape() (*Text, string, *[2]source.Span, bool) {
	text, shape, delimiters := p.bracketText()
	if text == nil {
		return nil, "", nil, false
	}
	return text, shape, &delimiters, true
}

func (p *parser) labelText(open *Token) *Text {
	if p.kind() == "EOF" || p.kind() == "UNTERMINATED" {
		p.close(open, "")
		return nil
	}
	return p.text([]string{"TEXT", "TAGSTART", "TAGEND", "UNICODE_TEXT"})
}

func (p *parser) close(open *Token, kind string) *Token {
	if p.kind() == "UNTERMINATED" {
		token := p.take()
		if token == nil {
			return nil
		}
		quoted := strings.HasPrefix(cutAt(p.source, token.Span.Start), "\"")
		span := open.Span
		if quoted {
			span = token.Span
		}
		p.unterminated(span)
		return nil
	}
	if p.kind() == "EOF" {
		p.unterminated(open.Span)
		return nil
	}
	return p.require(kind)
}

func (p *parser) text(accepted []string) *Text {
	start := p.position()
	if p.kind() == "STR" || p.kind() == "MD_STR" {
		t := p.take()
		if t == nil {
			return nil
		}
		return &Text{Span: t.Span, Kind: textKind(t.Kind), Pieces: []Token{*t}}
	}
	var pieces []Token
	for contains(accepted, p.kind()) {
		if t := p.take(); t != nil {
			pieces = append(pieces, *t)
		} else {
			return nil
		}
	}
	if len(pieces) == 0 {
		expected := append([]string{}, accepted...)
		expected = append(expected, "MD_STR", "STR")
		sortStrings(expected)
		p.unexpected(strings.Join(expected, ", "))
		return nil
	}
	return &Text{Span: p.span(start), Pieces: pieces, Kind: TextPlain}
}

func (p *parser) metadata() ([]ShapeData, bool) {
	var data []ShapeData
	for {
		beforeSpaces := p.at
		p.spaces()
		if p.kind() != "SHAPE_DATA" {
			p.at = beforeSpaces
			return data, true
		}
		start := p.position()
		pieces := []Token{*p.take()}
		for p.kind() == "SHAPE_DATA" && p.at < len(p.tokens) && p.tokens[p.at].Text != "" {
			pieces = append(pieces, *p.take())
		}
		if p.kind() == "UNTERMINATED" {
			p.unexpected("")
			return nil, false
		}
		span := p.span(start)
		valueStart := start + 2
		valueEnd := span.End - 1
		if valueEnd < valueStart {
			valueEnd = valueStart
		}
		value := ""
		if valueStart <= len(p.source) {
			value = p.sliceText(source.Span{Start: valueStart, End: valueEnd})
		}
		data = append(data, ShapeData{Span: span, Pieces: pieces, Value: value})
	}
}

type bracketSpec struct {
	shape   string
	closing string
}

var bracketSpecs = map[string]bracketSpec{
	"SQS":               {"square", "SQE"},
	"DOUBLECIRCLESTART": {"doublecircle", "DOUBLECIRCLEEND"},
	"PS":                {"round", "PE"},
	"(-":                {"ellipse", "-)"},
	"STADIUMSTART":      {"stadium", "STADIUMEND"},
	"SUBROUTINESTART":   {"subroutine", "SUBROUTINEEND"},
	"CYLINDERSTART":     {"cylinder", "CYLINDEREND"},
	"DIAMOND_START":     {"diamond", "DIAMOND_STOP"},
	"TAGEND":            {"odd", "SQE"},
	"TRAPSTART":         {"trapezoid", "TRAPEND"},
	"INVTRAPSTART":      {"inv_trapezoid", "TRAPEND"},
}

func opener(kind string) string {
	return bracketSpecs[kind].shape
}

func closeFor(kind string) string {
	return bracketSpecs[kind].closing
}

func trapShape(open, close string) (string, string) {
	switch {
	case open == "TRAPSTART" && close == "INVTRAPEND":
		return "lean_right", close
	case open == "INVTRAPSTART" && close == "TRAPEND":
		return "lean_left", close
	case open == "INVTRAPSTART":
		return "inv_trapezoid", "INVTRAPEND"
	default:
		return "trapezoid", "TRAPEND"
	}
}

func contains(values []string, value string) bool {
	for _, v := range values {
		if v == value {
			return true
		}
	}
	return false
}

func sortStrings(values []string) { sort.Strings(values) }
