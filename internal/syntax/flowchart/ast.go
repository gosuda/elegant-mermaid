package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type File struct {
	Config GraphConfig
	Doc    Document
	Span   source.Span
}

type GraphConfig struct {
	Keyword   Token
	Direction *Token
	Span      source.Span
}

type Document struct {
	Lines []Line
	Span  source.Span
}

type Line struct {
	Stmt Stmt
}

type Stmt interface {
	Bounds() source.Span
}

type node struct {
	Span source.Span
}

func (n node) Bounds() source.Span { return n.Span }

type LabelKind uint8

const (
	LabelPlain LabelKind = iota

	LabelString

	LabelMarkdown
)

type Text struct {
	Tokens []Token
	Kind   LabelKind
	Span   source.Span
}

func (t Text) String() string {
	var sb strings.Builder
	for _, tok := range t.Tokens {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

func (t Text) Quoted() bool { return t.Kind != LabelPlain }

type IdString struct {
	Tokens []Token
	Span   source.Span
}

func (s IdString) String() string {
	var sb strings.Builder
	for _, tok := range s.Tokens {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

type Vertex struct {
	ID    IdString
	Shape string
	Text  Text
	Label bool
	Span  source.Span
}

type StyledVertex struct {
	Vertex    Vertex
	Class     *IdString
	ShapeData *ShapeData
	Span      source.Span
}

type NodeGroup struct {
	Vertices []StyledVertex
	Span     source.Span
}

type LinkStatement struct {
	ID   *IdString
	Open Token
	End  *Token
	Span source.Span
}

type EdgeText struct {
	Text Text
	Span source.Span
}

type ArrowText struct {
	Text Text
	Span source.Span
}

type Link struct {
	Statement LinkStatement
	Edge      *EdgeText
	Arrow     *ArrowText
	Span      source.Span
}

type VertexStatement struct {
	node
	Groups []NodeGroup
	Links  []Link
}

type ShapeData struct {
	Tokens []Token
	Span   source.Span
}

func (d *ShapeData) Body() string {
	var sb strings.Builder
	for _, tok := range d.Tokens {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

type Subgraph struct {
	node
	Keyword   Token
	ID        *TextNoTags
	Title     *Text
	Direction *DirectionStatement
	Body      []Line
	End       Token
}

type TextNoTags struct {
	Tokens []Token
	Span   source.Span
}

func (t TextNoTags) String() string {
	var sb strings.Builder
	for _, tok := range t.Tokens {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

type StyleStatement struct {
	node
	Keyword Token
	Targets []IdString
	Styles  StylesOpt
}

type ClassDefStatement struct {
	node
	Keyword Token
	Names   []IdString
	Styles  StylesOpt
}

type ClassStatement struct {
	node
	Keyword Token
	Targets []IdString
	Class   IdString
}

type LinkStyleStatement struct {
	node
	Keyword       Token
	Default       bool
	Indices       NumList
	Interpolation *AlphaNum
	Styles        *StylesOpt
}

type NumList struct {
	Numbers []Token
	Span    source.Span
}

type StylesOpt struct {
	Styles []Style
	Span   source.Span
}

type Style struct {
	Components []Token
	Span       source.Span
}

func (s Style) Text() string {
	var sb strings.Builder
	for _, tok := range s.Components {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

type AlphaNum struct {
	Tokens []Token
	Span   source.Span
}

func (a AlphaNum) String() string {
	var sb strings.Builder
	for _, tok := range a.Tokens {
		sb.WriteString(tok.Text)
	}
	return sb.String()
}

type ClickStatement struct {
	node
	Keyword  Token
	Target   IdString
	Callback *CallbackAction
	Link     *LinkAction
}

type CallbackAction struct {
	Name  Token
	Args  *Token
	Extra *Token
	Span  source.Span
}

type LinkAction struct {
	Href   *Token
	URL    Text
	Tip    *Text
	Target *Token
	Span   source.Span
}

type DirectionStatement struct {
	node
	Keyword Token
	Value   Token
}

type AccTitle struct {
	node
	Keyword Token
	Value   Token
}

type AccDescr struct {
	node
	Keyword Token
	Value   Token
}

type AccDescrBlock struct {
	node
	Value Token
}

type EmptyStatement struct {
	node
}

func shapeByOpener(k TokenKind) string {
	switch k {
	case TokSQS:
		return "squareRect"
	case TokPS:
		return "roundedRect"
	case TokDiamondStart:
		return "diamond"
	case TokTagEnd:
		return "odd"
	case TokTrapStart:
		return "trapezoid"
	case TokInvTrapStart:
		return "inv_trapezoid"
	case TokVertexWithPropsStart:
		return "rect"
	}
	return compoundShapeByOpener(k)
}

func compoundShapeByOpener(k TokenKind) string {
	switch k {
	case TokDoubleCircleStart:
		return "doublecircle"
	case TokEllipseStart:
		return "ellipse"
	case TokStadiumStart:
		return "stadium"
	case TokSubroutineStart:
		return "subroutine"
	case TokCylinderStart:
		return "cylinder"
	}
	return ""
}

func closerByOpener(k TokenKind) (TokenKind, TokenKind) {
	switch k {
	case TokSQS, TokTagEnd, TokVertexWithPropsStart:
		return TokSQE, TokNone
	case TokPS:
		return TokPE, TokNone
	case TokDiamondStart:
		return TokDiamondStop, TokNone
	case TokTrapStart:
		return TokTrapEnd, TokInvTrapEnd
	case TokInvTrapStart:
		return TokInvTrapEnd, TokTrapEnd
	}
	return compoundCloserByOpener(k), TokNone
}

func compoundCloserByOpener(k TokenKind) TokenKind {
	switch k {
	case TokDoubleCircleStart:
		return TokDoubleCircleEnd
	case TokEllipseStart:
		return TokEllipseEnd
	case TokStadiumStart:
		return TokStadiumEnd
	case TokSubroutineStart:
		return TokSubroutineEnd
	case TokCylinderStart:
		return TokCylinderEnd
	}
	return TokNone
}

func isLabelOpener(k TokenKind) bool {
	return shapeByOpener(k) != ""
}

func isIDToken(k TokenKind) bool {
	switch k {
	case TokNum, TokNodeString, TokDown, TokMinus, TokDefault, TokComma, TokColon,
		TokAmp, TokBrkt, TokMult, TokUnicodeText:
		return true
	}
	return false
}

func isTextToken(k TokenKind) bool {
	switch k {
	case TokText, TokTagStart, TokTagEnd, TokUnicodeText:
		return true
	}
	return false
}

func isTextNoTagsToken(k TokenKind) bool {
	if isIDToken(k) || isTextToken(k) {
		return true
	}
	switch k {
	case TokSpace, TokStyle, TokLinkStyle, TokClassDef, TokClass, TokClick, TokUp,
		TokSubgraph, TokEnd, TokGraph, TokDir, TokDirectionTB, TokDirectionBT,
		TokDirectionRL, TokDirectionLR, TokDirectionTD, TokStartLink:
		return true
	}
	return false
}

func isAlphaNumToken(k TokenKind) bool {
	switch k {
	case TokNum, TokUnicodeText, TokNodeString, TokDir, TokDown, TokMinus, TokComma,
		TokColon, TokAmp, TokBrkt, TokMult:
		return true
	}
	return false
}
