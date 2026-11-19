package math

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Parsed struct {
	Source      string
	Expression  *Expr
	Diagnostics []diag.Diagnostic
}

type Kind uint8

const (
	KindLiteral Kind = iota
	KindRow
	KindGroup
	KindGlyph
	KindLimit
	KindSymbol
	KindFraction
	KindScripts
	KindRadical
	KindDelimited
	KindStyled
	KindText
	KindSpace
)

type Font uint8

const (
	FontRoman Font = iota
	FontItalic
	FontBold
)

type SymbolClass uint8

const (
	ClassGreek SymbolClass = iota
	ClassOrdinary
	ClassBinary
	ClassRelation
	ClassSum
	ClassProduct
	ClassIntegral
)

type Space uint8

const (
	SpaceThin Space = iota
	SpaceMedium
	SpaceQuad
)

type Delimiter uint8

const (
	DelimLeftParen Delimiter = iota
	DelimRightParen
	DelimLeftBracket
	DelimRightBracket
	DelimLeftBrace
	DelimRightBrace
	DelimBar
	DelimInvisible
)

type Expr struct {
	Span        source.Span
	Kind        Kind
	Literal     string
	Command     string
	Char        rune
	Font        Font
	Class       SymbolClass
	Space       Space
	Left        Delimiter
	Right       Delimiter
	Children    []*Expr
	Body        *Expr
	Numerator   *Expr
	Denominator *Expr
	Base        *Expr
	Superscript *Expr
	Subscript   *Expr
	Index       *Expr
	Radicand    *Expr
}
