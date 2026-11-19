package railroad

import "github.com/gosuda/elegant-mermaid/internal/source"

type Notation uint8

const (
	Constructor Notation = iota
	EBNF
	ABNF
	PEG
)

func (n Notation) String() string {
	return [...]string{"railroad", "railroad-ebnf", "railroad-abnf", "railroad-peg"}[n]
}

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Value struct {
	Span source.Span
	Text string
}

type MetaKind uint8

const (
	MetaTitle MetaKind = iota
	MetaAccTitle
	MetaAccDescr
)

type Meta struct {
	Span  source.Span
	Kind  MetaKind
	Value string
}

type Start struct {
	Span     source.Span
	Header   Token
	Notation Notation
	Meta     []Meta
	Rules    []Rule
}

type Rule struct {
	Span  source.Span
	Index int
	Name  Value
	Body  Expression
}

type Expression interface {
	expression()
}

type RailroadSequenceExpr struct {
	Span     source.Span
	Elements []Expression
}

type RailroadChoiceExpr struct {
	Span         source.Span
	Alternatives []Expression
}

type RailroadOptionalExpr struct {
	Span    source.Span
	Element Expression
}

type RailroadOneOrMoreExpr struct {
	Span    source.Span
	Element Expression
}

type RailroadZeroOrMoreExpr struct {
	Span    source.Span
	Element Expression
}

type RailroadTerminalExpr struct {
	Span  source.Span
	Value Value
}

type RailroadNonTerminalExpr struct {
	Span source.Span
	Name Value
}

type RailroadSpecialExpr struct {
	Span source.Span
	Text Value
}

type EbnfChoice struct {
	Span         source.Span
	Alternatives []EbnfSequence
}

type EbnfSequence struct {
	Span     source.Span
	Elements []EbnfTerm
}

type EbnfTerm struct {
	Span      source.Span
	Base      EbnfPrimary
	Postfixes []EbnfPostfix
}

type EbnfPrimary interface {
	ebnfPrimary()
}

type EbnfPostfix interface {
	ebnfPostfix()
}

type EbnfTerminal struct {
	Span  source.Span
	Value Value
}

type EbnfNonTerminal struct {
	Span source.Span
	Name Value
}

type EbnfSpecial struct {
	Span source.Span
	Text Value
}

type EbnfGroup struct {
	Span    source.Span
	Element *EbnfChoice
}

type EbnfOptional struct {
	Span    source.Span
	Element *EbnfChoice
}

type EbnfRepetition struct {
	Span    source.Span
	Element *EbnfChoice
}

type EbnfOptionalPostfix struct{ Span source.Span }

type EbnfZeroOrMorePostfix struct{ Span source.Span }

type EbnfOneOrMorePostfix struct{ Span source.Span }

type EbnfExceptionPostfix struct {
	Span   source.Span
	Except EbnfPrimary
}

type AbnfAlternation struct {
	Span         source.Span
	Alternatives []AbnfConcatenation
}

type AbnfConcatenation struct {
	Span     source.Span
	Elements []AbnfElement
}

type AbnfElement struct {
	Span    source.Span
	Repeat  *Token
	Primary AbnfPrimary
}

type AbnfPrimary interface {
	abnfPrimary()
}

type AbnfStringLiteral struct {
	Span  source.Span
	Value Value
}

type AbnfNumVal struct {
	Span  source.Span
	Value Value
}

type AbnfRuleName struct {
	Span source.Span
	Name Value
}

type AbnfGroup struct {
	Span    source.Span
	Element *AbnfAlternation
}

type AbnfOptionalGroup struct {
	Span    source.Span
	Element *AbnfAlternation
}

type PegOrderedChoice struct {
	Span         source.Span
	Alternatives []PegSequence
}

type PegSequence struct {
	Span     source.Span
	Elements []PegPrefix
}

type PegPrefix struct {
	Span     source.Span
	Operator *Token
	Suffix   PegSuffix
}

type PegSuffix struct {
	Span     source.Span
	Primary  PegPrimary
	Operator *Token
}

type PegPrimary interface {
	pegPrimary()
}

type PegLiteral struct {
	Span  source.Span
	Value Value
}

type PegIdentifier struct {
	Span source.Span
	Name Value
}

type PegGroup struct {
	Span    source.Span
	Element *PegOrderedChoice
}

type PegAny struct{ Span source.Span }

func (*RailroadSequenceExpr) expression()    {}
func (*RailroadChoiceExpr) expression()      {}
func (*RailroadOptionalExpr) expression()    {}
func (*RailroadOneOrMoreExpr) expression()   {}
func (*RailroadZeroOrMoreExpr) expression()  {}
func (*RailroadTerminalExpr) expression()    {}
func (*RailroadNonTerminalExpr) expression() {}
func (*RailroadSpecialExpr) expression()     {}
func (*EbnfChoice) expression()              {}
func (*AbnfAlternation) expression()         {}
func (*PegOrderedChoice) expression()        {}

func (*EbnfTerminal) ebnfPrimary()    {}
func (*EbnfNonTerminal) ebnfPrimary() {}
func (*EbnfSpecial) ebnfPrimary()     {}
func (*EbnfGroup) ebnfPrimary()       {}
func (*EbnfOptional) ebnfPrimary()    {}
func (*EbnfRepetition) ebnfPrimary()  {}

func (*EbnfOptionalPostfix) ebnfPostfix()   {}
func (*EbnfZeroOrMorePostfix) ebnfPostfix() {}
func (*EbnfOneOrMorePostfix) ebnfPostfix()  {}
func (*EbnfExceptionPostfix) ebnfPostfix()  {}

func (*AbnfStringLiteral) abnfPrimary() {}
func (*AbnfNumVal) abnfPrimary()        {}
func (*AbnfRuleName) abnfPrimary()      {}
func (*AbnfGroup) abnfPrimary()         {}
func (*AbnfOptionalGroup) abnfPrimary() {}

func (*PegLiteral) pegPrimary()    {}
func (*PegIdentifier) pegPrimary() {}
func (*PegGroup) pegPrimary()      {}
func (*PegAny) pegPrimary()        {}
