package er

import "github.com/gosuda/elegant-mermaid/internal/source"

type Start struct {
	Span     source.Span
	Header   Token
	Document Document
}

type Document struct {
	Span  source.Span
	Lines []Line
}

type Line struct {
	Span      source.Span
	Statement *Statement
}

type StatementKind uint8

const (
	KindEntity StatementKind = iota
	KindRelationship
	KindAccessibility
	KindDirection
	KindClassDef
	KindClass
	KindStyle
	KindSubgraph
)

type Statement struct {
	Span          source.Span
	Kind          StatementKind
	Entity        *EntityStatement
	Relationship  *RelationshipStatement
	Accessibility AccessibilityStatement
	Direction     Direction
	ClassDef      *ClassDefStatement
	Class         *ClassStatement
	Style         *StyleStatement
	Subgraph      *SubgraphStatement
}

type EntityStatement struct {
	Name       EntityName
	Alias      *EntityName
	Classes    *IdList
	Attributes *Attributes
	Delimiters *[2]source.Span
}

type RelationshipStatement struct {
	From        EntityName
	FromClasses *IdList
	Relation    RelSpec
	To          EntityName
	ToClasses   *IdList
	Role        Role
}

type AccessibilityStatement struct {
	Title bool
	Value Token
}

type Direction struct {
	Span  source.Span
	Value string
}

type ClassDefStatement struct {
	Span   source.Span
	IDs    IdList
	Styles StylesOpt
}

type ClassStatement struct {
	Span    source.Span
	Targets IdList
	Classes IdList
}

type StyleStatement struct {
	Span    source.Span
	Targets IdList
	Styles  StylesOpt
}

type IdList struct {
	Span  source.Span
	Names []Token
}

type StylesOpt struct {
	Span   source.Span
	Styles []Style
}

type Style struct {
	Span       source.Span
	Components []Token
}

type SubgraphStatement struct {
	Header   SubgraphHeader
	Document Document
	Close    Token
}

type SubgraphHeader struct {
	Span  source.Span
	ID    EntityName
	Title *SubgraphTitle
}

type SubgraphTitle struct {
	Span  source.Span
	Parts []EntityName
}

type EntityName struct {
	Span source.Span
	Name string
}

type Attributes struct {
	Span       source.Span
	Attributes []Attribute
}

type Attribute struct {
	Span          source.Span
	AttributeType AttributeType
	Name          AttributeName
	Keys          *AttributeKeyTypeList
	Comment       *AttributeComment
}

type AttributeType struct {
	Span     source.Span
	Word     Token
	Question *Token
}

type AttributeName struct {
	Span source.Span
	Word Token
}

type AttributeKeyTypeList struct {
	Span source.Span
	Keys []AttributeKeyType
}

type AttributeKeyType struct {
	Span  source.Span
	Token Token
	Value string
}

type AttributeComment struct {
	Span source.Span
	Text string
}

type RelSpec struct {
	Span    source.Span
	Left    Cardinality
	RelType RelType
	Right   Cardinality
}

type Cardinality struct {
	Span  source.Span
	Kind  CardinalityKind
	Token Token
}

type CardinalityKind uint8

const (
	CardZeroOrOne CardinalityKind = iota
	CardZeroOrMore
	CardOneOrMore
	CardOnlyOne
	CardMdParent
)

type RelType struct {
	Span        source.Span
	Identifying bool
	Token       Token
}

type Role struct {
	Span  source.Span
	Label string
	Token Token
}
