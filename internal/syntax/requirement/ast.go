package requirement

import "github.com/gosuda/elegant-mermaid/internal/source"

type Start struct {
	Span       source.Span
	Header     Token
	Diagram    Diagram
	Directives []Directive
}

type Diagram struct {
	Span       source.Span
	Statements []Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind struct {
	Kind         string
	Requirement  *RequirementDef
	Element      *ElementDef
	Relationship *RelationshipDef
	Directive    *Directive
	Direction    Direction
	ClassDef     *ClassDefStatement
	Class        *ClassStatement
	Style        *StyleStatement
}

type Directive struct {
	Span      source.Span
	Title     bool
	Multiline bool
	Value     Token
}

type Direction struct {
	Span  source.Span
	Value string
}

type RequirementDef struct {
	Span            source.Span
	RequirementType RequirementType
	Name            RequirementName
	Classes         *IdList
	Body            RequirementBody
	Delimiters      [2]source.Span
}

type RequirementBody struct {
	Span   source.Span
	Fields []RequirementField
}

type RequirementField struct {
	Span    source.Span
	Keyword Token
	Colon   source.Span
	Value   RequirementFieldValue
}

type RequirementFieldValue struct {
	Kind   string
	Id     Id
	Text   Text
	Risk   RiskLevel
	Verify VerifyType
}

type RequirementType struct {
	Span  source.Span
	Value string
}

type RiskLevel struct {
	Span  source.Span
	Value string
}

type VerifyType struct {
	Span  source.Span
	Value string
}

type ElementDef struct {
	Span       source.Span
	Name       ElementName
	Classes    *IdList
	Body       ElementBody
	Delimiters [2]source.Span
}

type ElementBody struct {
	Span   source.Span
	Fields []ElementField
}

type ElementField struct {
	Span    source.Span
	Keyword Token
	Colon   source.Span
	Value   ElementFieldValue
}

type ElementFieldValue struct {
	Kind string
	Type Type
	Ref  Ref
}

type RelationshipDef struct {
	Span         source.Span
	Left, Right  Id
	Relationship Relationship
	Arrow        Token
	Line         source.Span
	Reversed     bool
}

type Relationship struct {
	Span  source.Span
	Value string
}

type ClassDefStatement struct {
	Span   source.Span
	Ids    IdList
	Styles StylesOpt
}

type ClassStatement struct {
	Span      source.Span
	Targets   IdList
	Classes   IdList
	Separator *source.Span
}

type StyleStatement struct {
	Span   source.Span
	Ids    IdList
	Styles StylesOpt
}

type IdList struct {
	Span  source.Span
	Names []Id
}

type StylesOpt struct {
	Span   source.Span
	Styles []Style
}

type Style struct {
	Span       source.Span
	Components []StyleComponent
}

type StyleComponent struct {
	Span source.Span
	Kind string
	Text string
}

type RequirementName struct {
	Span   source.Span
	Quoted bool
	Value  string
}

type Id struct {
	Span   source.Span
	Quoted bool
	Value  string
}

type Text struct {
	Span   source.Span
	Quoted bool
	Value  string
}

type ElementName struct {
	Span   source.Span
	Quoted bool
	Value  string
}

type Type struct {
	Span   source.Span
	Quoted bool
	Value  string
}

type Ref struct {
	Span   source.Span
	Quoted bool
	Value  string
}
