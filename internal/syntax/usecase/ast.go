package usecase

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span    source.Span
	Header  Token
	LineEnd LineEnd
	Tokens  []Token
	Lines   []Line
}

type Line struct {
	Span      source.Span
	Blank     *BlankLine
	Comment   *CommentLine
	Statement *Statement
}

type LineEnd struct {
	Span  source.Span
	Token *Token
}

type BlankLine struct {
	Span  source.Span
	Token Token
}

type CommentLine struct {
	Span    source.Span
	Token   Token
	LineEnd LineEnd
}

type Statement struct {
	Span               source.Span
	AccTitle           *AccTitleStatement
	AccDescr           *AccDescrStatement
	Direction          *DirectionStatement
	Actor              *ActorStatement
	Entity             *EntityStatement
	SystemBoundary     *SystemBoundaryStatement
	MetadataAssignment *MetadataAssignmentStatement
	Note               *NoteStatement
	JSON               *JsonStatement
	ClassDef           *ClassDefStatement
	Class              *ClassStatement
	Style              *StyleStatement
	LineEnd            LineEnd
}

type AccTitleStatement struct {
	Span        source.Span
	Token       Token
	Value       string
	ContentSpan source.Span
}

type AccDescrStatement struct {
	Span        source.Span
	Token       Token
	Value       string
	ContentSpan source.Span
}

type DirectionStatement struct {
	Span      source.Span
	Keyword   Token
	Direction Token
}

type ActorStatement struct {
	Span     source.Span
	Keyword  Token
	Items    []ActorItem
	Relation *RelationTail
}

type ActorDeclarationOnly struct {
	Span    source.Span
	Keyword Token
	Items   []ActorItem
	LineEnd LineEnd
}

type ActorItem struct {
	Span       source.Span
	Name       ActorName
	Metadata   *Metadata
	Stereotype *Stereotype
	Classes    *ClassSuffix
}

type Delimiters struct{ Open, Close Token }

type ActorName struct {
	Span          source.Span
	ID            Token
	IDContentSpan source.Span
	Label         *NodeLabel
	Delimiters    *Delimiters
}

type EntityStatement struct {
	Span     source.Span
	Name     EntityName
	Relation *RelationTail
}

type EntityName struct {
	Span          source.Span
	ID            Token
	IDContentSpan source.Span
	Label         *NodeLabel
	Delimiters    *Delimiters
	Metadata      *UseCaseMetadata
	Stereotype    *Stereotype
	Classes       *ClassSuffix
}

type LabelKind int

const (
	LabelPlain LabelKind = iota
	LabelQuoted
	LabelMarkdown
)

type NodeLabel struct {
	Span        source.Span
	Text        string
	ContentSpan source.Span
	Kind        LabelKind
	Tokens      []Token
}

type UseCaseMetadata struct {
	Span     source.Span
	Metadata Metadata
}

type RelationTail struct {
	Span     source.Span
	ID       *Token
	At       *Token
	Arrow    Arrow
	Endpoint EntityName
}

type Arrow struct {
	Span            source.Span
	Semantic        *SemanticRelation
	ForwardSolid    *ForwardSolidOperator
	BackwardSolid   *BackwardSolidOperator
	MarkerlessSolid *MarkerlessSolidOperator
	ForwardCircle   *ForwardCircleOperator
	BackwardCircle  *BackwardCircleOperator
	ForwardCross    *ForwardCrossOperator
	BackwardCross   *BackwardCrossOperator
}

type SemanticRelation struct {
	Span     source.Span
	Operator Token
	Colon    *Token
	Relation *Token
}

type ForwardSolidOperator struct {
	Span  source.Span
	Token Token
}

type ForwardCircleOperator struct {
	Span  source.Span
	Token Token
}

type ForwardCrossOperator struct {
	Span  source.Span
	Token Token
}

type BackwardSolidOperator struct {
	Span  source.Span
	Token Token
	Label *EdgeLabel
	Right *Token
}

type MarkerlessSolidOperator struct {
	Span  source.Span
	Token Token
	Label *EdgeLabel
	Right *Token
}

type BackwardCircleOperator struct {
	Span  source.Span
	Token Token
	Label *EdgeLabel
	Right *Token
}

type BackwardCrossOperator struct {
	Span  source.Span
	Token Token
	Label *EdgeLabel
	Right *Token
}

type EdgeLabel struct {
	Span  source.Span
	Label NodeLabel
}

type Metadata struct {
	Span       source.Span
	Open       Token
	Properties []MetadataProperty
	Separators []MetadataSeparator
	Close      Token
}

type MetadataProperty struct {
	Span             source.Span
	Key              Token
	Value            Token
	KeyContentSpan   source.Span
	ValueContentSpan source.Span
}

type MetadataSeparator struct {
	Span   source.Span
	Tokens []Token
}

type MetadataAssignmentStatement struct {
	Span     source.Span
	Target   MetadataAssignmentTarget
	Metadata Metadata
}

type MetadataAssignmentTarget struct {
	Span        source.Span
	Token       Token
	ContentSpan source.Span
}

type SystemBoundaryStatement struct {
	Span     source.Span
	Keyword  Token
	Name     SystemBoundaryName
	Metadata *Metadata
	Classes  *ClassSuffix
	LineEnd  LineEnd
	Content  SystemBoundaryContent
	Close    Token
}

type SystemBoundaryName struct {
	Span          source.Span
	ID            Token
	IDContentSpan source.Span
	Label         *NodeLabel
	Delimiters    *Delimiters
}

type SystemBoundaryContent struct {
	Span     source.Span
	Elements []BoundaryElement
}

type BoundaryElement struct {
	Span    source.Span
	Blank   *BlankLine
	Comment *CommentLine
	Actor   *ActorDeclarationOnly
	Entity  *BoundaryEntity
}

type BoundaryEntity struct {
	Name    EntityName
	LineEnd LineEnd
}

type NoteStatement struct {
	Span     source.Span
	Keyword  Token
	ForToken Token
	Target   Token
	Label    NodeLabel
}

type Stereotype struct {
	Span        source.Span
	Open        Token
	Content     Token
	ContentSpan source.Span
	Close       Token
}

type ClassSuffix struct {
	Span      source.Span
	Separator Token
	Classes   []Token
}

type JsonStatement struct {
	Span    source.Span
	Header  Token
	ID      Token
	Object  JsonObject
	Classes *ClassSuffix
}

type JsonObject struct {
	Span       source.Span
	Properties []JsonProperty
}

type JsonProperty struct {
	Span  source.Span
	Key   Token
	Value JsonValue
}

type JsonValueKind int

const (
	JSONObject JsonValueKind = iota
	JSONArray
	JSONScalar
)

type JsonValue struct {
	Span   source.Span
	Kind   JsonValueKind
	Object JsonObject
	Array  []JsonValue
	Scalar Token
}

type ClassDefStatement struct {
	Span    source.Span
	Keyword Token
	Classes []Token
	Styles  Styles
}

type ClassStatement struct {
	Span    source.Span
	Keyword Token
	Targets []Token
	Classes []Token
}

type StyleStatement struct {
	Span    source.Span
	Keyword Token
	Target  Token
	Styles  Styles
}

type Styles struct {
	Span   source.Span
	Values []StyleValue
}

type StyleValue struct {
	Span       source.Span
	Key        []Token
	Components []StyleComponent
}

type StyleComponent struct {
	Span  source.Span
	Token Token
}
