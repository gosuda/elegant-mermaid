package class

import "github.com/gosuda/elegant-mermaid/internal/source"

type ClassName struct {
	Value, Generic string
	Span           source.Span
}
type (
	NamespaceName    = ClassName
	AlphaNumToken    = Token
	ClassLiteralName = Token
	ClassLabel       = Token
	Statement        struct {
		Kind       string
		Span       source.Span
		Class      *ClassStatement
		Namespace  *NamespaceStatement
		Member     *MemberStatement
		Relation   *RelationStatement
		Annotation *AnnotationStatement
		Note       *NoteStatement
		Click      *ClickStatement
		Style      *StyleStatement
		Value      string
	}
)

type (
	Statements      []Statement
	ClassStatements = Statements
	Start           struct {
		Header     Token
		Statements Statements
		Span       source.Span
	}
)

type (
	MermaidDoc      = Start
	GraphConfig     = Start
	File            = Start
	ClassIdentifier struct {
		Name     ClassName
		Label    string
		HasLabel bool
		Span     source.Span
	}
)

type (
	NamespaceIdentifier = ClassIdentifier
	ClassStatement      struct {
		Identifier      ClassIdentifier
		CSS, Annotation string
		Members         Members
		HasBody         bool
		Span            source.Span
	}
)

type NamespaceStatement struct {
	Identifier NamespaceIdentifier
	Children   ClassStatements
	Span       source.Span
}
type Members struct {
	Tokens []Token
	Span   source.Span
}
type MemberStatement struct {
	Name ClassName
	Text string
	Span source.Span
}
type (
	RelationType string
	LineType     string
	Relation     struct {
		Start, End RelationType
		Line       LineType
		Span       source.Span
	}
)

type RelationStatement struct {
	From, To                         ClassName
	FromMultiplicity, ToMultiplicity string
	Relation                         Relation
	Label                            string
	Span                             source.Span
}
type AnnotationStatement struct {
	Annotation string
	Name       ClassName
	Span       source.Span
}
type (
	NoteText      = Token
	NoteStatement struct {
		Name ClassName
		Text string
		Span source.Span
	}
)

type ClickStatement struct {
	Action                            string
	Name                              ClassName
	Value, Arguments, Tooltip, Target string
	Span                              source.Span
}
type StyleStatement struct {
	Targets []string
	Text    string
	Span    source.Span
}
type (
	CssClassStatement = StyleStatement
	ClassDefStatement = StyleStatement
	ClassList         []string
	StylesOpt         []Style
	Style             struct {
		Text string
		Span source.Span
	}
)

type (
	StyleComponent = Token
	Direction      struct {
		Value string
		Span  source.Span
	}
)
