package class

import "github.com/gosuda/elegant-mermaid/internal/source"

type ClassName struct {
	Value, Generic string
	Span           source.Span
}
type NamespaceName = ClassName
type AlphaNumToken = Token
type ClassLiteralName = Token
type ClassLabel = Token
type Statement struct {
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
type Statements []Statement
type ClassStatements = Statements
type Start struct {
	Header     Token
	Statements Statements
	Span       source.Span
}
type MermaidDoc = Start
type GraphConfig = Start
type File = Start
type ClassIdentifier struct {
	Name     ClassName
	Label    string
	HasLabel bool
	Span     source.Span
}
type NamespaceIdentifier = ClassIdentifier
type ClassStatement struct {
	Identifier      ClassIdentifier
	CSS, Annotation string
	Members         Members
	HasBody         bool
	Span            source.Span
}
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
type RelationType string
type LineType string
type Relation struct {
	Start, End RelationType
	Line       LineType
	Span       source.Span
}
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
type NoteText = Token
type NoteStatement struct {
	Name ClassName
	Text string
	Span source.Span
}
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
type CssClassStatement = StyleStatement
type ClassDefStatement = StyleStatement
type ClassList []string
type StylesOpt []Style
type Style struct {
	Text string
	Span source.Span
}
type StyleComponent = Token
type Direction struct {
	Value string
	Span  source.Span
}
