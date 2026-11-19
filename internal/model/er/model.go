package er

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

type Model struct {
	Entities      []Entity
	Declarations  []Declaration
	Groups        []Group
	Relationships []Relationship
	Definitions   []ClassDefinition
	Direction     string
	AccTitle      string
	AccDescr      string
	claimed       map[string]bool
}

type Declaration struct {
	Entity         int
	NameSpan       source.Span
	AttributeStart int
	AttributeEnd   int
}

type Entity struct {
	ID         string
	Label      string
	Alias      string
	HasAlias   bool
	AliasSpan  *source.Span
	Span       source.Span
	Attributes []Attribute
	Parent     int
	Classes    []string
	Styles     []string
	TextStyles []string
}

type Attribute struct {
	Span          source.Span
	AttributeType string
	TypeSpan      source.Span
	Name          string
	NameSpan      source.Span
	Keys          []string
	KeySpans      []source.Span
	Comment       string
	CommentSpan   *source.Span
	Nullable      bool
}

type Target struct {
	Group bool
	Index int
}

type Group struct {
	ID            string
	Label         string
	Span          source.Span
	Parent        int
	Members       []Target
	Direction     string
	DirectionSpan source.Span
	Classes       []string
	Styles        []string
	TextStyles    []string
}

type Relationship struct {
	From             string
	To               string
	FromTarget       Target
	ToTarget         Target
	Span             source.Span
	FromSpan         source.Span
	ToSpan           source.Span
	MarkerStart      string
	MarkerEnd        string
	LeftCardinality  syn.CardinalityKind
	RightCardinality syn.CardinalityKind
	StartSpan        source.Span
	EndSpan          source.Span
	Identifying      bool
	Label            string
	LabelSpan        source.Span
	Index            int
}

type ClassDefinition struct {
	Name       string
	Styles     []string
	TextStyles []string
}

func Resolve(_ []byte, start *syn.Start) (*Model, []diag.Diagnostic) {
	m := &Model{Direction: "TB", claimed: make(map[string]bool)}
	_, direction := m.document(&start.Document)
	if direction != nil {
		m.Direction = direction.Value
	}
	m.compileStyles()
	return m, nil
}

func (m *Model) ensure(name syn.EntityName) int {
	for i := range m.Entities {
		if m.Entities[i].ID == name.Name {
			return i
		}
	}
	m.Entities = append(m.Entities, Entity{
		ID:      name.Name,
		Label:   name.Name,
		Span:    name.Span,
		Parent:  -1,
		Classes: []string{"default"},
	})
	return len(m.Entities) - 1
}

func (m *Model) target(name syn.EntityName) Target {
	index := m.ensure(name)
	for i := len(m.Groups) - 1; i >= 0; i-- {
		if m.Groups[i].ID == name.Name {
			return Target{Group: true, Index: i}
		}
	}
	return Target{Index: index}
}

func (m *Model) document(document *syn.Document) ([]Target, *syn.Direction) {
	var members []Target
	var direction *syn.Direction
	for i := range document.Lines {
		statement := document.Lines[i].Statement
		if statement == nil {
			continue
		}
		if statement.Kind == syn.KindDirection {
			value := statement.Direction
			direction = &value
			continue
		}
		members = appendUnique(members, m.statement(statement))
	}
	return members, direction
}

func (m *Model) statement(s *syn.Statement) []Target {
	switch s.Kind {
	case syn.KindEntity:
		return m.entity(s.Entity)
	case syn.KindRelationship:
		targets := m.relationship(s.Span, s.Relationship)
		m.namedClasses(s.Relationship.From.Name, s.Relationship.FromClasses)
		m.namedClasses(s.Relationship.To.Name, s.Relationship.ToClasses)
		return targets
	case syn.KindSubgraph:
		return []Target{m.subgraph(s.Span, s.Subgraph)}
	default:
		m.metadata(s)
		return nil
	}
}

func (m *Model) entity(s *syn.EntityStatement) []Target {
	index := m.ensure(s.Name)
	e := &m.Entities[index]
	m.applyAlias(e, s.Alias)
	if s.Attributes != nil {
		start := len(e.Attributes)
		for i := range s.Attributes.Attributes {
			e.Attributes = append(e.Attributes, attributeFromAST(&s.Attributes.Attributes[i]))
		}
		m.Declarations = append(m.Declarations, Declaration{
			Entity: index, NameSpan: s.Name.Span,
			AttributeStart: start, AttributeEnd: len(e.Attributes),
		})
	}
	m.namedClasses(s.Name.Name, s.Classes)
	if s.Alias != nil && s.Attributes == nil {
		return nil
	}
	return []Target{{Index: index}}
}

func (m *Model) applyAlias(e *Entity, alias *syn.EntityName) {
	if alias == nil || alias.Name == "" || e.HasAlias {
		return
	}
	e.HasAlias = true
	e.Alias = alias.Name
	span := alias.Span
	e.AliasSpan = &span
	e.Label = alias.Name
}

func (m *Model) relationship(span source.Span, s *syn.RelationshipStatement) []Target {
	from, to := m.target(s.From), m.target(s.To)
	m.Relationships = append(m.Relationships, Relationship{
		From:             s.From.Name,
		To:               s.To.Name,
		FromTarget:       from,
		ToTarget:         to,
		Span:             span,
		FromSpan:         s.From.Span,
		ToSpan:           s.To.Span,
		MarkerStart:      marker(s.Relation.Right.Kind),
		MarkerEnd:        marker(s.Relation.Left.Kind),
		LeftCardinality:  s.Relation.Left.Kind,
		RightCardinality: s.Relation.Right.Kind,
		StartSpan:        s.Relation.Right.Span,
		EndSpan:          s.Relation.Left.Span,
		Identifying:      s.Relation.RelType.Identifying,
		Label:            syntax.DecodeEntities(s.Role.Label),
		LabelSpan:        s.Role.Span,
		Index:            len(m.Relationships),
	})
	return []Target{from, to}
}

func marker(kind syn.CardinalityKind) string {
	switch kind {
	case syn.CardOnlyOne:
		return "only_one"
	case syn.CardZeroOrOne:
		return "zero_or_one"
	case syn.CardOneOrMore:
		return "one_or_more"
	case syn.CardZeroOrMore:
		return "zero_or_more"
	}
	return ""
}

func (m *Model) subgraph(span source.Span, s *syn.SubgraphStatement) Target {
	members, direction := m.document(&s.Document)
	var kept []Target
	for _, member := range members {
		id := m.targetID(member)
		if m.claimed[id] {
			continue
		}
		m.claimed[id] = true
		kept = append(kept, member)
	}
	index := len(m.Groups)
	for _, member := range kept {
		m.setParent(member, index)
	}
	label := s.Header.ID.Name
	if s.Header.Title != nil {
		parts := make([]string, len(s.Header.Title.Parts))
		for i := range s.Header.Title.Parts {
			parts[i] = s.Header.Title.Parts[i].Name
		}
		label = strings.Join(parts, " ")
	}
	m.Groups = append(m.Groups, Group{
		ID:            s.Header.ID.Name,
		Label:         syntax.DecodeEntities(label),
		Span:          span,
		Parent:        -1,
		Members:       kept,
		Direction:     directionValue(direction),
		DirectionSpan: directionSpan(direction, s.Header.Span),
	})
	return Target{Group: true, Index: index}
}

func directionValue(direction *syn.Direction) string {
	if direction == nil {
		return ""
	}
	return direction.Value
}

func directionSpan(direction *syn.Direction, header source.Span) source.Span {
	if direction == nil {
		return header
	}
	return direction.Span
}

func (m *Model) targetID(t Target) string {
	if t.Group {
		if t.Index < len(m.Groups) {
			return m.Groups[t.Index].ID
		}
		return ""
	}
	if t.Index < len(m.Entities) {
		return m.Entities[t.Index].ID
	}
	return ""
}

func (m *Model) setParent(t Target, parent int) {
	if t.Group {
		if t.Index < len(m.Groups) {
			m.Groups[t.Index].Parent = parent
		}
		return
	}
	if t.Index < len(m.Entities) {
		m.Entities[t.Index].Parent = parent
	}
}

func (m *Model) existing(name string) []Target {
	var out []Target
	if i := slices.IndexFunc(m.Entities, func(e Entity) bool { return e.ID == name }); i >= 0 {
		out = append(out, Target{Index: i})
	}
	if i := slices.IndexFunc(m.Groups, func(g Group) bool { return g.ID == name }); i >= 0 {
		out = append(out, Target{Group: true, Index: i})
	}
	return out
}

func (m *Model) namedClasses(name string, classes *syn.IdList) {
	for _, target := range m.existing(name) {
		m.attachClasses(target, classes)
	}
}

func (m *Model) attachClasses(t Target, classes *syn.IdList) {
	if classes == nil {
		return
	}
	names := make([]string, len(classes.Names))
	for i, name := range classes.Names {
		names[i] = name.Text
	}
	if t.Group {
		if t.Index < len(m.Groups) {
			m.Groups[t.Index].Classes = append(m.Groups[t.Index].Classes, names...)
		}
		return
	}
	if t.Index < len(m.Entities) {
		m.Entities[t.Index].Classes = append(m.Entities[t.Index].Classes, names...)
	}
}

func (m *Model) metadata(s *syn.Statement) {
	switch s.Kind {
	case syn.KindAccessibility:
		if s.Accessibility.Title {
			m.AccTitle = strings.TrimSpace(s.Accessibility.Value.Text)
		} else {
			m.AccDescr = strings.TrimSpace(s.Accessibility.Value.Text)
		}
	case syn.KindClassDef:
		m.definition(*s.ClassDef)
	case syn.KindClass:
		m.classStatement(*s.Class)
	case syn.KindStyle:
		m.styleStatement(*s.Style)
	}
}

func (m *Model) classStatement(v syn.ClassStatement) {
	for _, name := range v.Targets.Names {
		m.namedClasses(name.Text, &v.Classes)
	}
}

func (m *Model) styleStatement(v syn.StyleStatement) {
	styles := styleValues(v.Styles)
	for _, name := range v.Targets.Names {
		for _, target := range m.existing(name.Text) {
			m.attachStyles(target, styles)
		}
	}
}

func (m *Model) definition(v syn.ClassDefStatement) {
	styles := styleValues(v.Styles)
	texts := textStyles(styles)
	for _, name := range v.IDs.Names {
		if i := slices.IndexFunc(m.Definitions, func(row ClassDefinition) bool { return row.Name == name.Text }); i >= 0 {
			m.Definitions[i].Styles = append(m.Definitions[i].Styles, styles...)
			m.Definitions[i].TextStyles = append(m.Definitions[i].TextStyles, texts...)
			continue
		}
		m.Definitions = append(m.Definitions, ClassDefinition{Name: name.Text, Styles: slices.Clone(styles), TextStyles: slices.Clone(texts)})
	}
}

func (m *Model) attachStyles(t Target, styles []string) {
	if t.Group {
		if t.Index < len(m.Groups) {
			m.Groups[t.Index].Styles = append(m.Groups[t.Index].Styles, styles...)
		}
		return
	}
	if t.Index < len(m.Entities) {
		m.Entities[t.Index].Styles = append(m.Entities[t.Index].Styles, styles...)
	}
}

func (m *Model) compileStyles() {
	for i := range m.Entities {
		compile(m.Definitions, m.Entities[i].Classes, &m.Entities[i].Styles, &m.Entities[i].TextStyles)
	}
	for i := range m.Groups {
		compile(m.Definitions, m.Groups[i].Classes, &m.Groups[i].Styles, &m.Groups[i].TextStyles)
	}
}

func appendUnique(members []Target, targets []Target) []Target {
	for _, t := range targets {
		if !slices.Contains(members, t) {
			members = append(members, t)
		}
	}
	return members
}

func attributeFromAST(a *syn.Attribute) Attribute {
	nullable := a.AttributeType.Question != nil
	attributeType := strings.Trim(a.AttributeType.Word.Text, "`")
	if nullable {
		attributeType += "?"
	}
	attribute := Attribute{
		Span:          a.Span,
		AttributeType: attributeType,
		TypeSpan:      a.AttributeType.Span,
		Name:          strings.Trim(a.Name.Word.Text, "`"),
		NameSpan:      a.Name.Span,
		Nullable:      nullable,
	}
	if a.Keys != nil {
		for i := range a.Keys.Keys {
			attribute.Keys = append(attribute.Keys, a.Keys.Keys[i].Value)
			attribute.KeySpans = append(attribute.KeySpans, a.Keys.Keys[i].Span)
		}
	}
	if a.Comment != nil {
		attribute.Comment = a.Comment.Text
		span := a.Comment.Span
		attribute.CommentSpan = &span
	}
	return attribute
}

func styleValues(styles syn.StylesOpt) []string {
	out := make([]string, 0, len(styles.Styles))
	for _, style := range styles.Styles {
		var b strings.Builder
		for _, part := range style.Components {
			b.WriteString(part.Text)
		}
		out = append(out, b.String())
	}
	return out
}

func textStyles(styles []string) []string {
	var out []string
	for _, style := range styles {
		if strings.Contains(style, "color") {
			out = append(out, strings.ReplaceAll(style, "fill", "bgFill"))
		}
	}
	return out
}

func compile(definitions []ClassDefinition, classes []string, styles *[]string, texts *[]string) {
	for _, class := range classes {
		i := slices.IndexFunc(definitions, func(row ClassDefinition) bool { return row.Name == class })
		if i < 0 {
			continue
		}
		*styles = append(*styles, definitions[i].Styles...)
		*texts = append(*texts, definitions[i].TextStyles...)
	}
}

// TableRows is the attribute table of one entity: type, name, keys, comment.
func (e *Entity) TableRows() [][]string {
	rows := make([][]string, 0, len(e.Attributes))
	for i := range e.Attributes {
		a := &e.Attributes[i]
		rows = append(rows, []string{
			syntax.DecodeEntities(a.AttributeType),
			syntax.DecodeEntities(a.Name),
			strings.Join(a.Keys, ","),
			syntax.DecodeEntities(a.Comment),
		})
	}
	return rows
}

// DisplayName is the heading text of one entity.
func (e *Entity) DisplayName() string {
	return syntax.DecodeEntities(e.Label)
}
