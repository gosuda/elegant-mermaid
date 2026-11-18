package agentflow

import (
	"sort"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax"
	synagentflow "github.com/gosuda/elegant-mermaid/internal/syntax/agentflow"
)

type Model struct {
	Nodes                []VertexModel
	Edges                []Edge
	Groups               []Flow
	Declarations         []Declaration
	ClassDefs            []ClassDefinition
	Links                []Interaction
	Direction            string
	AuthoredDirection    string
	AccTitle             string
	AccDescr             string
	DefaultEdgeStyles    []string
	DefaultInterpolation string
	Padding              int
	PaddingSet           bool
	global               map[string]struct{}
	reserved             map[string]struct{}
	diagnostics          []diag.Diagnostic
	anonymous            int
}

type Declaration struct {
	Node    int
	Group   int
	IsGroup bool
}

type Appearance struct {
	Classes  []string
	Styles   []string
	Metadata []syn.ConfigEntry
}

type VertexModel struct {
	ID           string
	Label        string
	LabelKind    synagentflow.TextKind
	Shape        string
	Parent       string
	Span         source.Span
	IDSpan       source.Span
	MetadataSpan *source.Span
	Connector    bool
	Appearance   Appearance
}

type Edge struct {
	ID            string
	From          string
	To            string
	FromSpan      source.Span
	ToSpan        source.Span
	Span          source.Span
	OperatorSpan  source.Span
	Label         string
	LabelKind     synagentflow.TextKind
	LabelSpan     *source.Span
	Marker        string
	Line          string
	Semantics     string
	Length        int
	Interpolation string
	Appearance    Appearance
}

type Flow struct {
	ID            string
	Title         string
	Parent        string
	Direction     string
	DirectionSpan source.Span
	Span          source.Span
	Opening       source.Span
	Members       []string
	Appearance    Appearance
}

type ClassDefinition struct {
	ID     string
	Styles []string
	Span   source.Span
}

type Interaction struct {
	ID        string
	URL       *string
	Callback  *string
	Arguments *string
	Tooltip   *string
	Target    *string
	Span      source.Span
}

type scopeKind uint8

const (
	scopeRoot scopeKind = iota
	scopeFlow
	scopeGlobal
)

type scope struct {
	kind scopeKind
	id   string
}

func Resolve(sourceText []byte, document *synagentflow.Start) (*Model, []diag.Diagnostic) {
	text := string(sourceText)
	m := &Model{
		Direction: canonicalDirection(document.Config.Direction.Value),
		global:    map[string]struct{}{},
		reserved:  map[string]struct{}{},
	}
	if document.Config.Authored != nil {
		m.AuthoredDirection = strings.TrimSpace(document.Config.Authored.Text)
	}
	padding, hasPadding := configuredPadding(text)
	m.Padding, m.PaddingSet = padding, hasPadding
	reserveIDs(&document.Document, m.reserved)
	m.walk(&document.Document, scope{})
	m.finishClasses()
	m.collapse()
	diagnostics := m.diagnostics
	m.diagnostics = nil
	diag.Sort(diagnostics)
	return m, diagnostics
}

func (m *Model) walk(document *synagentflow.Document, sc scope) {
	for i := range document.Lines {
		if document.Lines[i].Statement != nil {
			m.statement(document.Lines[i].Statement, sc)
		}
	}
}

func (m *Model) statement(statement *synagentflow.Statement, sc scope) {
	switch {
	case statement.Kind.Vertex != nil:
		m.vertices(statement.Kind.Vertex, sc)
	case statement.Kind.Flow != nil:
		m.flow(statement.Kind.Flow, statement.Span, sc)
	case statement.Kind.Global != nil:
		m.walk(&statement.Kind.Global.Body, scope{kind: scopeGlobal})
	case statement.Kind.Connector != nil:
		value := statement.Kind.Connector
		m.connector(&value.Name, value.Title, value.Metadata, sc)
	case statement.Kind.Direction != nil:
		m.setDirection(statement.Kind.Direction, sc)
	case statement.Kind.Access != nil:
		if statement.Kind.Access.Title {
			m.AccTitle = strings.TrimSpace(statement.Kind.Access.Value.Text)
		} else {
			m.AccDescr = strings.TrimSpace(statement.Kind.Access.Value.Text)
		}
	default:
		m.directive(statement)
	}
}

func (m *Model) directive(statement *synagentflow.Statement) {
	switch {
	case statement.Kind.ClassDef != nil:
		value := statement.Kind.ClassDef
		m.ClassDefs = append(m.ClassDefs, ClassDefinition{ID: idText(value.ID), Styles: stylesList(&value.Styles), Span: value.Span})
	case statement.Kind.Class != nil:
		value := statement.Kind.Class
		for _, id := range strings.Split(idText(value.Targets), ",") {
			if appearance := m.appearance(strings.TrimSpace(id)); appearance != nil {
				appearance.Classes = append(appearance.Classes, idText(value.Class))
			}
		}
	case statement.Kind.Style != nil:
		value := statement.Kind.Style
		for _, id := range strings.Split(idText(value.Targets), ",") {
			if appearance := m.appearance(strings.TrimSpace(id)); appearance != nil {
				appearance.Styles = append(appearance.Styles, stylesList(&value.Styles)...)
			}
		}
	case statement.Kind.LinkStyle != nil:
		m.linkStyle(statement.Kind.LinkStyle)
	case statement.Kind.Click != nil:
		m.click(statement.Kind.Click)
	}
}

func (m *Model) appearance(id string) *Appearance {
	for i := range m.Nodes {
		if m.Nodes[i].ID == id {
			return &m.Nodes[i].Appearance
		}
	}
	for i := range m.Groups {
		if m.Groups[i].ID == id {
			return &m.Groups[i].Appearance
		}
	}
	for i := range m.Edges {
		if m.Edges[i].ID == id {
			return &m.Edges[i].Appearance
		}
	}
	return nil
}

func (m *Model) linkStyle(value *synagentflow.LinkStyleStatement) {
	var appearance []string
	if value.Styles != nil {
		appearance = stylesList(value.Styles)
	}
	var interpolation string
	if value.Interpolation != nil {
		interpolation = joinTokens(value.Interpolation.Tokens)
	}
	if value.Default != nil {
		m.edgeDefaults(appearance, interpolation)
	}
	if value.Indices != nil {
		for _, token := range value.Indices.Indices {
			m.styleEdge(token, appearance, interpolation)
		}
	}
}

func (m *Model) styleEdge(token synagentflow.Token, appearance []string, interpolation string) {
	index := parseIndex(token.Text)
	if index < 0 || index >= len(m.Edges) {
		last := max(len(m.Edges)-1, 0)
		m.diagnostics = append(m.diagnostics, report("agentflow/link-style-index",
			"linkStyle index "+token.Text+" is outside 0.."+strconv.Itoa(last), token.Span))
		return
	}
	edge := &m.Edges[index]
	edge.Appearance.Styles = append(edge.Appearance.Styles, appearance...)
	if !hasFillStyle(appearance) {
		edge.Appearance.Styles = append(edge.Appearance.Styles, "fill:none")
	}
	if interpolation != "" {
		edge.Interpolation = interpolation
	}
}

func hasFillStyle(styles []string) bool {
	for _, style := range styles {
		if strings.HasPrefix(strings.TrimLeft(style, " \t"), "fill:") {
			return true
		}
	}
	return false
}

func (m *Model) edgeDefaults(appearance []string, interpolation string) {
	m.DefaultEdgeStyles = append(m.DefaultEdgeStyles, appearance...)
	if interpolation != "" {
		m.DefaultInterpolation = interpolation
	}
	for i := range m.Edges {
		m.Edges[i].Appearance.Styles = append(m.Edges[i].Appearance.Styles, appearance...)
		if interpolation != "" {
			m.Edges[i].Interpolation = interpolation
		}
	}
}

func (m *Model) click(value *synagentflow.ClickStatement) {
	if value.URL != nil {
		scheme, _, found := strings.Cut(strings.TrimSpace(value.URL.Text), ":")
		if !found || !safeScheme(scheme) {
			m.diagnostics = append(m.diagnostics, report("interaction/unsafe-url", "link URL is not allowed", value.URL.Span))
		}
	}
	if value.Callback != nil {
		m.diagnostics = append(m.diagnostics, report("interaction/callback-ignored",
			"callback "+joinTokens(value.Callback.Tokens)+" is ignored", value.Callback.Span))
	}
	m.Links = append(m.Links, Interaction{
		ID:        value.ID.Text,
		URL:       tokenString(value.URL),
		Callback:  alphaString(value.Callback),
		Arguments: tokenString(value.Arguments),
		Tooltip:   tokenString(value.Tooltip),
		Target:    tokenString(value.Target),
		Span:      value.Span,
	})
}

func safeScheme(scheme string) bool {
	switch strings.ToLower(scheme) {
	case "http", "https", "mailto":
		return true
	}
	return false
}

func tokenString(t *synagentflow.Token) *string {
	if t == nil {
		return nil
	}
	value := t.Text
	return &value
}

func alphaString(a *synagentflow.AlphaNum) *string {
	if a == nil {
		return nil
	}
	value := joinTokens(a.Tokens)
	return &value
}

func (m *Model) finishClasses() {
	for i := range m.Nodes {
		m.Nodes[i].Appearance.Styles = appliedStyles(m.ClassDefs, &m.Nodes[i].Appearance)
	}
	for i := range m.Groups {
		m.Groups[i].Appearance.Styles = appliedStyles(m.ClassDefs, &m.Groups[i].Appearance)
	}
	for i := range m.Edges {
		m.Edges[i].Appearance.Styles = appliedStyles(m.ClassDefs, &m.Edges[i].Appearance)
	}
}

func appliedStyles(defs []ClassDefinition, appearance *Appearance) []string {
	var applied []string
	for _, def := range defs {
		if classMatches(def.ID, appearance) {
			applied = append(applied, def.Styles...)
		}
	}
	applied = append(applied, appearance.Styles...)
	return applied
}

func classMatches(defID string, appearance *Appearance) bool {
	for _, id := range strings.Split(defID, ",") {
		if id == "default" {
			return true
		}
		for _, class := range appearance.Classes {
			if class == id {
				return true
			}
		}
	}
	return false
}

func (m *Model) setDirection(value *synagentflow.Direction, sc scope) {
	if sc.kind == scopeFlow {
		for i := range m.Groups {
			if m.Groups[i].ID == sc.id {
				m.Groups[i].Direction = canonicalDirection(value.Value)
				m.Groups[i].DirectionSpan = value.Span
			}
		}
		return
	}
	m.Direction = canonicalDirection(value.Value)
}

func (m *Model) ensure(id string, span source.Span) int {
	if id == "" || id == "connectors" || m.groupIndex(id) >= 0 {
		return -1
	}
	if index := m.nodeIndex(id); index >= 0 {
		return index
	}
	index := len(m.Nodes)
	m.Nodes = append(m.Nodes, VertexModel{
		ID: id, Label: syn.DecodeEntities(strings.TrimSpace(id)), LabelKind: synagentflow.TextPlain,
		Shape: "roundedRect", Span: span, IDSpan: span,
	})
	m.Declarations = append(m.Declarations, Declaration{Node: index})
	return index
}

func (m *Model) nodeIndex(id string) int {
	for i := range m.Nodes {
		if m.Nodes[i].ID == id {
			return i
		}
	}
	return -1
}

func (m *Model) groupIndex(id string) int {
	for i := range m.Groups {
		if m.Groups[i].ID == id {
			return i
		}
	}
	return -1
}

func (m *Model) parentOf(id string) string {
	if i := m.nodeIndex(id); i >= 0 {
		return m.Nodes[i].Parent
	}
	if i := m.groupIndex(id); i >= 0 {
		return m.Groups[i].Parent
	}
	return ""
}

func (m *Model) join(id string, span source.Span, sc scope) {
	if sc.kind == scopeGlobal {
		m.global[id] = struct{}{}
		m.release(id)
		return
	}
	if sc.kind != scopeFlow {
		return
	}
	if _, ok := m.global[id]; ok {
		return
	}
	if m.parentOf(id) != "" {
		return
	}
	if m.closesContainment(id, sc) {
		m.diagnostics = append(m.diagnostics, report("agentflow/containment-violation",
			"container "+sc.id+" cannot contain "+id+" because it closes a containment cycle", span))
		return
	}
	m.attach(id, sc.id)
}

func (m *Model) closesContainment(id string, sc scope) bool {
	for ancestor := sc.id; ancestor != ""; ancestor = m.parentOf(ancestor) {
		if ancestor == id {
			return true
		}
	}
	return false
}

func (m *Model) attach(id, parent string) {
	if i := m.nodeIndex(id); i >= 0 {
		m.Nodes[i].Parent = parent
	}
	if i := m.groupIndex(id); i >= 0 {
		m.Groups[i].Parent = parent
	}
	if g := m.groupIndex(parent); g >= 0 && !contains(m.Groups[g].Members, id) {
		m.Groups[g].Members = append(m.Groups[g].Members, id)
	}
}

func (m *Model) release(id string) {
	if i := m.nodeIndex(id); i >= 0 {
		m.Nodes[i].Parent = ""
	}
	if i := m.groupIndex(id); i >= 0 {
		m.Groups[i].Parent = ""
	}
	for g := range m.Groups {
		m.Groups[g].Members = removeString(m.Groups[g].Members, id)
	}
}

func removeString(values []string, value string) []string {
	out := values[:0]
	for _, v := range values {
		if v != value {
			out = append(out, v)
		}
	}
	return out
}

func propertyEntries(property *[2]synagentflow.Token) []syn.ConfigEntry {
	if property == nil {
		return nil
	}
	return []syn.ConfigEntry{{
		Key:     property[0].Text,
		KeySpan: property[0].Span,
		Value:   syn.ConfigValue{Kind: syn.ValueString, Text: property[1].Text},
	}}
}

func (m *Model) endpoint(styled *synagentflow.StyledVertex, sc scope) (string, bool) {
	id := idText(styled.Vertex.ID)
	if id == "" {
		return "", false
	}
	entries := mergeEntries(propertyEntries(styled.Vertex.Property), m.metadata(styled.Metadata))
	if m.reference(id, entries, styled) {
		return m.referencedEndpoint(id, styled, sc)
	}
	index := m.ensure(id, styled.Vertex.ID.Span)
	if index < 0 {
		return "", false
	}
	shape := ""
	if styled.Vertex.Shape != "" {
		shape = m.normalize(styled.Vertex.Shape, styled.Vertex.Span)
	}
	node := &m.Nodes[index]
	node.Span = styled.Span
	if styled.Vertex.Label != nil {
		node.Label = syn.DecodeEntities(strings.TrimSpace(textText(styled.Vertex.Label)))
		node.LabelKind = styled.Vertex.Label.Kind
	}
	if shape != "" {
		node.Shape = shape
	}
	if styled.Class != nil {
		node.Appearance.Classes = append(node.Appearance.Classes, idText(*styled.Class))
	}
	if len(styled.Metadata) > 0 {
		last := styled.Metadata[len(styled.Metadata)-1].Span
		node.MetadataSpan = &last
	}
	node.Appearance.Metadata = mergeEntries(node.Appearance.Metadata, entries)
	m.nodeMetadata(index, entries, styled.Metadata)
	m.join(id, styled.Vertex.ID.Span, sc)
	return id, true
}

func (m *Model) referencedEndpoint(id string, styled *synagentflow.StyledVertex, sc scope) (string, bool) {
	if styled.Class != nil {
		if appearance := m.appearance(id); appearance != nil {
			appearance.Classes = append(appearance.Classes, idText(*styled.Class))
		}
	}
	if m.groupIndex(id) < 0 {
		return "", false
	}
	m.join(id, styled.Vertex.ID.Span, sc)
	return id, true
}

func (m *Model) vertices(value *synagentflow.VertexStatement, sc scope) {
	var previous []endpointRef
	for i := range value.Nodes {
		set := &value.Nodes[i]
		var next []endpointRef
		for v := range set.Vertices {
			if id, ok := m.endpoint(&set.Vertices[v], sc); ok {
				next = append(next, endpointRef{id: id, span: set.Vertices[v].Vertex.ID.Span})
			}
		}
		if i > 0 && i-1 < len(value.Links) {
			m.product(previous, next, &value.Links[i-1])
		}
		previous = next
	}
}

type endpointRef struct {
	id   string
	span source.Span
}

func (m *Model) product(from, to []endpointRef, link *synagentflow.Link) {
	for si := range from {
		for ti := range to {
			authored := ""
			if link.Statement.ID != nil && si+1 == len(from) && ti == 0 {
				authored = strings.TrimRight(link.Statement.ID.Text, "@")
			}
			m.addEdge(&from[si], &to[ti], link, authored)
		}
	}
}

func (m *Model) addEdge(from, to *endpointRef, link *synagentflow.Link, authored string) {
	id := m.edgeID(authored)
	operator := strings.TrimSpace(link.Statement.Operator.Text)
	dotted := strings.Contains(operator, ".")
	marker := "none"
	if strings.HasSuffix(operator, "x") {
		marker = "cross"
	} else if strings.HasSuffix(operator, ">") {
		marker = "point"
	}
	var length int
	if dotted {
		length = dottedLength(operator)
	} else {
		length = solidLength(operator)
	}
	var label string
	var labelKind synagentflow.TextKind
	var labelSpan *source.Span
	if l := link.Label(); l != nil {
		label = syn.DecodeEntities(strings.TrimSpace(textText(l)))
		labelKind = l.Kind
		span := l.Span
		labelSpan = &span
	}
	line := "normal"
	semantics := "sequence"
	if dotted {
		line = "dotted"
		semantics = "reference"
	} else if marker == "cross" {
		semantics = "failure"
	}
	edge := Edge{
		ID: id, From: from.id, To: to.id,
		FromSpan: from.span, ToSpan: to.span,
		Span: link.Span, OperatorSpan: link.Statement.Operator.Span,
		Label: label, LabelKind: labelKind, LabelSpan: labelSpan,
		Marker: marker, Line: line, Semantics: semantics, Length: length,
		Interpolation: m.DefaultInterpolation,
	}
	edge.Appearance.Styles = append([]string{}, m.DefaultEdgeStyles...)
	m.Edges = append(m.Edges, edge)
}

func dottedLength(operator string) int {
	return min(max(strings.Count(operator, "."), 1), 10)
}

func solidLength(operator string) int {
	return min(max(strings.Count(operator, "-")-1, 1), 10)
}

func (m *Model) edgeID(authored string) string {
	if authored != "" && !contains(m.edgeIDs(), authored) {
		return authored
	}
	ordinal := len(m.Edges)
	ids := m.edgeIDs()
	for {
		id := "e" + strconv.Itoa(ordinal)
		if !contains(ids, id) {
			return id
		}
		ordinal++
	}
}

func (m *Model) edgeIDs() []string {
	ids := make([]string, len(m.Edges))
	for i := range m.Edges {
		ids[i] = m.Edges[i].ID
	}
	return ids
}

func (m *Model) flow(value *synagentflow.FlowStatement, span source.Span, sc scope) {
	name, title, data, opening := value.Name, value.Title, value.Metadata, value.Opening
	id := ""
	if name != nil {
		id = syn.DecodeEntities(strings.TrimSpace(noTagsText(name)))
	}
	if id == "" {
		id = m.flowID()
	}
	titleText := ""
	switch {
	case title != nil:
		titleText = syn.DecodeEntities(strings.TrimSpace(textText(title)))
	case name != nil:
		titleText = syn.DecodeEntities(strings.TrimSpace(noTagsText(name)))
	}
	entries := m.metadata(data)
	if m.groupIndex(id) < 0 {
		if index := m.nodeIndex(id); index >= 0 {
			m.Nodes = append(m.Nodes[:index], m.Nodes[index+1:]...)
		}
		m.reindexNodes()
		m.Declarations = append(m.Declarations, Declaration{Group: len(m.Groups), IsGroup: true})
		m.Groups = append(m.Groups, Flow{
			ID: id, DirectionSpan: opening, Span: span, Opening: opening,
		})
	}
	if g := m.groupIndex(id); g >= 0 {
		if titleText != "" {
			m.Groups[g].Title = titleText
		}
		m.Groups[g].Appearance.Metadata = mergeEntries(m.Groups[g].Appearance.Metadata, entries)
	}
	m.join(id, opening, sc)
	m.walk(&value.Body, scope{kind: scopeFlow, id: id})
}

func (m *Model) flowID() string {
	for {
		id := "flow" + strconv.Itoa(m.anonymous)
		m.anonymous++
		if _, taken := m.reserved[id]; !taken {
			m.reserved[id] = struct{}{}
			return id
		}
	}
}

func (m *Model) connector(name *synagentflow.TextNoTags, title *synagentflow.Text, data []synagentflow.ShapeData, sc scope) {
	id := syn.DecodeEntities(strings.TrimSpace(noTagsText(name)))
	entries := m.metadata(data)
	index := m.ensure(id, name.Span)
	if index < 0 {
		return
	}
	node := &m.Nodes[index]
	node.Connector = true
	node.Shape = "connector"
	if title != nil {
		if label := syn.DecodeEntities(strings.TrimSpace(textText(title))); label != "" {
			node.Label = label
		}
	}
	node.Appearance.Metadata = mergeEntries(node.Appearance.Metadata, entries)
	m.nodeMetadata(index, entries, data)
	m.join(id, name.Span, sc)
}

func (m *Model) collapsedOwner(id string) string {
	owner := ""
	ancestor := m.parentOf(id)
	for ancestor != "" {
		if g := m.groupIndex(ancestor); g >= 0 && collapsed(&m.Groups[g]) {
			owner = ancestor
		}
		ancestor = m.parentOf(ancestor)
	}
	return owner
}

func (m *Model) collapse() {
	redirects := m.collapseRedirects()
	m.Edges = m.redirectEdges(redirects)
	nodes := m.Nodes[:0]
	for i := range m.Nodes {
		if redirects[m.Nodes[i].ID] == "" {
			nodes = append(nodes, m.Nodes[i])
		}
	}
	m.Nodes = nodes
	m.reindexNodes()
}

func (m *Model) collapseRedirects() map[string]string {
	redirects := map[string]string{}
	for i := range m.Nodes {
		redirects[m.Nodes[i].ID] = m.collapsedOwner(m.Nodes[i].ID)
	}
	for i := range m.Groups {
		redirects[m.Groups[i].ID] = m.collapsedOwner(m.Groups[i].ID)
	}
	return redirects
}

func (m *Model) redirectEdges(redirects map[string]string) []Edge {
	kept := m.Edges[:0]
	for i := range m.Edges {
		if redirectEdge(&m.Edges[i], redirects) {
			kept = append(kept, m.Edges[i])
		}
	}
	return kept
}

func redirectEdge(edge *Edge, redirects map[string]string) bool {
	authoredLoop := edge.From == edge.To
	from, hasFrom := redirects[edge.From]
	to, hasTo := redirects[edge.To]
	if hasFrom && from != "" {
		edge.From = from
	}
	if hasTo && to != "" {
		edge.To = to
	}
	return authoredLoop || edge.From != edge.To || (!hasFrom && !hasTo)
}

func (m *Model) reindexNodes() {
	declarations := make([]Declaration, 0, len(m.Nodes)+len(m.Groups))
	for i := range m.Nodes {
		declarations = append(declarations, Declaration{Node: i})
	}
	for i := range m.Groups {
		declarations = append(declarations, Declaration{Group: i, IsGroup: true})
	}
	sort.SliceStable(declarations, func(a, b int) bool {
		return declarationStart(m, declarations[a]) < declarationStart(m, declarations[b])
	})
	m.Declarations = declarations
}

func declarationStart(m *Model, d Declaration) int {
	if d.IsGroup {
		if d.Group < len(m.Groups) {
			return m.Groups[d.Group].Opening.Start
		}
		return int(^uint(0) >> 1)
	}
	if d.Node < len(m.Nodes) {
		return m.Nodes[d.Node].IDSpan.Start
	}
	return int(^uint(0) >> 1)
}

func reserveIDs(document *synagentflow.Document, reserved map[string]struct{}) {
	for i := range document.Lines {
		if statement := document.Lines[i].Statement; statement != nil {
			reserveStatement(statement, reserved)
		}
	}
}

func reserveStatement(statement *synagentflow.Statement, reserved map[string]struct{}) {
	switch {
	case statement.Kind.Vertex != nil:
		for n := range statement.Kind.Vertex.Nodes {
			for v := range statement.Kind.Vertex.Nodes[n].Vertices {
				reserved[idText(statement.Kind.Vertex.Nodes[n].Vertices[v].Vertex.ID)] = struct{}{}
			}
		}
	case statement.Kind.Flow != nil:
		if statement.Kind.Flow.Name != nil {
			reserved[noTagsText(statement.Kind.Flow.Name)] = struct{}{}
		}
		reserveIDs(&statement.Kind.Flow.Body, reserved)
	case statement.Kind.Global != nil:
		reserveIDs(&statement.Kind.Global.Body, reserved)
	case statement.Kind.Connector != nil:
		reserved[noTagsText(&statement.Kind.Connector.Name)] = struct{}{}
	}
}

func configuredPadding(sourceText string) (int, bool) {
	preprocessed := syn.Preprocess([]byte(sourceText))
	padding, found := 0, false
	for _, config := range []syn.ConfigValue{preprocessed.Config, preprocessed.Init} {
		if value, ok := paddingFromConfig(config); ok {
			padding, found = value, true
		}
	}
	return padding, found
}

func paddingFromConfig(config syn.ConfigValue) (int, bool) {
	if config.Kind != syn.ValueMapping {
		return 0, false
	}
	for _, entry := range config.Entries {
		if entry.Key == "flowchart" {
			return paddingFromFlowchart(entry.Value)
		}
	}
	return 0, false
}

func paddingFromFlowchart(flowchart syn.ConfigValue) (int, bool) {
	if flowchart.Kind != syn.ValueMapping {
		return 0, false
	}
	for _, inner := range flowchart.Entries {
		if inner.Key == "padding" && inner.Value.Kind == syn.ValueInteger {
			value, err := strconv.Atoi(inner.Value.Text)
			if err != nil {
				return 0, false
			}
			return value, true
		}
	}
	return 0, false
}

func canonicalDirection(value string) string {
	switch strings.TrimSpace(value) {
	case "LR", ">":
		return "LR"
	case "RL", "<":
		return "RL"
	case "BT", "^":
		return "BT"
	default:
		return "TB"
	}
}

func textText(value *synagentflow.Text) string {
	return syn.DecodeEntities(strings.TrimSpace(joinTokens(value.Pieces)))
}

func noTagsText(value *synagentflow.TextNoTags) string {
	return syn.DecodeEntities(strings.TrimSpace(joinTokens(value.Pieces)))
}

func stylesList(value *synagentflow.StylesOpt) []string {
	out := make([]string, len(value.Styles))
	for i, style := range value.Styles {
		parts := make([]string, len(style.Components))
		for j, c := range style.Components {
			parts[j] = c.Token.Text
		}
		out[i] = strings.TrimSpace(strings.Join(parts, ""))
	}
	return out
}

func collapsed(flow *Flow) bool {
	for _, entry := range flow.Appearance.Metadata {
		if entry.Key == "view" && valueText(entry.Value) == "collapsed" {
			return true
		}
	}
	return false
}
