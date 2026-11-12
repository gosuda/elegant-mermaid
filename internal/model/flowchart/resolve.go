package flowchart

import (
	"strconv"
	"strings"

	evdiag "github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func Resolve(src []byte, file *syn.File) (*Model, []evdiag.Diagnostic) {
	r := &resolver{src: src, model: &Model{Direction: "TB"}, index: map[string]int{}}
	if file != nil {
		r.walk(file)
	}
	diags := r.diags
	evdiag.Sort(diags)
	if diags == nil {
		return r.model, []evdiag.Diagnostic{}
	}
	return r.model, diags
}

type resolver struct {
	src    []byte
	model  *Model
	index  map[string]int
	diags  []evdiag.Diagnostic
	scope  []string
	subCnt int
}

func (r *resolver) walk(file *syn.File) {
	if tok := file.Config.Direction; tok != nil {
		r.model.Direction = resolveDirection(strings.TrimSpace(tok.Text))
		r.model.DirectionSpan = tok.Span
	}
	for _, line := range file.Doc.Lines {
		r.statement(line.Stmt)
	}
}

func resolveDirection(text string) string {
	switch {
	case strings.Contains(text, "<"):
		return "RL"
	case strings.Contains(text, "^"):
		return "BT"
	case strings.Contains(text, ">"):
		return "LR"
	case strings.Contains(text, "v"):
		return "TB"
	}
	switch text {
	case "BT":
		return "BT"
	case "LR":
		return "LR"
	case "RL":
		return "RL"
	}
	return "TB"
}

func (r *resolver) statement(stmt syn.Stmt) {
	switch s := stmt.(type) {
	case *syn.VertexStatement:
		r.vertexStatement(s)
	case *syn.Subgraph:
		r.subgraph(s)
	case *syn.StyleStatement:
		r.styleStatement(s)
	case *syn.ClassDefStatement:
		r.classDefStatement(s)
	case *syn.ClassStatement:
		r.classStatement(s)
	case *syn.LinkStyleStatement:
		r.linkStyleStatement(s)
	case *syn.ClickStatement:
		r.clickStatement(s)
	default:
		r.accessibilityStatement(stmt)
	}
}

func (r *resolver) accessibilityStatement(stmt syn.Stmt) {
	switch s := stmt.(type) {
	case *syn.AccTitle:
		r.model.AccTitle = resolveLabel(s.Value.Text)
	case *syn.AccDescr:
		r.model.AccDescr = resolveLabel(s.Value.Text)
	case *syn.AccDescrBlock:
		r.model.AccDescr = resolveLabel(s.Value.Text)
	}
}

func (r *resolver) vertexStatement(s *syn.VertexStatement) {
	prev := r.nodeGroup(s.Groups[0])
	for i := range s.Links {
		next := r.nodeGroup(s.Groups[i+1])
		r.model.Edges = append(r.model.Edges, buildEdge(s.Links[i], prev[len(prev)-1], next[0]))
		prev = next
	}
}

func (r *resolver) nodeGroup(g syn.NodeGroup) []string {
	ids := make([]string, len(g.Vertices))
	for i := range g.Vertices {
		ids[i] = r.styledVertex(&g.Vertices[i])
	}
	return ids
}

func (r *resolver) nodeIndex(id string, at source.Span) int {
	if idx, ok := r.index[id]; ok {
		return idx
	}
	r.index[id] = len(r.model.Nodes)
	r.model.Nodes = append(r.model.Nodes, Node{ID: id, Shape: "squareRect", First: at, Span: at})
	return len(r.model.Nodes) - 1
}

func (r *resolver) styledVertex(sv *syn.StyledVertex) string {
	id := sv.Vertex.ID.String()
	if sv.ShapeData != nil && r.referenceData(id, sv.ShapeData) {
		return id
	}
	node := &r.model.Nodes[r.nodeIndex(id, sv.Vertex.ID.Span)]
	node.Span = sv.Span
	if sv.Vertex.Label {
		node.Label = resolveLabel(sv.Vertex.Text.String())
		node.LabelKind = labelKindOf(sv.Vertex.Text.Kind)
		node.Shape = sv.Vertex.Shape
	}
	if sv.Class != nil {
		node.Classes = append(node.Classes, sv.Class.String())
	}
	if len(r.scope) > 0 {
		r.joinGroup(id, r.scope[len(r.scope)-1])
	}
	if sv.ShapeData != nil {
		r.applyShapeData(node, sv.ShapeData)
	}
	return id
}

func (r *resolver) joinGroup(id, group string) {
	for i := range r.model.Groups {
		if r.model.Groups[i].ID != group {
			continue
		}
		for _, member := range r.model.Groups[i].Members {
			if member == id {
				return
			}
		}
		r.model.Groups[i].Members = append(r.model.Groups[i].Members, id)
		return
	}
}

func (r *resolver) subgraph(s *syn.Subgraph) {
	index := r.subCnt
	r.subCnt++
	id, title := subgraphIDTitle(s, index)
	group := Group{ID: id, Title: resolveLabel(title), Span: s.Span}
	if len(r.scope) > 0 {
		group.Parent = r.scope[len(r.scope)-1]
	}
	if s.Direction != nil {
		group.Direction = directionOf(s.Direction.Value.Kind)
		group.DirSpan = s.Direction.Bounds()
	}
	if existing, ok := r.groupIndex(id); ok {
		r.model.Groups[existing].Title = group.Title
		r.model.Groups[existing].Direction = group.Direction
		r.model.Groups[existing].DirSpan = group.DirSpan
	} else {
		r.model.Groups = append(r.model.Groups, group)
	}
	r.scope = append(r.scope, id)
	for _, line := range s.Body {
		r.statement(line.Stmt)
	}
	r.scope = r.scope[:len(r.scope)-1]
}

func (r *resolver) groupIndex(id string) (int, bool) {
	for i := range r.model.Groups {
		if r.model.Groups[i].ID == id {
			return i, true
		}
	}
	return 0, false
}

func subgraphIDTitle(s *syn.Subgraph, index int) (string, string) {
	if s.ID == nil {
		return "subGraph" + strconv.Itoa(index), ""
	}
	text := strings.TrimSpace(s.ID.String())
	if s.Title != nil {
		return text, s.Title.String()
	}
	return text, text
}

func directionOf(k syn.TokenKind) string {
	switch k {
	case syn.TokDirectionTB, syn.TokDirectionTD:
		return "TB"
	case syn.TokDirectionBT:
		return "BT"
	case syn.TokDirectionRL:
		return "RL"
	case syn.TokDirectionLR:
		return "LR"
	}
	return ""
}

func (r *resolver) styleStatement(s *syn.StyleStatement) {
	for _, target := range s.Targets {
		id := target.String()
		node := &r.model.Nodes[r.nodeIndex(id, target.Span)]
		node.Styles = resolveStyles(s.Styles)
		r.model.StyleTargets = append(r.model.StyleTargets, StyleTarget{ID: id, Styles: resolveStyles(s.Styles), Span: s.Bounds()})
	}
}

func (r *resolver) classDefStatement(s *syn.ClassDefStatement) {
	def := ClassDef{Styles: resolveStyles(s.Styles), Span: s.Bounds()}
	for _, name := range s.Names {
		def.Names = append(def.Names, splitList(name.String())...)
	}
	r.model.ClassDefs = append(r.model.ClassDefs, def)
}

func (r *resolver) classStatement(s *syn.ClassStatement) {
	class := s.Class.String()
	for _, target := range s.Targets {
		for _, id := range splitList(target.String()) {
			node := &r.model.Nodes[r.nodeIndex(id, target.Span)]
			node.Classes = append(node.Classes, class)
		}
	}
}

func splitList(text string) []string {
	parts := strings.Split(text, ",")
	out := parts[:0]
	for _, part := range parts {
		if trimmed := strings.TrimSpace(part); trimmed != "" {
			out = append(out, trimmed)
		}
	}
	return out
}

func (r *resolver) linkStyleStatement(s *syn.LinkStyleStatement) {
	style := LinkStyle{Default: s.Default, Span: s.Bounds()}
	if s.Styles != nil {
		style.Styles = resolveStyles(*s.Styles)
	}
	if s.Interpolation != nil {
		style.Interpolation = s.Interpolation.String()
	}
	for _, num := range s.Indices.Numbers {
		value, err := strconv.Atoi(num.Text)
		if err != nil {
			continue
		}
		if value < 0 || value >= len(r.model.Edges) {
			r.diags = append(r.diags, plainDiag(codeLinkStyleIDUnknown, num.Span))
			continue
		}
		style.Indices = append(style.Indices, value)
	}
	r.model.LinkStyles = append(r.model.LinkStyles, style)
}

func (r *resolver) clickStatement(s *syn.ClickStatement) {
	click := Click{Target: s.Target.String(), Span: s.Bounds()}
	if s.Callback != nil {
		click.Callback = s.Callback.Name.Text
		if s.Callback.Args != nil {
			click.Args = strings.TrimSpace(s.Callback.Args.Text)
		}
	}
	if s.Link != nil {
		click.Href = s.Link.Href != nil
		click.URL = s.Link.URL.String()
		if s.Link.Tip != nil {
			click.Tip = s.Link.Tip.String()
		}
	}
	r.model.Clicks = append(r.model.Clicks, click)
}

func buildEdge(link syn.Link, from, to string) Edge {
	edge := Edge{From: from, To: to, Stroke: "normal", Marker: "none", Span: link.Span}
	if link.Statement.ID != nil {
		edge.UserID = link.Statement.ID.String()
	}
	readHalves(link.Statement, &edge)
	if link.Edge != nil {
		edge.Label = resolveLabel(link.Edge.Text.String())
		edge.LabelOK = true
		edge.Labels = labelKindOf(link.Edge.Text.Kind)
	}
	if link.Arrow != nil {
		edge.Label = resolveLabel(link.Arrow.Text.String())
		edge.LabelOK = true
		edge.Labels = labelKindOf(link.Arrow.Text.Kind)
	}
	return edge
}

func readHalves(stmt syn.LinkStatement, edge *Edge) {
	end := stmt.Open
	if stmt.End != nil {
		end = *stmt.End
	}
	endBody := strings.TrimSpace(end.Text)
	edge.Stroke = strokeOf(endBody)
	edge.Length = edgeLength(endBody)
	startBody := strings.TrimSpace(stmt.Open.Text)
	edge.Start, edge.Marker = "none", "none"
	if startBody == "" || endBody == "" {
		return
	}
	startKind := markerName(startBody[0])
	endKind := endMarker(endBody)
	if strokeOf(startBody) != edge.Stroke || startKind != "none" && startKind != endKind {
		return
	}
	edge.Start, edge.Marker = startKind, endKind
}

func endMarker(body string) string {
	if body == "" {
		return "none"
	}
	return markerName(body[len(body)-1])
}

func strokeOf(body string) string {
	switch {
	case strings.Contains(body, "~"):
		return "invisible"
	case strings.Contains(body, "="):
		return "thick"
	case strings.Contains(body, "."):
		return "dotted"
	}
	return "normal"
}

func markerName(b byte) string {
	switch b {
	case '<', '>':
		return "point"
	case 'x':
		return "cross"
	case 'o':
		return "circle"
	}
	return "none"
}

func edgeLength(body string) int {
	if dots := strings.Count(body, "."); dots > 0 {
		return min(dots, 10)
	}
	count := strings.Count(body, "-") + strings.Count(body, "=") + strings.Count(body, ".")
	if count <= 1 {
		return 0
	}
	return min(count-1, 10)
}

func plainDiag(code string, span source.Span) evdiag.Diagnostic {
	return evdiag.Diagnostic{Code: code, Severity: evdiag.SeverityError, Message: modelMessage(code), Span: span}
}

func modelMessage(code string) string {
	switch code {
	case codeLinkStyleIDUnknown:
		return "linkStyle references an edge id that no link defines"
	case codeTypedShapeUnsupported:
		return "A typed shape in an @{ shape: ... } node is not supported"
	}
	return ""
}
