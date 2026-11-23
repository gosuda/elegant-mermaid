package flowchart

import (
	"slices"
	"strconv"
	"strings"

	evdiag "github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func Resolve(src []byte, file *syn.File) (*Model, []evdiag.Diagnostic) {
	r := &resolver{src: src, model: &Model{Direction: "TB"}, index: map[string]int{}, owners: map[string]string{}}
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
	owners map[string]string
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
		edge := buildEdge(s.Links[i], prev[len(prev)-1], next[0])
		edge.StatementSpan = s.Bounds()
		r.model.Edges = append(r.model.Edges, edge)
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

func declOf(sv *syn.StyledVertex) Decl {
	d := Decl{ID: sv.Vertex.ID.Span}
	if sv.Vertex.Label {
		d.Label, d.HasLabel = resolveLabel(sv.Vertex.Text.String()), true
	}
	return d
}

func (r *resolver) styledVertex(sv *syn.StyledVertex) string {
	if span, found := unquotedAt(&sv.Vertex); found {
		r.model.UnquotedAtSpans = append(r.model.UnquotedAtSpans, span)
	}
	id := sv.Vertex.ID.String()
	if slices.Contains(r.scope, id) {
		r.model.SubgraphCollisions = append(r.model.SubgraphCollisions, sv.Vertex.ID.Span)
	}
	if sv.ShapeData != nil && r.referenceData(id, sv.ShapeData) {
		return id
	}
	node := &r.model.Nodes[r.nodeIndex(id, sv.Vertex.ID.Span)]
	node.Span = sv.Span
	node.Decls = append(node.Decls, declOf(sv))
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

func unquotedAt(v *syn.Vertex) (source.Span, bool) {
	if !v.Label || v.Text.Kind != syn.LabelPlain ||
		!slices.Contains([]string{"squareRect", "stadium", "subroutine", "cylinder"}, v.Shape) {
		return source.Span{}, false
	}
	trimmed := strings.TrimSpace(v.Text.String())
	if strings.IndexAny(trimmed, `/\`) == 0 && strings.LastIndexAny(trimmed, `/\`) == len(trimmed)-1 {
		return source.Span{}, false
	}
	for _, tok := range v.Text.Tokens {
		if tok.Kind == syn.TokStr || tok.Kind == syn.TokMDStr {
			continue
		}
		if off := strings.IndexByte(tok.Text, '@'); off >= 0 {
			return source.Span{Start: tok.Span.Start + off, End: tok.Span.Start + off + 1}, true
		}
	}
	return source.Span{}, false
}

func (r *resolver) joinGroup(id, group string) {
	for _, existing := range r.model.Groups {
		if existing.ID == group && slices.Contains(existing.Members, id) {
			return
		}
	}
	for i := range r.model.Groups {
		if r.model.Groups[i].ID != group {
			continue
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
	if _, ok := r.groupIndex(id); !ok {
		r.model.Groups = append(r.model.Groups, group)
	}
	r.scope = append(r.scope, id)
	for _, line := range s.Body {
		r.statement(line.Stmt)
	}
	r.scope = r.scope[:len(r.scope)-1]
	r.finishGroup(id)
}

func (r *resolver) groupIndex(id string) (int, bool) {
	for i := range r.model.Groups {
		if r.model.Groups[i].ID == id {
			return i, true
		}
	}
	return 0, false
}

func (r *resolver) finishGroup(id string) {
	index, ok := r.groupIndex(id)
	if !ok {
		return
	}
	r.model.Groups[index].Members = slices.DeleteFunc(r.model.Groups[index].Members, func(member string) bool {
		if owner, exists := r.owners[member]; exists && owner != id {
			return true
		}
		r.owners[member] = id
		return member == id
	})
}

func subgraphIDTitle(s *syn.Subgraph, index int) (string, string) {
	if s.ID == nil {
		return "subGraph" + strconv.Itoa(index), ""
	}
	text := strings.TrimSpace(s.ID.String())
	if s.Title != nil {
		return text, s.Title.String()
	}
	if strings.ContainsAny(text, " \t\r\n\v\f") {
		return "subGraph" + strconv.Itoa(index), text
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
		for _, id := range splitList(target.String()) {
			node := &r.model.Nodes[r.nodeIndex(id, target.Span)]
			styles := resolveStyles(s.Styles)
			node.Styles.Styles = append(node.Styles.Styles, styles.Styles...)
			r.model.StyleTargets = append(r.model.StyleTargets, StyleTarget{ID: id, Styles: styles, Span: s.Bounds()})
		}
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
		click.Kind = ClickCallback
		click.Callback = s.Callback.Name.Text
		click.ActionSpan = s.Callback.Name.Span
		if s.Callback.Args != nil {
			click.Args = strings.TrimSpace(s.Callback.Args.Text)
		}
	}
	if s.Link != nil {
		r.clickLink(&click, s.Link)
	}
	r.model.Clicks = append(r.model.Clicks, click)
	r.diags = append(r.diags, interactionDiagnostics(click)...)
}

func (r *resolver) clickLink(click *Click, link *syn.LinkAction) {
	if link.Href == nil && !link.URL.Quoted() {
		click.Kind = ClickCallback
		click.Callback = link.URL.String()
	} else {
		click.URL = link.URL.String()
		click.Href = link.Href != nil
	}
	click.ActionSpan = link.URL.Span
	if link.Tip != nil {
		click.Tip = link.Tip.String()
	}
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
	return evdiag.Diagnostic{Code: code, Severity: evdiag.SeverityError, Message: modelMessage(code), Span: span, Help: modelHelp(code)}
}

func modelHelp(code string) string {
	switch code {
	case codeLinkStyleIDUnknown:
		return "Attach the id to a link first, as in e1@-->, before styling it."
	case codeTypedShapeUnsupported:
		return "Use one of the supported shape names such as rect, rounded, diamond, or circle."
	}
	return ""
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
