package wardley

import (
	"cmp"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/wardley"
)

const (
	configKey    = "wardley-beta"
	maxCanvasPx  = 65536
	maxPaddingPx = 4096
	offsetCap    = int64(1) << 31
	numberCap    = int64(1) << 62
	rangeMessage = " must be between 0-1 (decimal) or 0-100 (percentage). Received: "
)

type resolver struct {
	model    *Model
	diags    []diag.Diagnostic
	nodes    map[string]int
	pipeline map[string]int
	trends   map[string]int
}

func Resolve(src []byte, ast *syn.Wardley) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{}, nodes: map[string]int{}, pipeline: map[string]int{}, trends: map[string]int{}}
	r.readConfig(syntax.Preprocess(src))
	r.metadata(ast.Metadata)
	r.size(ast.Size)
	r.evolution(ast.Evolution)
	r.declareNodes(ast)
	r.retainEvidence(ast)
	r.declareRelations(ast)
	r.declareAnnotations(ast)
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

func (r *resolver) retainEvidence(ast *syn.Wardley) {
	r.model.Header = ast.Header.Span
	reference := func(v syn.Value) Reference {
		if i, ok := r.nodes[v.Text]; ok {
			return Reference{Node: i, Span: v.Span}
		}
		return Reference{Node: -1, Name: v.Text, Span: v.Span}
	}
	record := func(name, visibility, evolution syn.Value) {
		r.model.Declarations = append(r.model.Declarations, Declaration{
			Node: r.nodes[name.Text], Span: name.Span,
			Scale: coordinateScale(visibility.Text) | coordinateScale(evolution.Text),
		})
	}
	for _, a := range ast.Anchors {
		record(a.Name, a.Visibility, a.Evolution)
	}
	for _, c := range ast.Components {
		record(c.Name, c.Visibility, c.Evolution)
	}
	slices.SortFunc(r.model.Declarations, func(a, b Declaration) int { return cmp.Compare(a.Span.Start, b.Span.Start) })
	for _, l := range ast.Links {
		r.model.References = append(r.model.References, reference(l.From), reference(l.To))
	}
	for _, e := range ast.Evolves {
		r.model.References = append(r.model.References, reference(e.Component))
	}
	for _, p := range ast.Pipelines {
		r.model.PipelineUses = append(r.model.PipelineUses, reference(p.Parent))
		for _, c := range p.Components {
			r.model.PipelineUses = append(r.model.PipelineUses, reference(c.Name))
		}
	}
}

func coordinateScale(text string) uint8 {
	text = strings.TrimPrefix(text, "+")
	if strings.HasPrefix(text, "-") {
		return 0
	}
	whole, fraction, _ := strings.Cut(text, ".")
	whole = strings.TrimLeft(whole, "0")
	fraction = strings.Trim(fraction, "0")
	if whole == "" && fraction == "" {
		return 0
	}
	if whole == "" || whole == "1" && fraction == "" {
		return 1
	}
	return 2
}

func (r *resolver) declareNodes(ast *syn.Wardley) {
	for _, a := range ast.Anchors {
		r.anchor(a)
	}
	for _, c := range ast.Components {
		r.component(c)
	}
	for _, n := range ast.Notes {
		r.note(n)
	}
	for _, p := range ast.Pipelines {
		r.pipelineBlock(p)
	}
}

func (r *resolver) declareRelations(ast *syn.Wardley) {
	for _, l := range ast.Links {
		r.link(l)
	}
	for _, e := range ast.Evolves {
		r.evolve(e)
	}
}

func (r *resolver) declareAnnotations(ast *syn.Wardley) {
	r.annotationBox(ast.Annotations)
	for _, a := range ast.Annotation {
		r.annotation(a)
	}
	for _, a := range ast.Accelerators {
		r.model.Accelerators = append(r.model.Accelerators, r.force(syn.Accelerator(a), "Accelerator"))
	}
	for _, d := range ast.Deaccelerators {
		r.model.Deaccelerators = append(r.model.Deaccelerators, r.force(syn.Accelerator(d), "Deaccelerator"))
	}
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func trim(text string) string { return strings.TrimFunc(text, jsSpace) }

func (r *resolver) readConfig(pre syntax.Preprocessed) {
	if pre.HasFront {
		r.readFrontTitle(pre.Root)
	}
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		r.readMap(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = trim(syntax.DecodeEntities(entry.Value.Text))
		}
	}
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"width":   {1, maxCanvasPx},
	"height":  {1, maxCanvasPx},
	"padding": {0, maxPaddingPx},
}

func (r *resolver) readMap(block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == configKey })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		if _, known := integerKeys[field.Key]; known && field.Value.Kind == syntax.ValueInteger && !strings.HasPrefix(field.Value.Text, "-") {
			r.setBounded(field.Key, integer(strings.TrimPrefix(field.Value.Text, "+"), numberCap))
		}
	}
}

func (r *resolver) setBounded(key string, n int64) {
	if bounds := integerKeys[key]; n >= bounds.low && n <= bounds.high {
		r.upsert(key, n)
	}
}

func (r *resolver) upsert(key string, value int64) {
	if i := slices.IndexFunc(r.model.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		r.model.Config[i].Value = value
		return
	}
	r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
}

func (r *resolver) metadata(items []syn.Metadata) {
	last := map[string]string{}
	for _, m := range items {
		last[m.Field] = m.Value
	}
	if v := last["title"]; v != "" {
		r.model.Title = syntax.DecodeEntities(v)
	}
	r.model.AccTitle = last["accTitle"]
	r.model.AccDescr = last["accDescr"]
}

func (r *resolver) size(s *syn.Size) {
	if s == nil {
		return
	}
	r.setBounded("width", integer(s.Width.Text, numberCap))
	r.setBounded("height", integer(s.Height.Text, numberCap))
}

func (r *resolver) evolution(e *syn.Evolution) {
	if e == nil {
		return
	}
	for _, stage := range e.Stages {
		name := trim(stage.Name.Text)
		if stage.SecondName != nil {
			name += " / " + trim(stage.SecondName.Text)
		}
		r.model.Stages = append(r.model.Stages, syntax.DecodeEntities(name))
		if stage.Boundary != nil {
			r.model.Boundaries = append(r.model.Boundaries, parseDecimal(stage.Boundary.Text).scaled(thousandthPlaces))
		}
	}
}

func (r *resolver) percent(v syn.Value, context string) int64 {
	d := parseDecimal(v.Text)
	n, ok := toPercent(d)
	if !ok {
		r.diags = append(r.diags, syn.Diagnostic("wardley/coordinate-out-of-range", context+rangeMessage+d.String(), v.Span))
	}
	return n
}

func (r *resolver) coordinates(visibility, evolution syn.Value, context string) (x, y int64) {
	x = r.percent(evolution, context+" evolution")
	y = r.percent(visibility, context+" visibility")
	return x, y
}

func (r *resolver) addNode(n Node) {
	i, found := r.nodes[n.ID]
	if !found {
		r.nodes[n.ID] = len(r.model.Nodes)
		r.model.Nodes = append(r.model.Nodes, n)
		return
	}
	old := r.model.Nodes[i]
	n.PipelineParent = old.PipelineParent
	if !n.HasOffset {
		n.HasOffset, n.OffsetX, n.OffsetY = old.HasOffset, old.OffsetX, old.OffsetY
	}
	r.model.Nodes[i] = n
}

func (r *resolver) anchor(a syn.Anchor) {
	x, y := r.coordinates(a.Visibility, a.Evolution, `Anchor "`+a.Name.Text+`"`)
	r.addNode(Node{ID: a.Name.Text, Name: a.Name.Text, Label: syntax.DecodeEntities(a.Name.Text), X: x, Y: y, Anchor: true, Span: a.Name.Span})
}

func (r *resolver) component(c syn.Component) {
	x, y := r.coordinates(c.Visibility, c.Evolution, `Component "`+c.Name.Text+`"`)
	n := Node{ID: c.Name.Text, Name: c.Name.Text, Label: syntax.DecodeEntities(c.Name.Text), X: x, Y: y, Inertia: c.Inertia, Span: c.Name.Span}
	applyLabel(&n, c.Label)
	if c.Decorator != nil {
		n.Strategy = strategyOf(c.Decorator.Strategy.Text)
	}
	r.addNode(n)
}

func strategyOf(text string) Strategy {
	switch text {
	case "build":
		return StrategyBuild
	case "buy":
		return StrategyBuy
	case "outsource":
		return StrategyOutsource
	case "market":
		return StrategyMarket
	}
	return StrategyNone
}

func applyLabel(n *Node, label *syn.Label) {
	if label == nil {
		return
	}
	n.HasOffset = true
	n.OffsetX = signed(label.NegX, label.OffsetX.Text)
	n.OffsetY = signed(label.NegY, label.OffsetY.Text)
}

func signed(negative bool, digits string) int64 {
	n := integer(digits, offsetCap)
	if negative {
		return -n
	}
	return n
}

func (r *resolver) note(n syn.Note) {
	x, y := r.coordinates(n.Visibility, n.Evolution, `Note "`+n.Text.Text+`"`)
	r.model.Notes = append(r.model.Notes, Note{Text: syntax.DecodeEntities(n.Text.Text), X: x, Y: y})
}

func (r *resolver) pipelineBlock(p syn.Pipeline) {
	parent, found := r.nodes[p.Parent.Text]
	if !found {
		r.diags = append(r.diags, syn.Diagnostic("wardley/pipeline-parent-unknown", `Pipeline "`+p.Parent.Text+`" must reference an existing component with coordinates.`, p.Parent.Span))
		return
	}
	y := r.model.Nodes[parent].Y
	r.model.Nodes[parent].PipelineParent = true
	members := r.startPipeline(p.Parent.Text)
	for _, c := range p.Components {
		id := p.Parent.Text + "_" + c.Name.Text
		n := Node{ID: id, Name: c.Name.Text, Label: syntax.DecodeEntities(c.Name.Text), Y: y, Span: c.Name.Span}
		n.X = r.percent(c.Evolution, `Pipeline component "`+c.Name.Text+`" evolution`)
		applyLabel(&n, c.Label)
		r.addNode(n)
		*members = append(*members, id)
	}
}

func (r *resolver) startPipeline(node string) *[]string {
	i, found := r.pipeline[node]
	if !found {
		i = len(r.model.Pipelines)
		r.pipeline[node] = i
		r.model.Pipelines = append(r.model.Pipelines, Pipeline{Node: node})
	}
	r.model.Pipelines[i].Components = nil
	return &r.model.Pipelines[i].Components
}

func (r *resolver) resolveName(name string) string {
	if _, found := r.nodes[name]; found {
		return name
	}
	for i := range r.model.Nodes {
		if r.model.Nodes[i].Name == name {
			return r.model.Nodes[i].ID
		}
	}
	return name
}

func (r *resolver) link(l syn.Link) {
	link := Link{Source: r.resolveName(l.From.Text), Target: r.resolveName(l.To.Text), Span: l.Span}
	if l.Arrow != nil {
		link.Dashed = strings.Contains(l.Arrow.Text, "-.->") || strings.Contains(l.Arrow.Text, ".-.")
	}
	flow, flowLabel, flowLabelled := arrowFlow(l.Arrow)
	link.Flow = cmp.Or(portFlow(l.FromPort), portFlow(l.ToPort), flow)
	switch {
	case flowLabelled:
		link.Label = syntax.DecodeEntities(flowLabel)
	case l.LinkLabel != nil:
		link.Label = syntax.DecodeEntities(l.LinkLabel.Text)
	}
	r.model.Links = append(r.model.Links, link)
}

func portFlow(port *syn.Value) Flow {
	if port == nil {
		return FlowNone
	}
	return flowOf(port.Text)
}

func flowOf(text string) Flow {
	switch {
	case strings.Contains(text, "<>"):
		return FlowBidirectional
	case strings.Contains(text, "<"):
		return FlowBackward
	case strings.Contains(text, ">"):
		return FlowForward
	}
	return FlowNone
}

func arrowFlow(arrow *syn.Value) (flow Flow, label string, labelled bool) {
	if arrow == nil || !strings.HasPrefix(arrow.Text, "+") {
		return FlowNone, "", false
	}
	if rest, ok := strings.CutPrefix(arrow.Text, "+'"); ok {
		if end := strings.IndexByte(rest, '\''); end >= 0 {
			label, labelled = rest[:end], true
		}
	}
	return flowOf(arrow.Text), label, labelled
}

func (r *resolver) evolve(e syn.Evolve) {
	i, found := r.nodes[e.Component.Text]
	if !found {
		return
	}
	trend := Trend{Node: e.Component.Text, TargetX: r.percent(e.Target, `Evolve target for "`+e.Component.Text+`"`), TargetY: r.model.Nodes[i].Y}
	if at, replaced := r.trends[trend.Node]; replaced {
		r.model.Trends[at] = trend
		return
	}
	r.trends[trend.Node] = len(r.model.Trends)
	r.model.Trends = append(r.model.Trends, trend)
}

func (r *resolver) annotationBox(boxes []syn.Annotations) {
	if len(boxes) == 0 {
		return
	}
	x, y := r.coordinates(boxes[0].X, boxes[0].Y, "Annotations box")
	r.model.Box = &Point{X: x, Y: y}
}

func (r *resolver) annotation(a syn.Annotation) {
	number := integer(a.Number.Text, numberCap)
	x, y := r.coordinates(a.X, a.Y, "Annotation "+a.Number.Text)
	r.model.Annotations = append(r.model.Annotations, Annotation{Number: number, X: x, Y: y, Text: syntax.DecodeEntities(a.Text.Text)})
}

func (r *resolver) force(f syn.Accelerator, kind string) Force {
	x, y := r.coordinates(f.X, f.Y, kind+` "`+f.Name.Text+`"`)
	return Force{Name: syntax.DecodeEntities(f.Name.Text), X: x, Y: y}
}
