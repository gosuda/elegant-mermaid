package layout

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	agentflowmodel "github.com/gosuda/elegant-mermaid/internal/model/agentflow"
	archmodel "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	blockmodel "github.com/gosuda/elegant-mermaid/internal/model/block"
	c4model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	classmodel "github.com/gosuda/elegant-mermaid/internal/model/class"
	cynefinmodel "github.com/gosuda/elegant-mermaid/internal/model/cynefin"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	eventmodel "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	ganttmodel "github.com/gosuda/elegant-mermaid/internal/model/gantt"
	gitmodel "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	infomodel "github.com/gosuda/elegant-mermaid/internal/model/info"
	ishikawamodel "github.com/gosuda/elegant-mermaid/internal/model/ishikawa"
	journeymodel "github.com/gosuda/elegant-mermaid/internal/model/journey"
	kanbanmodel "github.com/gosuda/elegant-mermaid/internal/model/kanban"
	mindmapmodel "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	packetmodel "github.com/gosuda/elegant-mermaid/internal/model/packet"
	piemodel "github.com/gosuda/elegant-mermaid/internal/model/pie"
	quadrantmodel "github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	radarmodel "github.com/gosuda/elegant-mermaid/internal/model/radar"
	railroadmodel "github.com/gosuda/elegant-mermaid/internal/model/railroad"
	reqmodel "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	sankeymodel "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	sequencemodel "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	statemodel "github.com/gosuda/elegant-mermaid/internal/model/state"
	swimlanemodel "github.com/gosuda/elegant-mermaid/internal/model/swimlane"
	timelinemodel "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	treemapmodel "github.com/gosuda/elegant-mermaid/internal/model/treemap"
	usecasemodel "github.com/gosuda/elegant-mermaid/internal/model/usecase"
	vennmodel "github.com/gosuda/elegant-mermaid/internal/model/venn"
	wardleymodel "github.com/gosuda/elegant-mermaid/internal/model/wardley"
	xychartmodel "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	agentflowparser "github.com/gosuda/elegant-mermaid/internal/syntax/agentflow"
	blockparser "github.com/gosuda/elegant-mermaid/internal/syntax/block"
	c4parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
	classparser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
	erparser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
	eventparser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
	gitparser "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
	mindmapparser "github.com/gosuda/elegant-mermaid/internal/syntax/mindmap"
	railroadparser "github.com/gosuda/elegant-mermaid/internal/syntax/railroad"
	reqparser "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
	sequenceparser "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
	stateparser "github.com/gosuda/elegant-mermaid/internal/syntax/state"
	swimlaneparser "github.com/gosuda/elegant-mermaid/internal/syntax/swimlane"
	timelineparser "github.com/gosuda/elegant-mermaid/internal/syntax/timeline"
	usecaseparser "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
	xychartparser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

type Diagram struct {
	Source             []byte
	Preprocessing      syntax.Preprocessed
	Kind               string
	Found              bool
	Diagnostics        []diag.Diagnostic
	AccTitle, AccDescr string
	flowchart          *flowmodel.Model
	class              *classmodel.Model
	c4                 *c4model.Model
	requirement        *reqmodel.Model
	er                 *ermodel.Model
	state              *statemodel.Model
	usecase            *usecasemodel.Model
	agentflow          *agentflowmodel.Model
	swimlane           *swimlanemodel.Model
	sequence           *sequencemodel.Model
	eventmodeling      *eventmodel.Model
	gitgraph           *gitmodel.Model
	mindmap            *mindmapmodel.Model
	ishikawa           *ishikawamodel.Model
	radar              *radarmodel.Model
	railroad           *railroadmodel.Model
	block              *blockmodel.Model
	xychart            *xychartmodel.Model
	timeline           *timelinemodel.Model
	gantt              *ganttmodel.Model
	packet             *packetmodel.Model
	cynefin            *cynefinmodel.Model
	info               *infomodel.Model
	kanban             *kanbanmodel.Model
	quadrant           *quadrantmodel.Model
	treemap            *treemapmodel.Model
	wardley            *wardleymodel.Model
	journey            *journeymodel.Model
	pie                *piemodel.Model
	venn               *vennmodel.Model
	architecture       *archmodel.Model
	treeview           *treeviewModel
	sankey             *sankeymodel.Model
	config             syntax.EffectiveConfig
	baseDiagnostics    []diag.Diagnostic
	edgeSpans          []source.Span
}

func ParseDiagram(src []byte) *Diagram {
	text, bad := source.RepairUTF8(src)
	p := syntax.Preprocess(text)
	detection := syntax.Detect(text, p.Removed)
	d := &Diagram{Source: text, Preprocessing: p, Kind: detection.Kind, Found: detection.Found, Diagnostics: append(p.Diags, detection.Diagnostics...)}
	if bad >= 0 {
		d.Diagnostics = append(d.Diagnostics, diag.Diagnostic{Code: "source/invalid-utf8", Severity: diag.SeverityError, Message: fmt.Sprintf("invalid UTF-8 at byte %d", bad), Span: source.Span{Start: bad, End: bad + 3}, Help: "Save the source as UTF-8."})
	}
	var configDiags []diag.Diagnostic
	d.config, configDiags = syntax.ReadEffectiveConfig(d.configMappings()...)
	d.Diagnostics = append(d.Diagnostics, configDiags...)
	d.resolve()
	d.edgeSpans = d.resolvedEdgeSpans()
	d.baseDiagnostics = d.Diagnostics
	d.Diagnostics = d.DiagnosticsFor(d.config)
	return d
}

type kindBinding struct {
	resolve func(*Diagram) (parsed, resolved []diag.Diagnostic)
	input   func(*Diagram, scene.Profile, scene.Options) (Input, []diag.Diagnostic, error)
}

var kindBindings = map[string]kindBinding{
	"flowchart":     {(*Diagram).resolveFlowchart, (*Diagram).flowchartInput},
	"class":         {(*Diagram).resolveClass, (*Diagram).classInput},
	"c4":            {(*Diagram).resolveC4, (*Diagram).c4Input},
	"requirement":   {(*Diagram).resolveRequirement, (*Diagram).requirementInput},
	"er":            {(*Diagram).resolveER, (*Diagram).erInput},
	"state":         {(*Diagram).resolveState, (*Diagram).stateInput},
	"agentflow":     {(*Diagram).resolveAgentflow, (*Diagram).agentflowInput},
	"usecase":       {(*Diagram).resolveUsecase, (*Diagram).usecaseInput},
	"swimlane":      {(*Diagram).resolveSwimlane, (*Diagram).swimlaneInput},
	"sequence":      {(*Diagram).resolveSequence, (*Diagram).sequenceInput},
	"eventmodeling": {(*Diagram).resolveEventmodeling, (*Diagram).eventmodelingInput},
	"gitgraph":      {(*Diagram).resolveGitgraph, (*Diagram).gitgraphInput},
	"mindmap":       {(*Diagram).resolveMindmap, (*Diagram).mindmapInput},
	"railroad":      {(*Diagram).resolveRailroad, (*Diagram).railroadInput},
	"block":         {(*Diagram).resolveBlock, (*Diagram).blockInput},
	"xychart":       {(*Diagram).resolveXYChart, (*Diagram).xychartInput},
	"gantt":         {(*Diagram).resolveGantt, (*Diagram).ganttInput},
	"timeline":      {(*Diagram).resolveTimeline, (*Diagram).timelineInput},
	"radar":         {(*Diagram).resolveRadar, (*Diagram).radarInput},
	"cynefin":       {(*Diagram).resolveCynefin, (*Diagram).cynefinInput},
	"info":          {(*Diagram).resolveInfo, (*Diagram).infoInput},
	"packet":        {(*Diagram).resolvePacket, (*Diagram).packetInput},
	"kanban":        {(*Diagram).resolveKanban, (*Diagram).kanbanInput},
	"ishikawa":      {(*Diagram).resolveIshikawa, (*Diagram).ishikawaInput},
	"quadrant":      {(*Diagram).resolveQuadrant, (*Diagram).quadrantInput},
	"treemap":       {(*Diagram).resolveTreemap, (*Diagram).treemapInput},
	"wardley":       {(*Diagram).resolveWardley, (*Diagram).wardleyInput},
	"journey":       {(*Diagram).resolveJourney, (*Diagram).journeyInput},
	"pie":           {(*Diagram).resolvePie, (*Diagram).pieInput},
	"venn":          {(*Diagram).resolveVenn, (*Diagram).vennInput},
	"architecture":  {(*Diagram).resolveArchitecture, (*Diagram).architectureInput},
	"treeview":      {(*Diagram).resolveTreeview, (*Diagram).treeviewInput},
	"sankey":        {(*Diagram).resolveSankey, (*Diagram).sankeyInput},
}

func (d *Diagram) resolve() {
	binding, ok := kindBindings[d.Kind]
	if !ok {
		return
	}
	parsed, resolved := binding.resolve(d)
	d.Diagnostics = append(d.Diagnostics, parsed...)
	d.Diagnostics = append(d.Diagnostics, resolved...)
}

func (d *Diagram) Supported() bool {
	_, ok := kindBindings[d.Kind]
	return ok
}

func (d *Diagram) Input(profile scene.Profile, options scene.Options) (Input, error) {
	return d.InputConfigured(profile, options, d.config)
}

func (d *Diagram) InputConfigured(profile scene.Profile, options scene.Options, config syntax.EffectiveConfig) (Input, error) {
	binding, ok := kindBindings[d.Kind]
	if !ok {
		return Input{}, fmt.Errorf("unsupported diagram kind: %s", d.Kind)
	}
	options.FontFamily = config.FontFamily
	input, diagnostics, err := binding.input(d, profile, options)
	if err != nil {
		return Input{}, err
	}
	for _, diagnostic := range diagnostics {
		if diagnostic.Severity == diag.SeverityError {
			return Input{}, fmt.Errorf("%s: %s", diagnostic.Code, diagnostic.Message)
		}
	}
	input.Options = withFontFamily(input.Options, config.FontFamily)
	return input, nil
}

func (d *Diagram) resolveFlowchart() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := flowparser.Parse(d.Source, d.Preprocessing.Removed)
	d.flowchart, resolved = flowmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.flowchart.AccTitle, d.flowchart.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveClass() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := classparser.Parse(d.Source, d.Preprocessing.Removed)
	d.class, resolved = classmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.class.AccTitle, d.class.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveC4() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := c4parser.Parse(d.Source, d.Preprocessing.Removed)
	d.c4, resolved = c4model.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.c4.AccTitle, d.c4.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveRequirement() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := reqparser.Parse(d.Source, d.Preprocessing.Removed)
	d.requirement, resolved = reqmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.requirement.AccTitle, d.requirement.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveER() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := erparser.Parse(d.Source, d.Preprocessing.Removed)
	d.er, resolved = ermodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.er.AccTitle, d.er.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveState() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := stateparser.Parse(d.Source, d.Preprocessing.Removed)
	d.state, resolved = statemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.state.Title(), d.state.Description()
	return parsed, resolved
}

func (d *Diagram) resolveAgentflow() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := agentflowparser.Parse(d.Source, d.Preprocessing.Removed)
	d.agentflow, resolved = agentflowmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.agentflow.AccTitle, d.agentflow.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveUsecase() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := usecaseparser.Parse(d.Source, d.Preprocessing.Removed)
	d.usecase, resolved = usecasemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.usecase.AccTitle, d.usecase.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveSwimlane() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := swimlaneparser.Parse(d.Source, d.Preprocessing.Removed)
	d.swimlane, resolved = swimlanemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.swimlane.Flowchart.AccTitle, d.swimlane.Flowchart.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveSequence() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := sequenceparser.Parse(d.Source, d.Preprocessing.Removed)
	d.sequence, resolved = sequencemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.sequence.AccTitle, d.sequence.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveEventmodeling() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := eventparser.Parse(d.Source, d.Preprocessing.Removed)
	d.eventmodeling, resolved = eventmodel.Resolve(ast)
	return parsed, resolved
}

func (d *Diagram) resolveGitgraph() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := gitparser.Parse(d.Source, d.Preprocessing.Removed)
	d.gitgraph, resolved = gitmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.gitgraph.AccTitle, d.gitgraph.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveMindmap() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := mindmapparser.Parse(d.Source, d.Preprocessing.Removed)
	d.mindmap, resolved = mindmapmodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) resolveRailroad() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := railroadparser.Parse(d.Source, d.Preprocessing.Removed)
	d.railroad, resolved = railroadmodel.Resolve(ast)
	d.AccTitle, d.AccDescr = d.railroad.AccTitle, d.railroad.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveBlock() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := blockparser.Parse(d.Source, d.Preprocessing.Removed)
	d.block, resolved = blockmodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) resolveXYChart() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := xychartparser.Parse(d.Source, d.Preprocessing.Removed)
	d.xychart, resolved = xychartmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.xychart.AccTitle, d.xychart.AccDescr
	return parsed, resolved
}

func (d *Diagram) resolveTimeline() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := timelineparser.Parse(d.Source, d.Preprocessing.Removed)
	d.timeline, resolved = timelinemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.timeline.AccTitle, d.timeline.AccDescr
	return parsed, resolved
}

func (d *Diagram) flowchartInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromFlowchart(d.flowchart, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) classInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromClass(d.class, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) c4Input(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromC4(d.c4, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) requirementInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromRequirement(d.requirement, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) erInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromER(d.er, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) stateInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromState(d.state, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) agentflowInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromAgentflow(d.agentflow, profile, options)
}

func (d *Diagram) usecaseInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromUsecase(d.usecase, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) swimlaneInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromSwimlane(d.swimlane, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) sequenceInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromSequence(d.sequence, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) eventmodelingInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromEventmodeling(d.eventmodeling, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) gitgraphInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromGitgraph(d.gitgraph, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) mindmapInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromMindmap(d.mindmap, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) railroadInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromRailroad(d.railroad, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) blockInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromBlock(d.block, profile, options)
	return input, diagnostics, nil
}

func (d *Diagram) xychartInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromXYChart(d.xychart, profile, options)
}

func (d *Diagram) timelineInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromTimeline(d.timeline, profile, options)
	return input, diagnostics, nil
}
