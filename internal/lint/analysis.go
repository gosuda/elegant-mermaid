package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	architecturemodel "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	blockmodel "github.com/gosuda/elegant-mermaid/internal/model/block"
	c4model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	classmodel "github.com/gosuda/elegant-mermaid/internal/model/class"
	ermodel "github.com/gosuda/elegant-mermaid/internal/model/er"
	eventmodelingmodel "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	ganttmodel "github.com/gosuda/elegant-mermaid/internal/model/gantt"
	gitgraphmodel "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	ishikawamodel "github.com/gosuda/elegant-mermaid/internal/model/ishikawa"
	journeymodel "github.com/gosuda/elegant-mermaid/internal/model/journey"
	kanbanmodel "github.com/gosuda/elegant-mermaid/internal/model/kanban"
	mindmapmodel "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	packetmodel "github.com/gosuda/elegant-mermaid/internal/model/packet"
	piemodel "github.com/gosuda/elegant-mermaid/internal/model/pie"
	quadrantmodel "github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	radarmodel "github.com/gosuda/elegant-mermaid/internal/model/radar"
	requirementmodel "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	sankeymodel "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	sequencemodel "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	statemodel "github.com/gosuda/elegant-mermaid/internal/model/state"
	timelinemodel "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	treemapmodel "github.com/gosuda/elegant-mermaid/internal/model/treemap"
	treeviewmodel "github.com/gosuda/elegant-mermaid/internal/model/treeview"
	vennmodel "github.com/gosuda/elegant-mermaid/internal/model/venn"
	wardleymodel "github.com/gosuda/elegant-mermaid/internal/model/wardley"
	xychartmodel "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	architectureparser "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
	blockparser "github.com/gosuda/elegant-mermaid/internal/syntax/block"
	c4parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
	classparser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
	erparser "github.com/gosuda/elegant-mermaid/internal/syntax/er"
	eventparser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
	ganttparser "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
	gitgraphparser "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
	ishikawaparser "github.com/gosuda/elegant-mermaid/internal/syntax/ishikawa"
	journeyparser "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
	kanbanparser "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
	mindmapparser "github.com/gosuda/elegant-mermaid/internal/syntax/mindmap"
	packetparser "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
	pieparser "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
	quadrantparser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
	radarparser "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
	requirementparser "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
	sankeyparser "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
	sequenceparser "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
	stateparser "github.com/gosuda/elegant-mermaid/internal/syntax/state"
	timelineparser "github.com/gosuda/elegant-mermaid/internal/syntax/timeline"
	treemapparser "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
	treeviewparser "github.com/gosuda/elegant-mermaid/internal/syntax/treeview"
	vennparser "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
	wardleyparser "github.com/gosuda/elegant-mermaid/internal/syntax/wardley"
	xychartparser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

type Block struct {
	Source     []byte
	HostOffset int
	Token      string
	Header     source.Span
	Kind       string
	Found      bool
	Removed    []source.Span
}

type Analysis struct {
	Source            []byte
	Syntax            []diag.Diagnostic
	BodyStart         int
	Block             Block
	flow              *flowmodel.Model
	flowReady         bool
	xychartModel      *xychartmodel.Model
	timelineFile      *timelineparser.Start
	timelineModel     *timelinemodel.Model
	packetFile        *packetparser.Start
	packetModel       *packetmodel.Model
	radarModel        *radarmodel.Model
	sequenceFile      *sequenceparser.Start
	sequenceModel     *sequencemodel.Model
	gitgraphFile      *gitgraphparser.Start
	gitgraphModel     *gitgraphmodel.Model
	mindmapFile       *mindmapparser.Start
	mindmapModel      *mindmapmodel.Model
	blockFile         *blockparser.Start
	blockModel        *blockmodel.Model
	eventModel        *eventmodelingmodel.Model
	kindReady         bool
	classModel        *classmodel.Model
	stateModel        *statemodel.Model
	erModel           *ermodel.Model
	requirementModel  *requirementmodel.Model
	c4Model           *c4model.Model
	treeviewFile      *treeviewparser.TreeView
	treeviewModel     *treeviewmodel.Model
	ishikawaFile      *ishikawaparser.Start
	ishikawaModel     *ishikawamodel.Model
	kanbanFile        *kanbanparser.Start
	kanbanModel       *kanbanmodel.Model
	architectureModel *architecturemodel.Model
	treemapModel      *treemapmodel.Model
	sankeyFile        *sankeyparser.Start
	sankeyModel       *sankeymodel.Model
	pieModel          *piemodel.Model
	vennModel         *vennmodel.Model
	journeyModel      *journeymodel.Model
	ganttFile         *ganttparser.Start
	ganttModel        *ganttmodel.Model
	quadrantModel     *quadrantmodel.Model
	wardleyModel      *wardleymodel.Model
}

func Analyze(src []byte) *Analysis {
	return AnalyzeDiagram(layout.ParseDiagram(src))
}

func AnalyzeDiagram(d *layout.Diagram) *Analysis {
	detection := syntax.Detect(d.Source, d.Preprocessing.Removed)
	return &Analysis{
		Source:    d.Source,
		Syntax:    d.Diagnostics,
		BodyStart: d.Preprocessing.BodyStart,
		Block: Block{
			Source:  d.Source,
			Token:   string(d.Source[detection.Header.Start:detection.Header.End]),
			Header:  detection.Header,
			Kind:    d.Kind,
			Found:   d.Found,
			Removed: d.Preprocessing.Removed,
		},
	}
}

func (a *Analysis) Flowchart() *flowmodel.Model {
	a.parseFlowchart()
	return a.flow
}

func (a *Analysis) parseFlowchart() {
	if a.flowReady {
		return
	}
	file, _ := flowparser.Parse(a.Source, a.Block.Removed)
	a.flow, _ = flowmodel.Resolve(a.Source, file)
	a.flowReady = true
}

func (a *Analysis) parseKind() {
	if a.kindReady {
		return
	}
	a.kindReady = true
	if a.parseGridAndPartition() {
		return
	}
	if a.parseChartKinds() {
		return
	}
	if a.parseLayeredKinds() {
		return
	}
	if a.parseLaneAndTreeKinds() {
		return
	}
}

func (a *Analysis) parseGridAndPartition() bool {
	switch a.Block.Kind {
	case "treeview":
		a.treeviewFile, _ = treeviewparser.Parse(a.Source, a.Block.Removed)
		a.treeviewModel, _ = treeviewmodel.Resolve(a.Source, a.treeviewFile)
	case "ishikawa":
		a.ishikawaFile, _ = ishikawaparser.Parse(a.Source, a.Block.Removed)
		a.ishikawaModel, _ = ishikawamodel.Resolve(a.Source, a.ishikawaFile)
	case "kanban":
		a.kanbanFile, _ = kanbanparser.Parse(a.Source, a.Block.Removed)
		a.kanbanModel, _ = kanbanmodel.Resolve(a.Source, a.kanbanFile)
	case "architecture":
		file, _ := architectureparser.Parse(a.Source, a.Block.Removed)
		a.architectureModel, _ = architecturemodel.Resolve(a.Source, file)
	case "treemap":
		file, _ := treemapparser.Parse(a.Source, a.Block.Removed)
		a.treemapModel, _ = treemapmodel.Resolve(a.Source, file)
	case "sankey":
		a.sankeyFile, _ = sankeyparser.Parse(a.Source, a.Block.Removed)
		a.sankeyModel, _ = sankeymodel.Resolve(a.Source, a.sankeyFile)
	default:
		return false
	}
	return true
}

func (a *Analysis) parseChartKinds() bool {
	switch a.Block.Kind {
	case "pie":
		file, _ := pieparser.Parse(a.Source, a.Block.Removed)
		a.pieModel, _ = piemodel.Resolve(a.Source, file)
	case "venn":
		file, _ := vennparser.Parse(a.Source, a.Block.Removed)
		a.vennModel, _ = vennmodel.Resolve(a.Source, file)
	case "journey":
		file, _ := journeyparser.Parse(a.Source, a.Block.Removed)
		a.journeyModel, _ = journeymodel.Resolve(a.Source, file)
	case "gantt":
		a.ganttFile, _ = ganttparser.Parse(a.Source, a.Block.Removed)
		a.ganttModel, _ = ganttmodel.Resolve(a.Source, a.ganttFile)
	case "quadrant":
		file, _ := quadrantparser.Parse(a.Source, a.Block.Removed)
		a.quadrantModel, _ = quadrantmodel.Resolve(a.Source, file)
	case "wardley":
		file, _ := wardleyparser.Parse(a.Source, a.Block.Removed)
		a.wardleyModel, _ = wardleymodel.Resolve(a.Source, file)
	default:
		return false
	}
	return true
}

func (a *Analysis) parseLayeredKinds() bool {
	switch a.Block.Kind {
	case "class":
		file, _ := classparser.Parse(a.Source, a.Block.Removed)
		a.classModel, _ = classmodel.Resolve(a.Source, file)
	case "state":
		file, _ := stateparser.Parse(a.Source, a.Block.Removed)
		a.stateModel, _ = statemodel.Resolve(a.Source, file)
	case "er":
		file, _ := erparser.Parse(a.Source, a.Block.Removed)
		a.erModel, _ = ermodel.Resolve(a.Source, file)
	case "requirement":
		file, _ := requirementparser.Parse(a.Source, a.Block.Removed)
		a.requirementModel, _ = requirementmodel.Resolve(a.Source, file)
	case "c4":
		file, _ := c4parser.Parse(a.Source, a.Block.Removed)
		a.c4Model, _ = c4model.Resolve(a.Source, file)
	default:
		return false
	}
	return true
}

func (a *Analysis) parseLaneAndTreeKinds() bool {
	switch a.Block.Kind {
	case "xychart":
		file, _ := xychartparser.Parse(a.Source, a.Block.Removed)
		a.xychartModel, _ = xychartmodel.Resolve(a.Source, file)
	case "timeline":
		a.timelineFile, _ = timelineparser.Parse(a.Source, a.Block.Removed)
		a.timelineModel, _ = timelinemodel.Resolve(a.Source, a.timelineFile)
	case "packet":
		a.packetFile, _ = packetparser.Parse(a.Source, a.Block.Removed)
		a.packetModel, _ = packetmodel.Resolve(a.Source, a.packetFile)
	case "radar":
		file, _ := radarparser.Parse(a.Source, a.Block.Removed)
		a.radarModel, _ = radarmodel.Resolve(a.Source, file)
	case "sequence":
		a.sequenceFile, _ = sequenceparser.Parse(a.Source, a.Block.Removed)
		a.sequenceModel, _ = sequencemodel.Resolve(a.Source, a.sequenceFile)
	case "gitgraph":
		a.gitgraphFile, _ = gitgraphparser.Parse(a.Source, a.Block.Removed)
		a.gitgraphModel, _ = gitgraphmodel.Resolve(a.Source, a.gitgraphFile)
	case "mindmap":
		a.mindmapFile, _ = mindmapparser.Parse(a.Source, a.Block.Removed)
		a.mindmapModel, _ = mindmapmodel.Resolve(a.Source, a.mindmapFile)
	case "block":
		a.blockFile, _ = blockparser.Parse(a.Source, a.Block.Removed)
		a.blockModel, _ = blockmodel.Resolve(a.Source, a.blockFile)
	case "eventmodeling":
		file, _ := eventparser.Parse(a.Source, a.Block.Removed)
		a.eventModel, _ = eventmodelingmodel.Resolve(file)
	default:
		return false
	}
	return true
}
