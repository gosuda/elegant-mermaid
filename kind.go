package mermaid

type Kind uint8

const (
	KindFlowchart Kind = iota
	KindSwimlane
	KindAgentflow
	KindClass
	KindState
	KindEr
	KindRequirement
	KindUsecase
	KindC4
	KindSequence
	KindBlock
	KindArchitecture
	KindKanban
	KindPacket
	KindMindmap
	KindTreeview
	KindIshikawa
	KindGitgraph
	KindEventmodeling
	KindTimeline
	KindJourney
	KindGantt
	KindXychart
	KindQuadrant
	KindTreemap
	KindWardley
	KindPie
	KindRadar
	KindSankey
	KindVenn
	KindCynefin
	KindRailroad
	KindInfo
)

var kindIDs = [...]string{
	"flowchart",
	"swimlane",
	"agentflow",
	"class",
	"state",
	"er",
	"requirement",
	"usecase",
	"c4",
	"sequence",
	"block",
	"architecture",
	"kanban",
	"packet",
	"mindmap",
	"treeview",
	"ishikawa",
	"gitgraph",
	"eventmodeling",
	"timeline",
	"journey",
	"gantt",
	"xychart",
	"quadrant",
	"treemap",
	"wardley",
	"pie",
	"radar",
	"sankey",
	"venn",
	"cynefin",
	"railroad",
	"info",
}

func (k Kind) String() string {
	if int(k) < len(kindIDs) {
		return kindIDs[k]
	}
	return "unknown"
}
