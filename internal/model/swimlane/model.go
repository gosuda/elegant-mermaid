// Package swimlane resolves a swimlane document into its model: the flowchart
// resolution with lane order. Each top-level subgraph is one lane; the lane order is
// the order of the first subgraph openings, which is the order of the flowchart
// model's groups with an empty parent.
package swimlane

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

// Model is the resolved swimlane model.
type Model struct {
	// Flowchart is the flowchart resolution of the same source.
	Flowchart *flowmodel.Model
}

// Resolve resolves the swimlane document into its model.
func Resolve(src []byte, file *flowparser.File) (*Model, []diag.Diagnostic) {
	flowchart, diagnostics := flowmodel.Resolve(src, file)
	return &Model{Flowchart: flowchart}, diagnostics
}

// Lanes returns the top-level lane ids in first-opening declaration order.
func (m *Model) Lanes() []string {
	var lanes []string
	for i := range m.Flowchart.Groups {
		if m.Flowchart.Groups[i].Parent == "" {
			lanes = append(lanes, m.Flowchart.Groups[i].ID)
		}
	}
	return lanes
}
