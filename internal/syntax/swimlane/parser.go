// Package swimlane parses the swimlane kind: the flowchart grammar with the
// swimlane-beta header. The normative text is spec/grammar/swimlane.md.
package swimlane

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

const (
	flowchartPrefix = "flowchart/"
	swimlanePrefix  = "swimlane/"
)

// Parse parses src with the flowchart parser, skipping the removed spans that
// preprocessing found, and renames every kind-specific diagnostic to the swimlane
// prefix.
func Parse(src []byte, removed []source.Span) (*flowparser.File, []diag.Diagnostic) {
	file, diagnostics := flowparser.Parse(src, removed)
	for i := range diagnostics {
		remap(&diagnostics[i])
	}
	return file, diagnostics
}

func remap(d *diag.Diagnostic) {
	name, ok := strings.CutPrefix(d.Code, flowchartPrefix)
	if !ok {
		return
	}
	for i := range gen.Diagnostics {
		if suffix, found := strings.CutPrefix(gen.Diagnostics[i].Code, swimlanePrefix); found && suffix == name {
			d.Code = gen.Diagnostics[i].Code
			break
		}
	}
	d.Help = helpText(d.Code)
}

func helpText(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}
