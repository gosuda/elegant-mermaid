package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
)

func eventmodelingUndefinedFrame(document *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, frame := range document.Frames {
		for _, ref := range frame.Sources {
			if ref.Source < 0 {
				out = append(out, diagnostic(row, row.Summary, ref.Span))
			}
		}
	}
	return out
}

func eventmodelingInvalidFlow(document *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, target := range document.Frames {
		for _, ref := range target.Sources {
			if ref.Source < 0 {
				continue
			}
			name := document.Frames[ref.Source].Name
			for _, src := range document.Frames {
				if src.Name == name && !eventmodelingAllowed(src.Type, target.Type) {
					out = append(out, diagnostic(row, row.Summary, ref.Span))
					break
				}
			}
		}
	}
	return out
}

func eventmodelingAllowed(from, to string) bool {
	switch to {
	case "cmd", "command":
		return from == "ui" || from == "pcr" || from == "processor"
	case "evt", "event":
		return from == "cmd" || from == "command"
	case "rmo", "readmodel":
		return from == "evt" || from == "event"
	case "pcr", "processor", "ui":
		return from == "rmo" || from == "readmodel"
	}
	return false
}
