package layout

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	classmodel "github.com/gosuda/elegant-mermaid/internal/model/class"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	classparser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
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
}

func ParseDiagram(src []byte) *Diagram {
	text, bad := source.RepairUTF8(src)
	p := syntax.Preprocess(text)
	detection := syntax.Detect(text, p.Removed)
	d := &Diagram{Source: text, Preprocessing: p, Kind: detection.Kind, Found: detection.Found, Diagnostics: append(p.Diags, detection.Diagnostics...)}
	if bad >= 0 {
		d.Diagnostics = append(d.Diagnostics, diag.Diagnostic{Code: "source/invalid-utf8", Severity: diag.SeverityError, Message: fmt.Sprintf("invalid UTF-8 at byte %d", bad), Span: source.Span{Start: bad, End: bad + 3}, Help: "Save the source as UTF-8."})
	}
	d.resolve()
	diag.Sort(d.Diagnostics)
	return d
}

func (d *Diagram) resolve() {
	var parsed, resolved []diag.Diagnostic
	switch d.Kind {
	case "flowchart":
		ast, ds := flowparser.Parse(d.Source, d.Preprocessing.Removed)
		parsed = ds
		d.flowchart, resolved = flowmodel.Resolve(d.Source, ast)
		d.AccTitle, d.AccDescr = d.flowchart.AccTitle, d.flowchart.AccDescr
	case "class":
		ast, ds := classparser.Parse(d.Source, d.Preprocessing.Removed)
		parsed = ds
		d.class, resolved = classmodel.Resolve(d.Source, ast)
		d.AccTitle, d.AccDescr = d.class.AccTitle, d.class.AccDescr
	}
	d.Diagnostics = append(d.Diagnostics, parsed...)
	d.Diagnostics = append(d.Diagnostics, resolved...)
}

func (d *Diagram) Supported() bool { return d.flowchart != nil || d.class != nil }

func (d *Diagram) Input(profile scene.Profile, options scene.Options) (Input, error) {
	var input Input
	var diagnostics []diag.Diagnostic
	switch d.Kind {
	case "flowchart":
		input, diagnostics = FromFlowchart(d.flowchart, profile, options)
	case "class":
		input, diagnostics = FromClass(d.class, profile, options)
	default:
		return Input{}, fmt.Errorf("unsupported diagram kind: %s", d.Kind)
	}
	for _, diagnostic := range diagnostics {
		if diagnostic.Severity == diag.SeverityError {
			return Input{}, fmt.Errorf("%s: %s", diagnostic.Code, diagnostic.Message)
		}
	}
	return input, nil
}
