package railroad

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/railroad"
)

const (
	codeNoRules         = "railroad/no-rules"
	codeRepeatMax       = "railroad/repeat-max-ignored"
	Unbounded     int64 = -1
)

type Node interface {
	node()
}

type Terminal struct{ Value string }

type NonTerminal struct{ Name string }

type Special struct{ Text string }

type Sequence struct{ Elements []Node }

type Choice struct{ Alternatives []Node }

type Optional struct{ Element Node }

type Repetition struct {
	Element Node
	Min     int64
	Max     int64
}

func (*Terminal) node()    {}
func (*NonTerminal) node() {}
func (*Special) node()     {}
func (*Sequence) node()    {}
func (*Choice) node()      {}
func (*Optional) node()    {}
func (*Repetition) node()  {}

type Rule struct {
	Name       string
	Index      int
	Definition Node
	Span       source.Span
}

type Model struct {
	Notation syntax.Notation
	Title    string
	AccTitle string
	AccDescr string
	Rules    []Rule
}

func Resolve(ast *syntax.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{ast: ast}
	m := &Model{Notation: ast.Notation}
	for _, meta := range ast.Meta {
		switch meta.Kind {
		case syntax.MetaTitle:
			m.Title = meta.Value
		case syntax.MetaAccTitle:
			m.AccTitle = meta.Value
		case syntax.MetaAccDescr:
			m.AccDescr = meta.Value
		}
	}
	for _, rule := range ast.Rules {
		m.Rules = append(m.Rules, Rule{Name: rule.Name.Text, Index: rule.Index, Definition: r.lowerBody(rule.Body), Span: rule.Span})
	}
	if len(m.Rules) == 0 {
		r.diags = append(r.diags, registryDiagnostic(codeNoRules, "diagram has no railroad rules", ast.Header.Span))
	}
	return m, r.diags
}

type resolver struct {
	ast   *syntax.Start
	diags []diag.Diagnostic
}

func registryDiagnostic(code, message string, span source.Span) diag.Diagnostic {
	d := diag.Diagnostic{Code: code, Message: message, Span: span}
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			d.Help = gen.Diagnostics[i].Help
			d.Severity = diag.SeverityWarning
			if gen.Diagnostics[i].Severity == "info" {
				d.Severity = diag.SeverityInfo
			}
		}
	}
	return d
}

func (r *resolver) repeatNotice(token syntax.Token, max string) {
	r.diags = append(r.diags, registryDiagnostic(codeRepeatMax, "finite repetition maximum "+max+" is not drawn", token.Span))
}

func parseCount(digits string) int64 {
	var n int64
	for i := range len(digits) {
		d := int64(digits[i] - '0')
		if n > (1<<62-d)/10 {
			return 1 << 62
		}
		n = n*10 + d
	}
	return n
}

func trimZeros(digits string) string {
	for len(digits) > 1 && digits[0] == '0' {
		digits = digits[1:]
	}
	if digits == "" {
		return "0"
	}
	return digits
}
