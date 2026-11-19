package lint

type Described struct {
	Code      string
	Severity  string
	Summary   string
	Help      string
	Rationale string
	FixSafety string
}

func Describe(code string) (Described, bool) {
	e, ok := lookup(code)
	if !ok {
		return Described{}, false
	}
	if r := e.lint; r != nil {
		return Described{Code: r.Code, Severity: r.Severity, Summary: r.Summary, Help: r.Help, Rationale: r.Rationale, FixSafety: r.FixSafety}, true
	}
	d := e.syntax
	return Described{Code: d.Code, Severity: d.Severity, Summary: d.Summary, Help: d.Help, Rationale: d.Rationale, FixSafety: d.FixSafety}, true
}
