package lint

import (
	"maps"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

type ruleFunc func(a *Analysis, row Row) []diag.Diagnostic

var ruleTable = buildRuleTable()

func buildRuleTable() map[string]ruleFunc {
	table := map[string]ruleFunc{}
	maps.Copy(table, commonRules())
	maps.Copy(table, flowchartRules())
	for _, binding := range []struct {
		kind  string
		codes []string
		run   ruleFunc
	}{
		{"class", []string{"duplicate-class", "no-duplicate-methods"}, classRuleDiagnostics},
		{"state", []string{"duplicate-state", "duplicate-transition", "self-transition", "empty-composite"}, stateRuleDiagnostics},
		{"er", []string{"duplicate-attribute", "duplicate-entity", "standalone-entity"}, erRuleDiagnostics},
		{"requirement", []string{"duplicate-name", "duplicate-id", "undefined-reference"}, requirementRuleDiagnostics},
		{"c4", []string{"duplicate-id", "undefined-relationship-endpoint", "undefined-element-style", "undefined-relationship-style-endpoint"}, c4RuleDiagnostics},
		{"xychart", []string{"missing-x-axis", "missing-y-axis", "no-series", "series-length-mismatch"}, xychartRuleDiagnostics},
		{"timeline", []string{"empty-section", "empty-event", "no-entries"}, timelineRuleDiagnostics},
		{"eventmodeling", []string{"undefined-frame", "invalid-flow"}, eventmodelingRuleDiagnostics},
		{"packet", []string{"no-fields", "empty-labels"}, packetRuleDiagnostics},
		{"radar", []string{"no-curves", "curve-length-mismatch", "duplicate-axis"}, radarRuleDiagnostics},
		{"sequence", []string{"duplicate-participant", "prefer-explicit-participants", "no-activate-without-deactivate"}, sequenceRuleDiagnostics},
		{"gitgraph", []string{"duplicate-tag", "no-commits"}, gitgraphRuleDiagnostics},
		{"mindmap", []string{"duplicate-sibling", "no-nodes", "deep-nesting"}, mindmapRuleDiagnostics},
		{"block", []string{"no-blocks"}, blockRuleDiagnostics},
		{"treeview", []string{"no-nodes", "duplicate-sibling"}, treeviewRuleDiagnostics},
		{"ishikawa", []string{"no-causes", "empty-category", "deep-nesting", "duplicate-sibling"}, ishikawaRuleDiagnostics},
		{"kanban", []string{"no-columns", "empty-column", "duplicate-column", "duplicate-task-id"}, kanbanRuleDiagnostics},
		{"architecture", []string{"no-elements", "no-edges", "duplicate-edge"}, architectureRuleDiagnostics},
		{"treemap", []string{"zero-value", "no-leaves", "duplicate-sibling", "branch-with-value"}, treemapRuleDiagnostics},
		{"sankey", []string{"non-positive-value", "duplicate-link", "self-loop"}, sankeyRuleDiagnostics},
		{"gantt", []string{"duplicate-task-id", "undefined-dependency", "empty-section"}, ganttRuleDiagnostics},
		{"quadrant", []string{"duplicate-point", "no-points", "missing-x-axis", "missing-y-axis", "duplicate-quadrant"}, quadrantRuleDiagnostics},
		{"wardley", []string{"undefined-component", "orphan-component", "no-components", "mixed-coordinate-scale", "duplicate-component"}, wardleyRuleDiagnostics},
		{"pie", []string{"duplicate-label", "zero-value", "no-data"}, pieRuleDiagnostics},
		{"venn", []string{"duplicate-set", "non-positive-size", "single-set", "self-union", "duplicate-union"}, vennRuleDiagnostics},
		{"journey", []string{"empty-section", "task-without-actor", "no-tasks"}, journeyRuleDiagnostics},
	} {
		for _, code := range binding.codes {
			kind, run := binding.kind, binding.run
			table[kind+"/"+code] = func(a *Analysis, row Row) []diag.Diagnostic {
				if a.Block.Kind != kind {
					return nil
				}
				return run(a, row)
			}
		}
	}
	return table
}

type Result struct {
	Syntax []diag.Diagnostic
	Lint   []diag.Diagnostic
}

func (r Result) All() []diag.Diagnostic {
	out := make([]diag.Diagnostic, 0, len(r.Syntax)+len(r.Lint))
	out = append(out, r.Syntax...)
	out = append(out, r.Lint...)
	diag.Sort(out)
	return out
}

type FileScope struct {
	Directives []Directive
	Used       []bool
}

func NewFileScope(dirs []Directive) *FileScope {
	return &FileScope{Directives: dirs, Used: make([]bool, len(dirs))}
}

func Run(a *Analysis, cfg Config) Result {
	return RunWith(a, cfg, nil)
}

func RunWith(a *Analysis, cfg Config, file *FileScope) Result {
	rules := cfg.Rules()
	dirs, finds := parseBlockDirectives(a.Source, a.BodyStart)
	s := newSuppressor(dirs, file)
	syntax := s.filter(a.Syntax)
	linted := s.filter(runRules(a, rules))
	metas := newMetaSet(rules)
	linted = append(linted, metas.report(finds)...)
	linted = append(linted, metas.report(unusedFindings(dirs, s.blockUsed))...)
	diag.Sort(syntax)
	diag.Sort(linted)
	return Result{Syntax: syntax, Lint: linted}
}

func runRules(a *Analysis, rules []Rule) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, rule := range rules {
		fn, ok := ruleTable[rule.Row.Code]
		if !ok {
			continue
		}
		for _, d := range fn(a, rule.Row) {
			d.Severity = rule.Severity
			out = append(out, d)
		}
	}
	return out
}

type suppressor struct {
	block     []Directive
	blockUsed []bool
	file      *FileScope
}

func newSuppressor(dirs []Directive, file *FileScope) *suppressor {
	return &suppressor{block: dirs, blockUsed: make([]bool, len(dirs)), file: file}
}

func (s *suppressor) filter(ds []diag.Diagnostic) []diag.Diagnostic {
	kept := make([]diag.Diagnostic, 0, len(ds))
	for _, d := range ds {
		if !s.covers(d) {
			kept = append(kept, d)
		}
	}
	return kept
}

func (s *suppressor) covers(d diag.Diagnostic) bool {
	if !suppressibleCode(d.Code) {
		return false
	}
	code := canonical(d.Code)
	hit := markCovering(s.block, s.blockUsed, code, d.Span.Start)
	if s.file != nil && markCovering(s.file.Directives, s.file.Used, code, d.Span.Start) {
		hit = true
	}
	return hit
}

func markCovering(dirs []Directive, used []bool, code string, at int) bool {
	hit := false
	for i := range dirs {
		if dirs[i].covers(code, at) {
			used[i] = true
			hit = true
		}
	}
	return hit
}

func (d *Directive) covers(code string, at int) bool {
	return slices.ContainsFunc(d.scopes, func(s codeScope) bool {
		return s.code == code && at >= s.start && at < s.end
	})
}

func unusedFindings(dirs []Directive, used []bool) []finding {
	var finds []finding
	for i := range dirs {
		if used[i] || dirs[i].Kind == Enable || len(dirs[i].Names) == 0 {
			continue
		}
		finds = append(finds, finding{code: codeUnused, value: strings.Join(dirs[i].Names, ", "), span: dirs[i].Span})
	}
	return finds
}

type metaSet struct {
	rules map[string]Rule
}

func newMetaSet(rules []Rule) metaSet {
	set := metaSet{rules: map[string]Rule{}}
	for _, rule := range rules {
		if metaRow(rule.Row) {
			set.rules[rule.Row.Code] = rule
		}
	}
	return set
}

func (m metaSet) report(finds []finding) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, f := range finds {
		rule, ok := m.rules[f.code]
		if !ok {
			continue
		}
		d := diagnostic(rule.Row, fill(rule.Row, f.value), f.span)
		d.Severity = rule.Severity
		out = append(out, d)
	}
	return out
}

func classRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return classLint(a.classModel, row)
}

func stateRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return stateLint(a.stateModel, row)
}

func requirementRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return requirementLint(a.requirementModel, row)
}

func c4RuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return c4Lint(a.c4Model, row)
}

func erRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "er/duplicate-attribute":
		return ERDuplicateAttribute(a.erModel, row)
	case "er/duplicate-entity":
		return ERDuplicateEntity(a.erModel, row)
	case "er/standalone-entity":
		return ERStandaloneEntity(a.erModel, row)
	}
	return nil
}

func xychartRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "xychart/missing-x-axis":
		return xychartMissingXAxis(a.xychartModel, row)
	case "xychart/missing-y-axis":
		return xychartMissingYAxis(a.xychartModel, row)
	case "xychart/no-series":
		return xychartNoSeries(a.xychartModel, row)
	case "xychart/series-length-mismatch":
		return xychartSeriesLengthMismatch(a.xychartModel, row)
	}
	return nil
}

func timelineRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "timeline/no-entries":
		return timelineNoEntries(a.timelineModel, a.Block.Header, row)
	case "timeline/empty-section":
		return timelineEmptySection(a.timelineModel, row)
	case "timeline/empty-event":
		return timelineEmptyEvent(a.timelineModel, row)
	}
	return nil
}

func packetRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "packet/no-fields":
		return packetNoFields(a.packetModel, a.Block.Header, row)
	case "packet/empty-labels":
		return packetEmptyLabels(a.packetModel, row)
	}
	return nil
}

func radarRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "radar/no-curves":
		return radarNoCurves(a.radarModel, row)
	case "radar/curve-length-mismatch":
		return radarCurveLengthMismatch(a.radarModel, row)
	case "radar/duplicate-axis":
		return radarDuplicateAxis(a.radarModel, row)
	}
	return nil
}

func eventmodelingRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "eventmodeling/undefined-frame":
		return eventmodelingUndefinedFrame(a.eventModel, row)
	case "eventmodeling/invalid-flow":
		return eventmodelingInvalidFlow(a.eventModel, row)
	}
	return nil
}

func sequenceRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "sequence/duplicate-participant":
		return sequenceDuplicateParticipant(a.sequenceModel, row)
	case "sequence/prefer-explicit-participants":
		return sequencePreferExplicitParticipants(a.sequenceModel, row)
	case "sequence/no-activate-without-deactivate":
		return sequenceNoActivateWithoutDeactivate(a.sequenceModel, row)
	}
	return nil
}

func gitgraphRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "gitgraph/duplicate-tag":
		return gitgraphDuplicateTag(a.gitgraphModel, row)
	case "gitgraph/no-commits":
		return gitgraphNoCommits(a.gitgraphModel, row)
	}
	return nil
}

func mindmapRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "mindmap/duplicate-sibling":
		return mindmapDuplicateSibling(a.mindmapModel, row)
	case "mindmap/no-nodes":
		return mindmapNoNodes(a.mindmapModel, row)
	case "mindmap/deep-nesting":
		return mindmapDeepNesting(a.mindmapModel, row)
	}
	return nil
}

func blockRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return blockNoBlocks(a.blockModel, row)
}

func treeviewRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "treeview/no-nodes":
		return treeviewNoNodes(a.treeviewModel, row)
	case "treeview/duplicate-sibling":
		return treeviewDuplicateSibling(a.treeviewModel, row)
	}
	return nil
}

func ishikawaRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "ishikawa/no-causes":
		return ishikawaNoCauses(a.ishikawaModel, row)
	case "ishikawa/empty-category":
		return ishikawaEmptyCategory(a.ishikawaModel, row)
	case "ishikawa/deep-nesting":
		return ishikawaDeepNesting(a.ishikawaModel, row)
	case "ishikawa/duplicate-sibling":
		return ishikawaDuplicateSibling(a.ishikawaModel, row)
	}
	return nil
}

func kanbanRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "kanban/no-columns":
		return kanbanNoColumns(a.kanbanModel, row)
	case "kanban/empty-column":
		return kanbanEmptyColumn(a.kanbanModel, row)
	case "kanban/duplicate-column":
		return kanbanDuplicateColumn(a.kanbanModel, row)
	case "kanban/duplicate-task-id":
		return kanbanDuplicateTaskID(a.kanbanModel, row)
	}
	return nil
}

func architectureRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	switch row.Code {
	case "architecture/no-elements":
		return architectureNoElements(a.architectureModel, row)
	case "architecture/no-edges":
		return architectureNoEdges(a.architectureModel, row)
	case "architecture/duplicate-edge":
		return architectureDuplicateEdge(a.architectureModel, row)
	}
	return nil
}

func treemapRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return treemapLint(a.treemapModel, row)
}

func sankeyRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return sankeyLint(a.sankeyModel, row)
}

func ganttRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return ganttRule(a.ganttModel, row)
}

func quadrantRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return quadrantRule(a.quadrantModel, row)
}

func wardleyRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return wardleyRule(a.wardleyModel, row)
}

func pieRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return pieRules(a.pieModel, row)
}

func vennRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return vennRules(a.vennModel, row)
}

func journeyRuleDiagnostics(a *Analysis, row Row) []diag.Diagnostic {
	a.parseKind()
	return journeyRules(a.journeyModel, row)
}
