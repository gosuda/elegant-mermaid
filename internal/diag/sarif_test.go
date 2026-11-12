package diag

import (
	"encoding/json"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func TestAppendSARIFUTF16ColumnsAndRelated(t *testing.T) {
	files := []FileDiagnostics{{
		Path:   "a.mmd",
		Kind:   "flowchart",
		Source: []byte("ab\U0001F600\ncd\n"),
		Diagnostics: []Diagnostic{{
			Code:     "common/empty-source",
			Severity: SeverityError,
			Message:  "source is empty",
			Span:     source.Span{Start: 2, End: 6},
			Related:  []Related{{Span: source.Span{Start: 7, End: 9}, Message: "first declared here"}},
			Help:     "add a diagram header, for example flowchart",
			Fixes:    []Fix{{Title: "drop", Safety: FixSafe}},
		}},
	}}
	want := `{"$schema":"https://json.schemastore.org/sarif-2.1.0.json","version":"2.1.0","runs":[{"tool":{"driver":{"name":"emd","version":"0.1.0","rules":[` +
		`{"id":"common/empty-source","shortDescription":{"text":"source is empty"},"help":{"text":"add a diagram header, for example flowchart"}}` +
		`]}},"results":[` +
		`{"ruleId":"common/empty-source","level":"error","message":{"text":"source is empty"},` +
		`"locations":[{"physicalLocation":{"artifactLocation":{"uri":"a.mmd"},` +
		`"region":{"startLine":1,"startColumn":3,"endLine":1,"endColumn":5}}}],` +
		`"relatedLocations":[{"physicalLocation":{"artifactLocation":{"uri":"a.mmd"},` +
		`"region":{"startLine":2,"startColumn":1,"endLine":2,"endColumn":3}},"message":{"text":"first declared here"}}]}` +
		`]}]}` + "\n"
	if got := string(AppendSARIF(nil, "0.1.0", files)); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestAppendSARIFLevelsAndRuleOrder(t *testing.T) {
	files := []FileDiagnostics{{
		Path:   "<stdin>",
		Source: []byte("abc"),
		Diagnostics: []Diagnostic{
			{Code: "flowchart/duplicate-ids", Severity: SeverityError, Message: "e", Span: source.Span{Start: 0, End: 1}},
			{Code: "meta/unknown-rule", Severity: SeverityWarning, Message: "w", Span: source.Span{Start: 1, End: 2}},
			{Code: "custom/own-code", Severity: SeverityInfo, Message: "i", Span: source.Span{Start: 2, End: 3}},
			{Code: "common/empty-source", Severity: SeverityInfo, Message: "i", Span: source.Span{Start: 2, End: 3}},
		},
	}}
	out := AppendSARIF(nil, "0.1.0", files)
	var log decodedSARIF
	if err := json.Unmarshal(out, &log); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	if log.Runs[0].Tool.Driver.Name != "emd" || log.Runs[0].Tool.Driver.Version != "0.1.0" {
		t.Fatalf("driver = %+v", log.Runs[0].Tool.Driver)
	}
	levels := map[string]string{}
	for i := range log.Runs[0].Results {
		levels[log.Runs[0].Results[i].RuleID] = log.Runs[0].Results[i].Level
	}
	want := map[string]string{
		"flowchart/duplicate-ids": "error",
		"meta/unknown-rule":       "warning",
		"custom/own-code":         "note",
		"common/empty-source":     "note",
	}
	for code, level := range want {
		if levels[code] != level {
			t.Fatalf("%s level = %q, want %q", code, levels[code], level)
		}
	}
	checkSARIFRules(t, log)
}

func checkSARIFRules(t *testing.T, log decodedSARIF) {
	t.Helper()
	rules := make([]string, len(log.Runs[0].Tool.Driver.Rules))
	for i := range log.Runs[0].Tool.Driver.Rules {
		rules[i] = log.Runs[0].Tool.Driver.Rules[i].ID
	}
	wantRules := []string{"meta/unknown-rule", "flowchart/duplicate-ids", "common/empty-source", "custom/own-code"}
	if len(rules) != len(wantRules) {
		t.Fatalf("rules = %v, want %v", rules, wantRules)
	}
	for i := range wantRules {
		if rules[i] != wantRules[i] {
			t.Fatalf("rules = %v, want %v", rules, wantRules)
		}
	}
	checkSARIFRuleMetadata(t, log)
}

func checkSARIFRuleMetadata(t *testing.T, log decodedSARIF) {
	t.Helper()
	for i := range log.Runs[0].Tool.Driver.Rules {
		r := log.Runs[0].Tool.Driver.Rules[i]
		if r.ID == "custom/own-code" && (r.ShortDescription.Text != "" || r.Help.Text != "") {
			t.Fatalf("unknown code carries text: %+v", r)
		}
		if r.ID == "meta/unknown-rule" && r.ShortDescription.Text != "unknown rule CODE" {
			t.Fatalf("rule summary = %q", r.ShortDescription.Text)
		}
	}
}

type decodedSARIF struct {
	Runs []struct {
		Tool struct {
			Driver struct {
				Name    string `json:"name"`
				Version string `json:"version"`
				Rules   []struct {
					ID               string `json:"id"`
					ShortDescription struct {
						Text string `json:"text"`
					} `json:"shortDescription"`
					Help struct {
						Text string `json:"text"`
					} `json:"help"`
				} `json:"rules"`
			} `json:"driver"`
		} `json:"tool"`
		Results []struct {
			RuleID  string `json:"ruleId"`
			Level   string `json:"level"`
			Message struct {
				Text string `json:"text"`
			} `json:"message"`
			Locations []struct {
				PhysicalLocation struct {
					ArtifactLocation struct {
						URI string `json:"uri"`
					} `json:"artifactLocation"`
					Region struct {
						StartLine   int `json:"startLine"`
						StartColumn int `json:"startColumn"`
						EndLine     int `json:"endLine"`
						EndColumn   int `json:"endColumn"`
					} `json:"region"`
				} `json:"physicalLocation"`
			} `json:"locations"`
		} `json:"results"`
	} `json:"runs"`
}

func TestAppendSARIFHoldsOneResultPerDiagnostic(t *testing.T) {
	files := randomFiles(400)
	out := AppendSARIF(nil, "9.9.9", files)
	var log decodedSARIF
	if err := json.Unmarshal(out, &log); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	if len(log.Runs) != 1 {
		t.Fatalf("runs = %d, want 1", len(log.Runs))
	}
	want := countDiagnostics(files)
	if len(log.Runs[0].Results) != want {
		t.Fatalf("results = %d, want %d", len(log.Runs[0].Results), want)
	}
	checkSARIFLocations(t, log)
}

func checkSARIFLocations(t *testing.T, log decodedSARIF) {
	t.Helper()
	seen := map[string]bool{}
	for i := range log.Runs[0].Results {
		r := &log.Runs[0].Results[i]
		if len(r.Locations) != 1 {
			t.Fatalf("result %d has %d locations", i, len(r.Locations))
		}
		region := r.Locations[0].PhysicalLocation.Region
		if region.StartLine < 1 || region.StartColumn < 1 || region.EndLine < region.StartLine {
			t.Fatalf("result %d region = %+v", i, region)
		}
		seen[r.RuleID] = true
	}
	for i := range log.Runs[0].Tool.Driver.Rules {
		if !seen[log.Runs[0].Tool.Driver.Rules[i].ID] {
			t.Fatalf("rule %q has no result", log.Runs[0].Tool.Driver.Rules[i].ID)
		}
	}
	if len(log.Runs[0].Tool.Driver.Rules) != len(seen) {
		t.Fatalf("rules = %d, distinct codes = %d", len(log.Runs[0].Tool.Driver.Rules), len(seen))
	}
}
