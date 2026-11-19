package syntax_test

import (
	"encoding/json"
	"os"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func TestDetectKeywords(t *testing.T) {
	data, err := os.ReadFile("../../spec/data/kinds.json")
	if err != nil {
		t.Fatal(err)
	}
	var kinds []struct {
		ID       string `json:"id"`
		Keywords []struct {
			Text string `json:"text"`
			Case string `json:"case"`
		} `json:"keywords"`
	}
	if err := json.Unmarshal(data, &kinds); err != nil {
		t.Fatal(err)
	}
	count := 0
	for _, kind := range kinds {
		for _, keyword := range kind.Keywords {
			count++
			t.Run(keyword.Text, func(t *testing.T) {
				checkDetectedKeyword(t, keyword.Text, keyword.Case, kind.ID)
			})
		}
	}
	if count != 52 {
		t.Fatalf("keyword count = %d", count)
	}
}

func checkDetectedKeyword(t *testing.T, text, caseRule, kind string) {
	t.Helper()
	got := syntax.Detect([]byte(text+"\n"), nil)
	if !got.Found || got.Kind != kind || got.Header != (source.Span{End: len(text)}) || len(got.Diagnostics) != 0 {
		t.Fatalf("detection = %+v", got)
	}
	changed := strings.ToUpper(text)
	if changed == text {
		changed = strings.ToLower(text)
	}
	folded := syntax.Detect([]byte(changed), nil)
	want := caseRule == "insensitive"
	if folded.Found != want || want && folded.Kind != kind {
		t.Fatalf("case detection = %+v, want found %v", folded, want)
	}
}

func TestDetectPreprocessedHeader(t *testing.T) {
	prefixes := []string{"", " \t\n", "---\nconfig: {}\n---\n", "%%{init: {}}%%\n", "%% comment\n", "---\r\nconfig: {}\r\n---\r\n%%{init: {}}%%\r\n%% comment\r\n", "---\rconfig: {}\r---\r%%{init: {}}%%\r%% comment\r"}
	for _, prefix := range prefixes {
		src := []byte(prefix + " \tflowchart LR\nA --> B")
		p := syntax.Preprocess(src)
		got := syntax.Detect(src, p.Removed)
		start := len(prefix) + 2
		if !got.Found || got.Kind != "flowchart" || got.Header != (source.Span{Start: start, End: start + 9}) {
			t.Fatalf("prefix %q: %+v", prefix, got)
		}
	}
}

func TestDetectUnknown(t *testing.T) {
	for _, token := range []string{"blockchain", "graphs", "pie2", "flowchart_extra", "flowchart-x", "error"} {
		got := syntax.Detect([]byte(" \t"+token+"\n"), nil)
		if got.Found || len(got.Diagnostics) != 1 {
			t.Fatalf("%q: %+v", token, got)
		}
		d := got.Diagnostics[0]
		if d.Code != "common/unknown-diagram-kind" || d.Severity != diag.SeverityError || d.Span != got.Header {
			t.Fatalf("%q: %+v", token, d)
		}
		if d.Message != "unknown diagram kind "+token || d.Span.End != 2+len(token) {
			t.Fatalf("%q: %+v", token, d)
		}
		if d.Help != "Start the source with a supported diagram header, for example flowchart." {
			t.Fatalf("help = %q", d.Help)
		}
	}
}

func TestDetectASCIICaseOnly(t *testing.T) {
	if syntax.Detect([]byte("İSHIKAWA"), nil).Found {
		t.Fatal("non-ASCII case folding matched a keyword")
	}
}

func TestDetectEmpty(t *testing.T) {
	for _, text := range []string{"", " \t\r\n", "%% comment", "%% one\r%% two\r", "---\nconfig: {}\n---\n", "%%{init: {}}%%", "%%{unknown: x}%%\r%% comment"} {
		src := []byte(text)
		got := syntax.Detect(src, syntax.Preprocess(src).Removed)
		if got.Found || len(got.Diagnostics) != 1 {
			t.Fatalf("%q: %+v", text, got)
		}
		d := got.Diagnostics[0]
		if d.Code != "common/empty-source" || d.Severity != diag.SeverityError || d.Span != (source.Span{}) || d.Message != "source is empty" || d.Help != "add a diagram header, for example flowchart" {
			t.Fatalf("%q: %+v", text, d)
		}
	}
}
