package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
)

func TestSequenceNoActivateWithoutDeactivate(t *testing.T) {
	row := Row{Code: "sequence/no-activate-without-deactivate", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"sequenceDiagram\nparticipant A\nactivate A\n", 1},
		{"sequenceDiagram\nparticipant A\nactivate A\ndeactivate A\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := sequenceNoActivateWithoutDeactivate(resolved, row)
		if len(got) != tc.want {
			t.Fatalf("%q: got %v, want %d diagnostics", tc.source, got, tc.want)
		}
		for _, d := range got {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(tc.source) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}

func TestSequencePreferExplicitParticipants(t *testing.T) {
	row := Row{Code: "sequence/prefer-explicit-participants", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"sequenceDiagram\nA->>B: hi\n", 2},
		{"sequenceDiagram\nparticipant A\nparticipant B\nA->>B: hi\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := sequencePreferExplicitParticipants(resolved, row)
		if len(got) != tc.want {
			t.Fatalf("%q: got %v, want %d diagnostics", tc.source, got, tc.want)
		}
		for _, d := range got {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(tc.source) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}

func TestSequenceDuplicateParticipant(t *testing.T) {
	row := Row{Code: "sequence/duplicate-participant", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"sequenceDiagram\nparticipant A\nparticipant A\n", 1},
		{"sequenceDiagram\nparticipant A\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := sequenceDuplicateParticipant(resolved, row)
		if len(got) != tc.want {
			t.Fatalf("%q: got %v, want %d diagnostics", tc.source, got, tc.want)
		}
		for _, d := range got {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(tc.source) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}
