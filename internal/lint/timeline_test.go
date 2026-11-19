package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/timeline"
)

func TestTimelineNoEntries(t *testing.T) {
	for i, text := range []string{"timeline\n", "timeline\n2020 : event\n"} {
		checkTimelineNoEntriesCase(t, i, text)
	}
}

func TestTimelineEmptySection(t *testing.T) {
	for i, text := range []string{"timeline\nsection A\n", "timeline\nsection A\n2020 : event\n"} {
		checkTimelineEmptySectionCase(t, i, text)
	}
}

func TestTimelineEmptyEvent(t *testing.T) {
	for i, text := range []string{"timeline\n2020 :  \n", "timeline\n2020 : event\n"} {
		checkTimelineEmptyEventCase(t, i, text)
	}
}

func checkTimelineNoEntriesCase(t *testing.T, i int, text string) {
	t.Helper()
	document, _ := parser.Parse([]byte(text), nil)
	m, _ := model.Resolve([]byte(text), document)
	row := Row{Code: "timeline/no-entries", Summary: "expected", Help: "help"}
	ds := timelineNoEntries(m, source.Span{Start: 0, End: 8}, row)
	want := 0
	if i == 0 {
		want = 1
	}
	if len(ds) != want {
		t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
	}
	for _, d := range ds {
		checkTimelineFinding1(t, d, row, text)
	}
}

func checkTimelineEmptySectionCase(t *testing.T, i int, text string) {
	t.Helper()
	document, _ := parser.Parse([]byte(text), nil)
	m, _ := model.Resolve([]byte(text), document)
	row := Row{Code: "timeline/empty-section", Summary: "expected", Help: "help"}
	ds := timelineEmptySection(m, row)
	want := 0
	if i == 0 {
		want = 1
	}
	if len(ds) != want {
		t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
	}
	for _, d := range ds {
		checkTimelineFinding2(t, d, row, text)
	}
}

func checkTimelineEmptyEventCase(t *testing.T, i int, text string) {
	t.Helper()
	document, parsed := parser.Parse([]byte(text), nil)
	if len(parsed) != 0 {
		t.Fatalf("fixture did not parse: %+v", parsed)
	}
	m, _ := model.Resolve([]byte(text), document)
	row := Row{Code: "timeline/empty-event", Summary: "expected", Help: "help"}
	ds := timelineEmptyEvent(m, row)
	want := 0
	if i == 0 {
		want = 1
	}
	if len(ds) != want {
		t.Fatalf("case %d: got %d diagnostics, want %d", i, len(ds), want)
	}
	for _, d := range ds {
		checkTimelineFinding3(t, d, row, text)
	}
}

func checkTimelineFinding1(t *testing.T, d diag.Diagnostic, row Row, text string) {
	t.Helper()
	if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("unexpected diagnostic: %+v", d)
	}
}

func checkTimelineFinding2(t *testing.T, d diag.Diagnostic, row Row, text string) {
	t.Helper()
	if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("unexpected diagnostic: %+v", d)
	}
}

func checkTimelineFinding3(t *testing.T, d diag.Diagnostic, row Row, text string) {
	t.Helper()
	if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("unexpected diagnostic: %+v", d)
	}
}
