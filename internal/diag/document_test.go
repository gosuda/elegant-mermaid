package diag

import (
	"encoding/json"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func documentFiles() []FileDiagnostics {
	return []FileDiagnostics{
		{
			Path:   "b.mmd",
			Kind:   "flowchart",
			Source: []byte("one\ntwo\n"),
			Diagnostics: []Diagnostic{
				{
					Code:     "flowchart/no-self-loop",
					Severity: SeverityWarning,
					Message:  "self",
					Span:     source.Span{Start: 0, End: 1},
				},
				{
					Code:     "flowchart/arrow-invalid",
					Severity: SeverityError,
					Message:  "single arrow",
					Span:     source.Span{Start: 5, End: 6},
				},
			},
		},
		{
			Path:   "a.mmd",
			Source: []byte("x"),
			Diagnostics: []Diagnostic{
				{
					Code:     "common/empty-source",
					Severity: SeverityInfo,
					Message:  "empty",
					Span:     source.Span{Start: 0, End: 1},
				},
			},
		},
	}
}

func TestAppendDocumentOrdersFilesAndCounts(t *testing.T) {
	want := `{"version":1,"files":[` +
		`{"path":"a.mmd","kind":null,"diagnostics":[` +
		`{"code":"common/empty-source","severity":"info","message":"empty","span":{"start":0,"end":1},` +
		`"line":1,"column":1,"end_line":1,"end_column":2,"related":[],"help":"","fixes":[]}]},` +
		`{"path":"b.mmd","kind":"flowchart","diagnostics":[` +
		`{"code":"flowchart/no-self-loop","severity":"warning","message":"self","span":{"start":0,"end":1},` +
		`"line":1,"column":1,"end_line":1,"end_column":2,"related":[],"help":"","fixes":[]},` +
		`{"code":"flowchart/arrow-invalid","severity":"error","message":"single arrow","span":{"start":5,"end":6},` +
		`"line":2,"column":2,"end_line":2,"end_column":3,"related":[],"help":"","fixes":[]}]}],` +
		`"summary":{"files":2,"errors":1,"warnings":1,"info":1}}` + "\n"
	if got := string(AppendDocument(nil, documentFiles())); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestAppendDocumentCountsFilesWithoutDiagnostics(t *testing.T) {
	files := []FileDiagnostics{{Path: "<stdin>", Kind: "flowchart", Source: []byte("flowchart LR\n")}}
	want := `{"version":1,"files":[{"path":"<stdin>","kind":"flowchart","diagnostics":[]}],` +
		`"summary":{"files":1,"errors":0,"warnings":0,"info":0}}` + "\n"
	if got := string(AppendDocument(nil, files)); got != want {
		t.Fatalf("got\n%s\nwant\n%s", got, want)
	}
}

func TestAppendDocumentDoesNotMutateInput(t *testing.T) {
	files := documentFiles()
	AppendDocument(nil, files)
	if files[0].Diagnostics[0].Code != "flowchart/no-self-loop" {
		t.Fatalf("input reordered: %q", files[0].Diagnostics[0].Code)
	}
	if files[0].Path != "b.mmd" {
		t.Fatalf("input reordered: %q", files[0].Path)
	}
}

type decodedDocument struct {
	Version int `json:"version"`
	Files   []struct {
		Path        string            `json:"path"`
		Kind        *string           `json:"kind"`
		Diagnostics []json.RawMessage `json:"diagnostics"`
	} `json:"files"`
	Summary struct {
		Files    int `json:"files"`
		Errors   int `json:"errors"`
		Warnings int `json:"warnings"`
		Info     int `json:"info"`
	} `json:"summary"`
}

func TestAppendDocumentParsesAndKeepsEveryDiagnostic(t *testing.T) {
	files := randomFiles(400)
	out := AppendDocument(nil, files)
	var doc decodedDocument
	if err := json.Unmarshal(out, &doc); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	total := 0
	for i := range doc.Files {
		total += len(doc.Files[i].Diagnostics)
	}
	if total != countDiagnostics(files) {
		t.Fatalf("got %d diagnostics, want %d", total, countDiagnostics(files))
	}
	if doc.Summary.Files != len(files) {
		t.Fatalf("summary.files = %d, want %d", doc.Summary.Files, len(files))
	}
	if doc.Summary.Errors+doc.Summary.Warnings+doc.Summary.Info != total {
		t.Fatalf("summary total = %d, want %d", doc.Summary.Errors+doc.Summary.Warnings+doc.Summary.Info, total)
	}
	for i := 1; i < len(doc.Files); i++ {
		if doc.Files[i-1].Path >= doc.Files[i].Path {
			t.Fatalf("paths out of order: %q then %q", doc.Files[i-1].Path, doc.Files[i].Path)
		}
	}
}
