package diag

import (
	"fmt"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type xorshift32 struct {
	state uint32
}

func (x *xorshift32) next() uint32 {
	x.state ^= x.state << 13
	x.state ^= x.state >> 17
	x.state ^= x.state << 5
	return x.state
}

func (x *xorshift32) draw(limit int) int {
	return int(x.next() % uint32(limit))
}

var sampleCodes = []string{
	"flowchart/arrow-invalid",
	"flowchart/duplicate-ids",
	"common/empty-source",
	"common/no-experimental",
	"meta/unknown-rule",
	"config/malformed",
	"unregistered/code",
}

var sampleSeverities = []Severity{SeverityError, SeverityWarning, SeverityInfo}

func (x *xorshift32) source() []byte {
	out := make([]byte, 0, 64)
	for range 1 + x.draw(20) {
		switch x.draw(4) {
		case 0:
			out = append(out, '\n')
		case 1:
			out = append(out, 'a'+byte(x.draw(6)))
		case 2:
			out = append(out, "é"...)
		default:
			out = append(out, ' ')
		}
	}
	return out
}

func (x *xorshift32) span(size int) source.Span {
	start := x.draw(size + 1)
	return source.Span{Start: start, End: start + x.draw(size-start+1)}
}

func (x *xorshift32) diagnostic(size int) Diagnostic {
	d := Diagnostic{
		Code:     sampleCodes[x.draw(len(sampleCodes))],
		Severity: sampleSeverities[x.draw(len(sampleSeverities))],
		Message:  fmt.Sprintf("case %d message", x.draw(97)),
		Span:     x.span(size),
	}
	if x.draw(2) == 0 {
		d.Help = "fix it"
	}
	for range x.draw(3) {
		d.Related = append(d.Related, Related{Span: x.span(size), Message: "note"})
	}
	if x.draw(2) == 0 {
		d.Fixes = []Fix{{Title: "t", Safety: FixSafe}}
	}
	return d
}

func randomFiles(count int) []FileDiagnostics {
	files := make([]FileDiagnostics, 0, count)
	for i := range count {
		x := &xorshift32{state: uint32(i + 1)}
		src := x.source()
		f := FileDiagnostics{Path: fmt.Sprintf("f%03d.mmd", (i*7919)%count), Source: src}
		if x.draw(2) == 0 {
			f.Kind = "flowchart"
		}
		for range x.draw(4) {
			f.Diagnostics = append(f.Diagnostics, x.diagnostic(len(src)))
		}
		files = append(files, f)
	}
	return files
}

func countDiagnostics(files []FileDiagnostics) int {
	total := 0
	for i := range files {
		total += len(files[i].Diagnostics)
	}
	return total
}

func machineGoldenFiles() []FileDiagnostics {
	return []FileDiagnostics{
		{Path: "z.mmd"},
		{
			Path: "<stdin>", Kind: "flowchart", Source: []byte("a😀b\n"),
			Diagnostics: []Diagnostic{
				{Code: "common/empty-source", Severity: SeverityInfo, Message: "info", Span: source.Span{Start: 5, End: 6}},
				{
					Code: "common/empty-source", Severity: SeverityWarning, Message: "50%,:\r\né😀",
					Span:  source.Span{Start: 1, End: 5},
					Fixes: []Fix{{Title: "Replace", Safety: FixSafe, Edits: []Edit{{Span: source.Span{Start: 1, End: 5}, NewText: "x"}}}},
				},
				{
					Code: "common/empty-source", Severity: SeverityError, Message: "error",
					Span:    source.Span{Start: 0, End: 1},
					Related: []Related{{Span: source.Span{Start: 5, End: 6}, Message: "related"}},
				},
			},
		},
	}
}

const machineGoldenJSON = `{"version":1,"files":[{"path":"<stdin>","kind":"flowchart","diagnostics":[{"code":"common/empty-source","severity":"error","message":"error","span":{"start":0,"end":1},"line":1,"column":1,"end_line":1,"end_column":2,"related":[{"span":{"start":5,"end":6},"line":1,"column":3,"message":"related"}],"help":"","fixes":[]},{"code":"common/empty-source","severity":"warning","message":"50%,:\r\né😀","span":{"start":1,"end":5},"line":1,"column":2,"end_line":1,"end_column":3,"related":[],"help":"","fixes":[{"title":"Replace","safety":"safe","edits":[{"span":{"start":1,"end":5},"new_text":"x"}]}]},{"code":"common/empty-source","severity":"info","message":"info","span":{"start":5,"end":6},"line":1,"column":3,"end_line":1,"end_column":4,"related":[],"help":"","fixes":[]}]},{"path":"z.mmd","kind":null,"diagnostics":[]}],"summary":{"files":2,"errors":1,"warnings":1,"info":1}}` + "\n"

const machineGoldenSARIF = `{"$schema":"https://json.schemastore.org/sarif-2.1.0.json","version":"2.1.0","runs":[{"tool":{"driver":{"name":"emd","version":"0.1.0","rules":[{"id":"common/empty-source","shortDescription":{"text":"source is empty"},"help":{"text":"add a diagram header, for example flowchart"}}]}},"results":[{"ruleId":"common/empty-source","level":"error","message":{"text":"error"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":1,"endLine":1,"endColumn":2}}}],"relatedLocations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":4,"endLine":1,"endColumn":5}},"message":{"text":"related"}}]},{"ruleId":"common/empty-source","level":"warning","message":{"text":"50%,:\r\né😀"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":2,"endLine":1,"endColumn":4}}}]},{"ruleId":"common/empty-source","level":"note","message":{"text":"info"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"<stdin>"},"region":{"startLine":1,"startColumn":4,"endLine":1,"endColumn":5}}}]}]}]}` + "\n"

const machineGoldenGitHub = "::error file=<stdin>,line=1,col=1,endLine=1,endColumn=2,title=common/empty-source::error\n" +
	"::warning file=<stdin>,line=1,col=2,endLine=1,endColumn=3,title=common/empty-source::50%25,:%0D%0Aé😀\n" +
	"::notice file=<stdin>,line=1,col=3,endLine=1,endColumn=4,title=common/empty-source::info\n"

func TestMachineFormatGolden(t *testing.T) {
	files := machineGoldenFiles()
	cases := []struct {
		name string
		got  []byte
		want string
	}{
		{"json", AppendDocument([]byte("prefix"), files), machineGoldenJSON},
		{"sarif", AppendSARIF([]byte("prefix"), "0.1.0", files), machineGoldenSARIF},
		{"github", AppendGitHub([]byte("prefix"), files), machineGoldenGitHub},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if string(tc.got) != "prefix"+tc.want {
				t.Fatalf("got %q\nwant %q", tc.got, "prefix"+tc.want)
			}
		})
	}
}
