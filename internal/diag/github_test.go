package diag

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func TestAppendGitHubEscapesMessageAndProperties(t *testing.T) {
	files := []FileDiagnostics{{
		Path:   "dir:name,x.mmd",
		Source: []byte("50% done\r\nnext\n"),
		Diagnostics: []Diagnostic{{
			Code:     "flowchart/a:b,c",
			Severity: SeverityWarning,
			Message:  "50% done\r\nnext",
			Span:     source.Span{Start: 10, End: 13},
		}},
	}}
	want := "::warning file=dir%3Aname%2Cx.mmd,line=2,col=1,endLine=2,endColumn=4," +
		"title=flowchart/a%3Ab%2Cc::50%25 done%0D%0Anext\n"
	if got := string(AppendGitHub(nil, files)); got != want {
		t.Fatalf("got\n%q\nwant\n%q", got, want)
	}
}

func TestAppendGitHubLevelsForAllSeverities(t *testing.T) {
	commands := map[Severity]string{
		SeverityError:   "::error",
		SeverityWarning: "::warning",
		SeverityInfo:    "::notice",
	}
	for severity, command := range commands {
		files := []FileDiagnostics{{
			Path:   "<stdin>",
			Source: []byte("abc"),
			Diagnostics: []Diagnostic{{
				Code:     "c/x",
				Severity: severity,
				Message:  "m",
				Span:     source.Span{Start: 0, End: 1},
			}},
		}}
		got := string(AppendGitHub(nil, files))
		want := command + " file=<stdin>,line=1,col=1,endLine=1,endColumn=2,title=c/x::m\n"
		if got != want {
			t.Fatalf("got\n%q\nwant\n%q", got, want)
		}
	}
}

func TestAppendGitHubOneLinePerDiagnostic(t *testing.T) {
	files := randomFiles(2000)
	lines := strings.Split(strings.TrimSuffix(string(AppendGitHub(nil, files)), "\n"), "\n")
	want := countDiagnostics(files)
	if want == 0 || len(lines) != want {
		t.Fatalf("lines = %d, want %d", len(lines), want)
	}
	for i := range lines {
		if !isCommandLine(lines[i]) {
			t.Fatalf("line %d = %q", i, lines[i])
		}
	}
}

func isCommandLine(line string) bool {
	for _, prefix := range []string{"::error ", "::warning ", "::notice "} {
		if strings.HasPrefix(line, prefix) {
			return strings.Count(line, "::") == 2
		}
	}
	return false
}

func TestAppendGitHubKeepsPropertySeparatorsOutOfValues(t *testing.T) {
	files := []FileDiagnostics{{
		Path:   "a,b.mmd",
		Source: []byte("x"),
		Diagnostics: []Diagnostic{{
			Code:     "c/x",
			Severity: SeverityInfo,
			Message:  "plain",
			Span:     source.Span{Start: 0, End: 1},
		}},
	}}
	got := string(AppendGitHub(nil, files))
	properties := got[:strings.Index(got, "::plain")]
	if strings.Count(properties, ",") != 5 {
		t.Fatalf("property separators = %d: %q", strings.Count(properties, ","), properties)
	}
	if !strings.Contains(properties, "file=a%2Cb.mmd") {
		t.Fatalf("path not escaped: %q", properties)
	}
}
