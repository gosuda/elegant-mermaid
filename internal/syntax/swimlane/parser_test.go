package swimlane

import (
	"strings"
	"testing"
)

func codes(t *testing.T, src string) []string {
	t.Helper()
	file, diagnostics := Parse([]byte(src), nil)
	if file == nil {
		t.Fatal("nil file")
	}
	out := make([]string, len(diagnostics))
	for i, d := range diagnostics {
		out[i] = d.Code
	}
	return out
}

func TestParseAcceptsSwimlaneHeader(t *testing.T) {
	for _, src := range []string{
		"swimlane-beta\n  A --> B\n",
		"swimlane-beta LR\n  subgraph Customer\n    Browse[Browse] --> Pay\n  end\n",
		"swimlane-beta TB\n  subgraph A\n    subgraph Inner\n      n\n    end\n  end\n",
	} {
		if got := codes(t, src); len(got) != 0 {
			t.Fatalf("%q: %v", src, got)
		}
	}
}

func TestParseRemapsKindDiagnostics(t *testing.T) {
	got := codes(t, "swimlane-beta LR\n  A -> B\n  subgraph L\n    X[a\n")
	want := []string{"swimlane/arrow-invalid", "swimlane/unterminated", "swimlane/unclosed-node-bracket"}
	if strings.Join(got, ",") != strings.Join(want, ",") {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestParseClearsFlowchartHelp(t *testing.T) {
	_, diagnostics := Parse([]byte("swimlane-beta\n  A -> B\n"), nil)
	if len(diagnostics) != 1 || diagnostics[0].Help != "" {
		t.Fatalf("%+v", diagnostics)
	}
	if len(diagnostics[0].Fixes) != 1 {
		t.Fatalf("fix lost: %+v", diagnostics[0])
	}
}

func TestRemapKeepsSharedAndUnknownCodes(t *testing.T) {
	for _, code := range []string{"config/malformed", "flowchart/no-such-code"} {
		d := diagnosticOf(code)
		remap(&d)
		if d.Code != code {
			t.Fatalf("%s became %s", code, d.Code)
		}
	}
}
