package pie

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func TestSliceDiagnosticsAndFixes(t *testing.T) {
	cases := []struct {
		input, code string
		safety      diag.FixSafety
		fixed       string
	}{
		{"Dogs: 10", "pie/label-requires-quotes", diag.FixSafe, "\"Dogs\": 10"},
		{"\"Dogs\" 10", "pie/missing-colon", diag.FixSafe, "\"Dogs\" : 10"},
		{"\"Dogs\":", "pie/missing-number", diag.FixSafe, ""},
		{"\"Dogs : 10", "pie/quote-unclosed", diag.FixUnsafe, "\"Dogs\" : 10"},
		{"\"He said \"Hi\"\": 1", "pie/label-double-in-double", diag.FixSafe, ""},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			assertSliceDiagnostic(t, tc.input, tc.code, tc.fixed, tc.safety)
		})
	}
	for _, input := range []string{"\"Dogs\": 10", "\"He said \\\"Hi\\\"\": 1"} {
		_, clean := Parse([]byte("pie\n"+input+"\n"), nil)
		if len(clean) != 0 {
			t.Fatalf("valid slice %q: %+v", input, clean)
		}
	}
}

func assertSliceDiagnostic(t *testing.T, input, code, want string, safety diag.FixSafety) {
	t.Helper()
	src := []byte("pie\n" + input + "\n")
	_, ds := Parse(src, nil)
	if len(ds) != 1 || ds[0].Code != code {
		t.Fatalf("got %+v", ds)
	}
	d := ds[0]
	if d.Help == "" || d.Severity != diag.SeverityError {
		t.Fatalf("missing metadata: %+v", d)
	}
	if want == "" {
		if len(d.Fixes) != 0 {
			t.Fatal("unexpected fix")
		}
		return
	}
	assertSliceFix(t, src, d, want, safety)
}

func assertSliceFix(t *testing.T, src []byte, d diag.Diagnostic, want string, safety diag.FixSafety) {
	t.Helper()
	if len(d.Fixes) != 1 || d.Fixes[0].Safety != safety {
		t.Fatalf("bad fix: %+v", d.Fixes)
	}
	e := d.Fixes[0].Edits[0]
	fixed := string(src[:e.Span.Start]) + e.NewText + string(src[e.Span.End:])
	if fixed != "pie\n"+want+"\n" {
		t.Fatalf("fixed %q", fixed)
	}
	_, after := Parse([]byte(fixed), nil)
	if len(after) != 0 {
		t.Fatalf("fixed source diagnostics: %+v", after)
	}
}
