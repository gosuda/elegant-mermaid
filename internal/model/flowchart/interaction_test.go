package flowchart

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func resolveSource(t *testing.T, src string) (*Model, []string) {
	t.Helper()
	data := []byte(src)
	ast, parse := syn.Parse(data, nil)
	for _, d := range parse {
		if d.Severity == 0 {
			t.Fatalf("parse error %s: %s", d.Code, d.Message)
		}
	}
	model, diags := Resolve(data, ast)
	var out []string
	for _, d := range diags {
		out = append(out, d.Severity.String()+" "+d.Code+" "+d.Message+" @"+src[d.Span.Start:d.Span.End])
	}
	return model, out
}

func TestClickInteractionDiagnostics(t *testing.T) {
	for _, c := range []struct {
		click string
		want  []string
	}{
		{`click A "https://example.test" "tip"`, nil},
		{`click A href "HTTP://example.test"`, nil},
		{`click A href "mailto:me@example.test" "tip" _blank`, nil},
		{`click A "  https://example.test  "`, nil},
		{`click A "javascript:alert(1)"`, []string{`warning interaction/unsafe-url link URL is not allowed @"javascript:alert(1)"`}},
		{`click A href "#anchor" "tip"`, []string{`warning interaction/unsafe-url link URL is not allowed @"#anchor"`}},
		{`click A "notes://do-your-thing/id"`, []string{`warning interaction/unsafe-url link URL is not allowed @"notes://do-your-thing/id"`}},
		{`click A ""`, []string{`warning interaction/unsafe-url link URL is not allowed @""`}},
		{`click A call fn()`, []string{`info interaction/callback-ignored callback fn is ignored @fn`}},
		{`click A call fn(1, 2) "tip"`, []string{`info interaction/callback-ignored callback fn is ignored @fn`}},
		{`click A plain`, []string{`info interaction/callback-ignored callback plain is ignored @plain`}},
		{`click A plain "tip"`, []string{`info interaction/callback-ignored callback plain is ignored @plain`}},
	} {
		_, got := resolveSource(t, "flowchart LR\n  A --> B\n  "+c.click+"\n")
		if len(got) != len(c.want) || (len(got) == 1 && got[0] != c.want[0]) {
			t.Errorf("%s: got %q, want %q", c.click, got, c.want)
		}
	}
}

func TestClickModelFields(t *testing.T) {
	model, _ := resolveSource(t, "flowchart LR\n  A --> B\n  click A href \"https://example.test\" \"tip\"\n  click B call fn(1, 2)\n  click B plain \"note\"\n")
	want := []Click{
		{Target: "A", Kind: ClickLink, URL: "https://example.test", Tip: "tip", Href: true},
		{Target: "B", Kind: ClickCallback, Callback: "fn", Args: "1, 2"},
		{Target: "B", Kind: ClickCallback, Callback: "plain", Tip: "note"},
	}
	if len(model.Clicks) != len(want) {
		t.Fatalf("%d clicks", len(model.Clicks))
	}
	for i, w := range want {
		got := model.Clicks[i]
		got.Span, got.ActionSpan = source.Span{}, source.Span{}
		if got != w {
			t.Errorf("click %d: got %+v, want %+v", i, got, w)
		}
	}
}
