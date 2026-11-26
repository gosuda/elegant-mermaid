package cli

import (
	"strings"
	"testing"
)

func TestRenderEffectiveConfigLimits(t *testing.T) {
	const source = "---\nconfig:\n  maxEdges: 0\n---\nflowchart LR\nA --> B\n"
	raised := writeFixture(t, "raised.yaml", "maxEdges: 1\n")
	for _, format := range []string{"svg", "text"} {
		assertConfigLimitOverride(t, source, format, raised)
	}
}

func assertConfigLimitOverride(t *testing.T, source, format, raised string) {
	t.Helper()
	out, stderr, code := invoke(t, source, "render", "-e", format)
	if code != 1 || out != "" || !strings.Contains(stderr, "error[limit/max-edges]: diagram has 1 edges; the limit is 0") {
		t.Fatalf("%s source cap: %d %q %q", format, code, out, stderr)
	}
	out, stderr, code = invoke(t, source, "render", "-e", format, "-c", raised)
	if code != 0 || out == "" || stderr != "" {
		t.Fatalf("%s raised cap: %d %q %q", format, code, out, stderr)
	}
}

func TestRenderEffectiveConfigCanLowerTextLimit(t *testing.T) {
	lower := writeFixture(t, "lower.yaml", "maxTextSize: 1\n")
	out, stderr, code := invoke(t, "flowchart LR\nA\n", "render", "-e", "svg", "-c", lower)
	if code != 1 || out != "" || !strings.Contains(stderr, "error[limit/max-text-size]") || !strings.Contains(stderr, "the limit is 1 bytes") {
		t.Fatalf("lowered cap: %d %q %q", code, out, stderr)
	}
}

func TestRenderEffectiveFontConfig(t *testing.T) {
	const source = "---\nconfig:\n  fontFamily: Source\n---\nflowchart LR\nA[Alphabet]\n"
	config := writeFixture(t, "font.yaml", "fontFamily: 'Custom & <Font>'\n")
	out, stderr, code := invoke(t, source, "render", "-e", "svg", "-c", config)
	if code != 0 || !strings.Contains(out, "font-family='Custom &amp; &lt;Font&gt;'") {
		t.Fatalf("configured SVG: %d %q %q", code, out, stderr)
	}
	if strings.Count(stderr, "info[config/font-metrics-approximate]") != 1 || !strings.Contains(stderr, "fontFamily is Custom & <Font>") || strings.Contains(stderr, "fontFamily is Source") {
		t.Fatalf("effective font diagnostics: %q", stderr)
	}
}

func TestRenderEffectiveFontConfigCanClearSource(t *testing.T) {
	const source = "---\nconfig:\n  fontFamily: Source\n---\nflowchart LR\nA[Alphabet]\n"
	config := writeFixture(t, "clear.yaml", "fontFamily: ''\n")
	out, stderr, code := invoke(t, source, "render", "-e", "svg", "-c", config)
	plain, _, _ := invoke(t, "flowchart LR\nA[Alphabet]\n", "render", "-e", "svg")
	if code != 0 || stderr != "" || out != plain {
		t.Fatalf("cleared font: %d %q %q", code, out, stderr)
	}
}

func TestRenderEffectiveConfigWarnsForUnknownSiteKey(t *testing.T) {
	config := writeFixture(t, "unknown.yaml", "xyChart:\n  xAxis:\n    typo: true\nthemeVariables: {opaque: value}\n")
	out, stderr, code := invoke(t, "flowchart LR\nA\n", "render", "-e", "svg", "-c", config)
	if code != 0 || out == "" || strings.Count(stderr, "warning[config/unknown-key]") != 1 {
		t.Fatalf("unknown site key: %d %q %q", code, out, stderr)
	}
	if !strings.HasPrefix(stderr, "<stdin>:1:1: warning[config/unknown-key]: unknown config key xyChart.xAxis.typo") {
		t.Fatalf("site key has a Mermaid source span: %q", stderr)
	}
}

func TestLayoutConfigDiagnostics(t *testing.T) {
	const source = "---\nconfig:\n  fontFamily: serif\n  typo: true\n---\nflowchart LR\nA[Alphabet]\n"
	for _, stage := range []string{"model", "layout"} {
		t.Run(stage, func(t *testing.T) {
			out, stderr, code := invoke(t, source, "layout", "--stage", stage)
			if code != 0 || !strings.Contains(out, `"fontFamily":"serif"`) {
				t.Fatalf("configured dump: %d %q %q", code, out, stderr)
			}
			if strings.Count(stderr, "info[config/font-metrics-approximate]") != 1 || strings.Count(stderr, "warning[config/unknown-key]") != 1 {
				t.Fatalf("source diagnostics: %q", stderr)
			}
		})
	}
}
