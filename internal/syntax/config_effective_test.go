package syntax

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func TestEffectiveConfigLimitsAndOverlay(t *testing.T) {
	base, diagnostics := ReadEffectiveConfig(configMapping(t, "maxEdges: 0\nmaxTextSize: 2147483647\nfontFamily: serif\n"))
	if len(diagnostics) != 0 {
		t.Fatalf("base: %+v, %+v", base, diagnostics)
	}
	assertEffectiveConfigValues(t, base, 0, 2147483647, "serif")
	config, diagnostics := base.Overlay(configMapping(t, "maxEdges: +5\nmaxTextSize: -0\nfontFamily: ''\n"))
	if len(diagnostics) != 0 {
		t.Fatalf("overlay: %+v, %+v", config, diagnostics)
	}
	assertEffectiveConfigValues(t, config, 5, 0, "")
	assertEffectiveConfigValues(t, base, 0, 2147483647, "serif")
}

func assertEffectiveConfigValues(t *testing.T, config EffectiveConfig, maxEdges, maxTextSize int32, family string) {
	t.Helper()
	if config.MaxEdges != maxEdges || config.MaxTextSize != maxTextSize || config.FontFamily != family {
		t.Fatalf("config = %+v, want maxEdges %d, maxTextSize %d, fontFamily %q", config, maxEdges, maxTextSize, family)
	}
}

func TestEffectiveConfigRejectsInvalidValues(t *testing.T) {
	for _, key := range []string{"maxEdges", "maxTextSize"} {
		for _, value := range []string{"-1", "2147483648", "99999999999999999999", "1.0", "1e2", "'2'", "true", "null", "[]", "{}"} {
			requireInvalidConfigValue(t, key, value)
		}
	}
	for _, value := range []string{"3", "false", "null", "[]", "{}"} {
		requireInvalidConfigValue(t, "fontFamily", value)
	}
}

func requireInvalidConfigValue(t *testing.T, key, value string) {
	t.Helper()
	text := key + ": " + value + "\n"
	_, diagnostics := ReadEffectiveConfig(configMapping(t, text))
	if len(diagnostics) != 1 {
		t.Fatalf("%q: expected one error, got %+v", text, diagnostics)
	}
	diagnostic := diagnostics[0]
	if diagnostic.Code != "config/malformed" || diagnostic.Severity != diag.SeverityError || !strings.HasSuffix(diagnostic.Message, " for "+key) || text[diagnostic.Span.Start:diagnostic.Span.End] != key {
		t.Fatalf("%q: invalid diagnostic: %+v", text, diagnostic)
	}
}

func TestEffectiveConfigUnknownKeyPaths(t *testing.T) {
	text := "typo: {nested: true}\nxyChart:\n  xAxis:\n    typo: true\n  yAxis:\n    showLabel: true\nthemeVariables: {arbitrary: value}\n"
	_, diagnostics := ReadEffectiveConfig(configMapping(t, text))
	want := []string{"unknown config key typo", "unknown config key xyChart.xAxis.typo"}
	if len(diagnostics) != len(want) {
		t.Fatalf("unknown diagnostics: %+v", diagnostics)
	}
	for i, diagnostic := range diagnostics {
		if diagnostic.Code != "config/unknown-key" || diagnostic.Severity != diag.SeverityWarning || diagnostic.Message != want[i] || text[diagnostic.Span.Start:diagnostic.Span.End] != "typo" {
			t.Fatalf("unknown diagnostic %d: %+v", i, diagnostic)
		}
	}
}

func configMapping(t *testing.T, text string) ConfigValue {
	t.Helper()
	value, diagnostics := ParseConfigYAML([]byte(text), 0, len(text))
	if len(diagnostics) != 0 {
		t.Fatalf("config fixture: %+v", diagnostics)
	}
	return value
}
