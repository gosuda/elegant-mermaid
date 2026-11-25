package syntax

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

// EffectiveConfig contains the values read from general Mermaid config.
// Overlay returns a new value so a document can serve concurrent callers.
type EffectiveConfig struct {
	Look                  Look
	MaxTextSize, MaxEdges int32
	FontFamily            string
	FontSpan              source.Span
	SiteDiagnostics       []diag.Diagnostic
}

func ReadEffectiveConfig(mappings ...ConfigValue) (EffectiveConfig, []diag.Diagnostic) {
	return (EffectiveConfig{MaxTextSize: 50000, MaxEdges: 500}).Overlay(mappings...)
}

func (config EffectiveConfig) Overlay(mappings ...ConfigValue) (EffectiveConfig, []diag.Diagnostic) {
	var diagnostics []diag.Diagnostic
	config.Look, diagnostics = config.Look.Overlay(mappings...)
	for _, mapping := range mappings {
		diagnostics = append(diagnostics, configKeyDiagnostics(mapping, configScope{})...)
		for _, entry := range mapping.Entries {
			if !config.apply(entry) {
				diagnostics = append(diagnostics, malformedConfigValue(entry))
			}
		}
	}
	diag.Sort(diagnostics)
	return config, diagnostics
}

func (config *EffectiveConfig) apply(entry ConfigEntry) bool {
	switch entry.Key {
	case "maxTextSize":
		return readConfigLimit(entry.Value, &config.MaxTextSize)
	case "maxEdges":
		return readConfigLimit(entry.Value, &config.MaxEdges)
	case "fontFamily":
		if entry.Value.Kind != ValueString {
			return false
		}
		config.FontFamily, config.FontSpan = entry.Value.Text, entry.KeySpan
	}
	return true
}

func readConfigLimit(value ConfigValue, limit *int32) bool {
	if value.Kind != ValueInteger {
		return false
	}
	number, err := strconv.ParseInt(value.Text, 10, 32)
	if err != nil || number < 0 {
		return false
	}
	*limit = int32(number)
	return true
}
