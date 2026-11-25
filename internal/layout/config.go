package layout

import (
	"fmt"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func (d *Diagram) EffectiveConfig(site syntax.ConfigValue) (syntax.EffectiveConfig, error) {
	config, diagnostics := d.config.Overlay(site)
	for _, diagnostic := range diagnostics {
		if diagnostic.Severity == diag.SeverityError {
			return syntax.EffectiveConfig{}, fmt.Errorf("%w: %s", ErrSiteConfig, diagnostic.Message)
		}
		diagnostic.Span = source.Span{}
		config.SiteDiagnostics = append(config.SiteDiagnostics, diagnostic)
	}
	for _, entry := range site.Entries {
		if entry.Key == "fontFamily" {
			config.FontSpan = source.Span{}
		}
	}
	return config, nil
}

func (d *Diagram) HasSourceErrors() bool {
	for _, diagnostic := range d.baseDiagnostics {
		if diagnostic.Severity == diag.SeverityError {
			return true
		}
	}
	return false
}

// DiagnosticsFor recomputes only admission and font diagnostics. Parser and
// resolver diagnostics stay independent of a caller's render configuration.
func (d *Diagram) DiagnosticsFor(config syntax.EffectiveConfig) []diag.Diagnostic {
	diagnostics := slices.Clone(d.baseDiagnostics)
	diagnostics = append(diagnostics, config.SiteDiagnostics...)
	if len(d.Source) > int(config.MaxTextSize) {
		diagnostics = append(diagnostics, diag.Diagnostic{
			Code: "limit/max-text-size", Severity: diag.SeverityError,
			Message: fmt.Sprintf("source has %d bytes; the limit is %d bytes", len(d.Source), config.MaxTextSize),
			Span:    source.Span{Start: int(config.MaxTextSize), End: len(d.Source)},
			Help:    "Shorten the source, or raise maxTextSize.",
		})
	}
	if len(d.edgeSpans) > int(config.MaxEdges) {
		diagnostics = append(diagnostics, diag.Diagnostic{
			Code: "limit/max-edges", Severity: diag.SeverityError,
			Message: fmt.Sprintf("diagram has %d edges; the limit is %d", len(d.edgeSpans), config.MaxEdges),
			Span:    d.edgeSpans[config.MaxEdges], Help: "Reduce the number of edges, or raise maxEdges.",
		})
	}
	if config.FontFamily != "" {
		diagnostics = append(diagnostics, diag.Diagnostic{
			Code: "config/font-metrics-approximate", Severity: diag.SeverityInfo,
			Message: "text width is measured with Inter; fontFamily is " + config.FontFamily,
			Span:    config.FontSpan, Help: "Text widths may differ from the font named in fontFamily.",
		})
	}
	diag.Sort(diagnostics)
	return diagnostics
}

func withFontFamily(options scene.Options, family string) scene.Options {
	options.FontFamily = family
	options.Config = slices.DeleteFunc(slices.Clone(options.Config), func(entry scene.Config) bool {
		return entry.Key == "fontFamily"
	})
	return options
}
