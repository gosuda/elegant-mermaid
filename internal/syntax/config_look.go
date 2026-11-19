package syntax

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
)

const (
	lookKey     = "look"
	lookSeedKey = "handDrawnSeed"
)

type Look struct {
	Value    string
	Seed     uint32
	HasValue bool
	HasSeed  bool
}

func ReadLook(mappings ...ConfigValue) (Look, []diag.Diagnostic) {
	return Look{}.Overlay(mappings...)
}

func (look Look) Overlay(mappings ...ConfigValue) (Look, []diag.Diagnostic) {
	var diags []diag.Diagnostic
	for _, mapping := range mappings {
		if mapping.Kind != ValueMapping {
			continue
		}
		for _, entry := range mapping.Entries {
			diags = look.apply(entry, diags)
		}
	}
	return look, diags
}

func (look *Look) apply(entry ConfigEntry, diags []diag.Diagnostic) []diag.Diagnostic {
	switch entry.Key {
	case lookKey:
		if entry.Value.Kind == ValueString {
			look.Value, look.HasValue = entry.Value.Text, true
		}
	case lookSeedKey:
		seed, ok := readSeed(entry.Value)
		if !ok {
			return append(diags, malformedSeed(entry))
		}
		look.Seed, look.HasSeed = seed, true
	}
	return diags
}

func readSeed(v ConfigValue) (uint32, bool) {
	if v.Kind != ValueInteger {
		return 0, false
	}
	seed, err := strconv.ParseUint(strings.TrimPrefix(v.Text, "+"), 10, 32)
	return uint32(seed), err == nil
}

func malformedSeed(entry ConfigEntry) diag.Diagnostic {
	d := configDiagnostic(codeMalformed, "invalid config value "+shownValue(entry.Value)+" for "+entry.Key, entry.KeySpan)
	for _, row := range gen.Diagnostics {
		if row.Code == codeMalformed {
			d.Help = row.Help
		}
	}
	return d
}

func shownValue(v ConfigValue) string {
	switch v.Kind {
	case ValueNull:
		return "null"
	case ValueBool:
		return strconv.FormatBool(v.Bool)
	case ValueSequence:
		return "[...]"
	case ValueMapping:
		return "{...}"
	}
	return v.Text
}
