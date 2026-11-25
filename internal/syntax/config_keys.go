package syntax

import (
	"cmp"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
)

type configScope struct{ kind, prefix, display string }

func configKeyDiagnostics(mapping ConfigValue, scope configScope) []diag.Diagnostic {
	var diagnostics []diag.Diagnostic
	for _, entry := range mapping.Entries {
		class := configKeyClass(scope.kind, scope.prefix+entry.Key)
		if class == "" || class == "rejected" {
			diagnostics = append(diagnostics, unknownConfigKey(entry, scope.display+entry.Key, class))
			continue
		}
		if child, ok := scope.child(entry); ok {
			diagnostics = append(diagnostics, configKeyDiagnostics(entry.Value, child)...)
		}
	}
	return diagnostics
}

func unknownConfigKey(entry ConfigEntry, path, class string) diag.Diagnostic {
	diagnostic := diag.Diagnostic{
		Code: "config/unknown-key", Severity: diag.SeverityWarning, Span: entry.KeySpan,
		Message: "unknown config key " + path, Help: "Check the spelling of the key, or remove it.",
	}
	if class == "rejected" {
		diagnostic.Code = "config/unsupported-key"
		diagnostic.Message = "config key " + path + " is not supported by this project"
		diagnostic.Help = "Remove the key; this project cannot produce the output it asks for."
	}
	return diagnostic
}

func (scope configScope) child(entry ConfigEntry) (configScope, bool) {
	if entry.Value.Kind != ValueMapping {
		return configScope{}, false
	}
	child := configScope{kind: scope.kind, prefix: scope.prefix + entry.Key + ".", display: scope.display + entry.Key + "."}
	if scope.kind == "" {
		child.kind, child.prefix = configBlockKind(entry.Key), ""
	}
	return child, hasConfigChildren(child.kind, child.prefix)
}

func configBlockKind(key string) string {
	switch key {
	case "quadrantChart":
		return "quadrant"
	case "wardley-beta":
		return "wardley"
	default:
		return strings.ToLower(key)
	}
}

func configSchemaIndex(kind, key string) (int, bool) {
	return slices.BinarySearchFunc(gen.ConfigKeys, gen.ConfigKey{Kind: kind, Key: key}, func(a, b gen.ConfigKey) int {
		return cmp.Or(strings.Compare(a.Kind, b.Kind), strings.Compare(a.Key, b.Key))
	})
}

func configKeyClass(kind, key string) string {
	index, found := configSchemaIndex(kind, key)
	if !found {
		return ""
	}
	return gen.ConfigKeys[index].Class
}

func hasConfigChildren(kind, prefix string) bool {
	index, _ := configSchemaIndex(kind, prefix)
	return index < len(gen.ConfigKeys) && gen.ConfigKeys[index].Kind == kind && strings.HasPrefix(gen.ConfigKeys[index].Key, prefix)
}
