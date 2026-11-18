package cynefin

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/cynefin"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	pre := syntax.Preprocess([]byte(src))
	ast, _ := syn.Parse([]byte(src), pre.Removed)
	return Resolve([]byte(src), ast)
}

func names(m *Model) []string {
	out := make([]string, len(m.Domains))
	for i, d := range m.Domains {
		out[i] = d.Name
	}
	return out
}

func TestMissingDomainsFollowDeclaredOnesInCanonicalOrder(t *testing.T) {
	m, ds := resolve("cynefin-beta\nclear\n\"a\"\ncomplex\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"clear", "complex", "complicated", "chaotic", "confusion"}, names(m))
	require.True(t, m.Domains[0].Declared)
	require.False(t, m.Domains[2].Declared)
}

func TestRedeclaredDomainReplacesItsItems(t *testing.T) {
	m, _ := resolve("cynefin-beta\ncomplex\n\"one\"\n\"two\"\nclear\ncomplex\n\"three\"\n")
	require.Equal(t, []string{"complex", "clear", "complicated", "chaotic", "confusion"}, names(m))
	require.Equal(t, []string{"three"}, []string{m.Domains[0].Items[0].Label})
	require.Len(t, m.Domains[0].Items, 1)
}

func TestSelfLoopTransitionIsAWarningAndDropped(t *testing.T) {
	src := "cynefin-beta\ncomplex --> complex : \"x\"\ncomplex --> clear : \"y\"\n"
	m, ds := resolve(src)
	require.Len(t, m.Transitions, 1)
	require.Equal(t, "clear", m.Transitions[0].To)
	require.Len(t, ds, 1)
	require.Equal(t, "cynefin/self-loop-transition", ds[0].Code)
	require.Equal(t, diag.SeverityWarning, ds[0].Severity)
	require.Equal(t, "complex --> complex : \"x\"", src[ds[0].Span.Start:ds[0].Span.End])
}

func TestEntitiesDecodeInLabelsAndTitle(t *testing.T) {
	m, _ := resolve("cynefin-beta\ntitle a #35; b\ncomplex\n\"x #amp; y\"\ncomplex --> clear : \"#65;#bogus;\"\n")
	require.Equal(t, "a # b", m.Title)
	require.Equal(t, "x & y", m.Domains[0].Items[0].Label)
	require.Equal(t, "A#bogus;", m.Transitions[0].Label)
}

func TestConfigKeysAreRangeCheckedAndSorted(t *testing.T) {
	src := "---\nconfig:\n  cynefin:\n    width: 640\n    seed: 0\n    height: 0\n    boundaryAmplitude: 0\n    other: 3\n---\ncynefin-beta\n"
	m, _ := resolve(src)
	require.Equal(t, []ConfigEntry{{"boundaryAmplitude", 0}, {"width", 640}}, m.Config)
}

func TestInitDirectiveOverridesFrontmatterConfig(t *testing.T) {
	src := "---\nconfig:\n  cynefin:\n    seed: 5\n---\n%%{init: {\"cynefin\": {\"seed\": 9}}}%%\ncynefin-beta\n"
	m, _ := resolve(src)
	require.Equal(t, []ConfigEntry{{"seed", 9}}, m.Config)
}

func TestFrontmatterTitleIsTheFallbackTitle(t *testing.T) {
	m, _ := resolve("---\ntitle: From front\n---\ncynefin-beta\n")
	require.Equal(t, "From front", m.Title)
	m, _ = resolve("---\ntitle: From front\n---\ncynefin-beta\ntitle Body wins\n")
	require.Equal(t, "Body wins", m.Title)
}

func TestAccessibilityMetadataIsKept(t *testing.T) {
	m, _ := resolve("cynefin-beta\naccTitle: T\naccDescr: D\n")
	require.Equal(t, "T", m.AccTitle)
	require.Equal(t, "D", m.AccDescr)
}
