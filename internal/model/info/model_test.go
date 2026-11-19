package info

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/info"
)

func TestResolveCarriesTheLibraryVersion(t *testing.T) {
	src := []byte("info\nshowInfo\n")
	ast, _ := syn.Parse(src, syntax.Preprocess(src).Removed)
	m, ds := Resolve(ast)
	require.Empty(t, ds)
	require.Equal(t, "0.1.0", m.Version)
}
