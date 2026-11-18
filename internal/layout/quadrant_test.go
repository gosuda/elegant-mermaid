package layout

import (
	"bytes"
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func quadrantErrors(d *Diagram) bool {
	return slices.ContainsFunc(d.Diagnostics, func(x diag.Diagnostic) bool { return x.Severity == diag.SeverityError })
}

func assertQuadrantInputCarriesThePayload(t *testing.T, source string) {
	t.Helper()
	d := ParseDiagram([]byte(source))
	if quadrantErrors(d) {
		return
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in, err := d.Input(profile, scene.Options{})
		require.NoError(t, err)
		require.Equal(t, quadrantPayload(d.quadrant), quadrantFromInput(in), source)
	}
}

func TestQuadrantInputCarriesTheWholePayload(t *testing.T) {
	for _, source := range []string{
		"quadrantChart\n",
		"quadrantChart\n  title T\n  x-axis A --> B\n  y-axis C\n  quadrant-1 one\n  quadrant-4 four\n  P: [0.25, 0.75]\n  Q:::hot: [1, 0] radius: 12\n  classDef hot radius: 3\n",
		"%%{init: {\"quadrantChart\": {\"chartWidth\": 800, \"pointRadius\": 9, \"titlePadding\": 0}}}%%\nquadrantChart\n  title #amp; T\n  P: [0.5, 0.5]\n",
	} {
		assertQuadrantInputCarriesThePayload(t, source)
	}
}

func TestQuadrantCorpusInputsCarryTheirPayloads(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "quadrant", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		assertQuadrantInputCarriesThePayload(t, string(data))
	}
}

func TestQuadrantModelDumpListsEveryPoint(t *testing.T) {
	d := ParseDiagram([]byte("quadrantChart\n  A: [0.1, 0.2]\n  B: [0.3, 0.4] radius: 7\n"))
	require.False(t, quadrantErrors(d))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, in))
	require.Contains(t, out.String(), "\"regions\":[[5,100,200,0],\n[6,300,400,8]]")
}
