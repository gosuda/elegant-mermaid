package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func adaptState(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, "error", diagnostic.Severity.String(), "%s: %s", diagnostic.Code, diagnostic.Message)
	}
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func TestStateFixedSymbolsUseExactSizes(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := adaptState(t, "stateDiagram-v2\n[*] --> A\nA --> [*]\nstate forked <<fork>>\nstate decision <<choice>>\n", profile)
		for i, box := range in.Boxes {
			if box.Shape != "roundedRect" {
				require.True(t, in.Exact[i], "symbol %s must bypass measured sizing", box.ID)
			}
		}
	}
}

func TestStateFinalNoteAndDuplicateTransitionsSurvive(t *testing.T) {
	in := adaptState(t, "stateDiagram-v2\nA --> B: first\nA --> B: second\nnote left of A: old\nnote right of A: final\n", scene.ProfileCell)
	require.Len(t, in.Attachments, 1)
	require.Equal(t, "final", in.Boxes[in.Attachments[0].Note].Text)
	require.Len(t, in.Routes, 2)
	require.NotEqual(t, in.Routes[0].ID, in.Routes[1].ID)
}

func TestStateEmptyConcurrentRegionsKeepDeclarationOrder(t *testing.T) {
	in := adaptState(t, "stateDiagram-v2\nstate C {\n--\nA\n--\n}\n", scene.ProfileCell)
	require.Len(t, in.RegionSets, 1)
	require.Len(t, in.RegionSets[0].Regions, 3)
	for _, region := range in.RegionSets[0].Regions {
		parent := ""
		for _, box := range in.Boxes {
			if box.ID == in.Groups[region].ID {
				parent = box.Parent
			}
		}
		require.Equal(t, "C", parent)
	}
}
