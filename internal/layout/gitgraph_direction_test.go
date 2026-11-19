package layout

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestGitgraphDirectionNamesAreExact(t *testing.T) {
	require.Equal(t, scene.DirectionLR, gitgraphDirection("LR"))
	require.Equal(t, scene.DirectionTB, gitgraphDirection("TB"))
	require.Equal(t, scene.DirectionBT, gitgraphDirection("BT"))
	require.Equal(t, scene.DirectionRL, gitgraphDirection("RL"))
	require.Equal(t, scene.DirectionRL, gitgraphDirection("sideways"))
}

func TestGitgraphRightToLeftModelIsRejected(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := gitgraphInput(t, gitgraphSample, profile)
		in.Direction = scene.DirectionRL
		_, _, err := layoutGitgraph(in)
		require.ErrorIs(t, err, geom.ErrDomain, "%v", profile)
	}
}

func TestGitgraphHeaderRightToLeftIsASyntaxError(t *testing.T) {
	d := ParseDiagram([]byte("gitGraph RL:\ncommit\n"))
	require.NotEmpty(t, errorsOf(d.Diagnostics))
}
