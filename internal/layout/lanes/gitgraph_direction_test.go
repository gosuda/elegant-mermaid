package lanes

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestRightToLeftIsNotAGitgraphDirection(t *testing.T) {
	in := GitGraphInput{
		Direction:    scene.DirectionRL,
		ShowBranches: true,
		RotateLabels: true,
		Branches:     []Branch{{ID: "m"}},
		Commits:      []Commit{{ID: "a"}},
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		_, err := GitGraph(in, Params{Profile: profile})
		require.ErrorIs(t, err, geom.ErrDomain, "%v", profile)
	}
}

func TestEverySupportedGitgraphDirectionLaysOut(t *testing.T) {
	for _, direction := range []scene.Direction{scene.DirectionLR, scene.DirectionTB, scene.DirectionBT} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			straight(t, []Branch{{ID: "m"}}, []Commit{{ID: "a"}}, nil, direction, profile)
		}
	}
}
