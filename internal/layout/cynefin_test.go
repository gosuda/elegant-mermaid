package layout

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const cynefinSample = "---\nconfig:\n  cynefin:\n    seed: 3\n    width: 640\n---\ncynefin-beta\n  title Sorting\n  complex\n  \"probe\"\n  \"sense\"\n  clear\n" +
	"  complex --> complicated : \"learned\"\n  clear --> chaotic\n  complex --> complex\n"

func cynefinDiagramInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func TestCynefinInputEncodesTheModel(t *testing.T) {
	in := cynefinDiagramInput(t, cynefinSample, scene.ProfileVector)
	require.Equal(t, "cynefin", in.Kind)
	var boxes []string
	for _, b := range in.Boxes {
		boxes = append(boxes, b.ID+">"+b.Parent)
	}
	require.Equal(t, []string{"frame>", "complex>frame", "clear>frame", "complicated>frame", "chaotic>frame", "confusion>frame"}, boxes)
	var labels []string
	for _, l := range in.Labels {
		labels = append(labels, l.ID+"="+l.Text)
	}
	require.Equal(t, []string{
		"title=Sorting", "complex.label=Complex", "complex.i0=probe", "complex.i1=sense", "clear.label=Clear",
		"complicated.label=Complicated", "chaotic.label=Chaotic", "confusion.label=Confusion", "e0.label=learned",
	}, labels)
	require.Len(t, in.Routes, 2)
	require.Equal(t, Route{ID: "e0", From: "complex", To: "complicated", Orthogonal: true, MarkerStart: "none", MarkerEnd: "point", Line: "normal"}, in.Routes[0])
	require.Equal(t, []scene.Config{{Key: "seed", Value: "3"}, {Key: "width", Value: "640"}}, in.Options.Config)
}

func TestCynefinInputRoundTripsThroughTheFamily(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := cynefinDiagramInput(t, cynefinSample, profile)
		s, _, err := Layout(in)
		require.NoError(t, err)
		require.Len(t, s.Boxes, len(in.Boxes))
		require.Len(t, s.Routes, len(in.Routes))
		require.Len(t, s.Labels, len(in.Labels))
		for i, b := range in.Boxes {
			require.Equal(t, b.ID, s.Boxes[i].ID)
		}
		for i, l := range in.Labels {
			require.Equal(t, l.ID, s.Labels[i].ID)
			require.Equal(t, l.Text, s.Labels[i].Text)
		}
	}
}

func TestInfoInputIsOneBoxAndOneLabel(t *testing.T) {
	in := cynefinDiagramInput(t, "info\nshowInfo\n", scene.ProfileCell)
	require.Equal(t, "info", in.Kind)
	require.Equal(t, []Box{{ID: "info", Role: scene.RoleNode}}, in.Boxes)
	require.Equal(t, []Label{{ID: "version", Owner: "info", Text: "v0.1.0"}}, in.Labels)
	require.Empty(t, in.Routes)
}
