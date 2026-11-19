package layout

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const vennSample = "venn-beta\n" +
	"  title Skills\n" +
	"  set A[\"Alpha\"]:10\n" +
	"    text one\n" +
	"  set B:6\n" +
	"  set C:4\n" +
	"  union A,B[\"Shared\"]:3\n" +
	"    text two\n" +
	"  union B,C:1\n"

func vennInputOf(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, d.Diagnostics)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func TestVennInputEncodesTheModel(t *testing.T) {
	d := ParseDiagram([]byte(vennSample))
	require.Empty(t, d.Diagnostics)
	require.Len(t, d.venn.Subsets, 5)
	require.Equal(t, []string{"B", "C"}, d.venn.Subsets[4].Sets)
	require.Empty(t, d.venn.Subsets[4].Display)
	payload := vennPayload(d.venn).Venn
	require.Len(t, payload.Overlaps, 2)
	require.EqualValues(t, 1000, payload.Overlaps[1].Value)
	require.Len(t, payload.Regions, 1)
	require.Equal(t, "Shared", payload.Regions[0].Label)
	require.Equal(t, []string{"two"}, payload.Regions[0].Texts)
	in := vennInputOf(t, vennSample, scene.ProfileVector)
	require.Equal(t, "venn", in.Kind)
	var boxes, labels []string
	for _, b := range in.Boxes {
		boxes = append(boxes, b.ID+"<"+b.Parent)
	}
	for _, l := range in.Labels {
		labels = append(labels, l.ID+"="+l.Text)
	}
	require.Equal(t, []string{"venn<", "set0<venn", "set1<venn", "set2<venn", "region0<venn"}, boxes)
	require.Equal(t, []string{
		"title=Skills", "set0.label=Alpha", "set0.t0=one", "set1.label=B", "set2.label=C",
		"region0.label=Shared", "region0.t0=two",
	}, labels)
	var sets [][]int
	for _, s := range in.RegionSets {
		sets = append(sets, s.Regions)
	}
	require.Equal(t, [][]int{
		{vennTagSet, 20000}, {vennTagSet, 12000}, {vennTagSet, 8000},
		{vennTagOverlap, 0, 1, 6000}, {vennTagOverlap, 1, 2, 2000},
		{vennTagRegion, 0, 1},
	}, sets)
}

func TestVennInputIsTheSameForBothProfiles(t *testing.T) {
	vector := vennInputOf(t, vennSample, scene.ProfileVector)
	cell := vennInputOf(t, vennSample, scene.ProfileCell)
	require.Equal(t, scene.ProfileVector, cell.Profile)
	require.Equal(t, vector, cell)
}

func TestVennLayoutDecodesWhatTheInputEncodes(t *testing.T) {
	in := vennInputOf(t, vennSample, scene.ProfileVector)
	s, _, err := Layout(in)
	require.NoError(t, err)
	var boxes []string
	for _, b := range s.Boxes {
		boxes = append(boxes, b.ID)
	}
	require.Equal(t, []string{"venn", "set0", "set1", "set2", "region0"}, boxes)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
}

func TestVennZeroSetsLayOutAnEmptyCanvas(t *testing.T) {
	s, _, err := Layout(Input{Kind: "venn", Options: scene.DefaultOptions()})
	require.NoError(t, err)
	require.Equal(t, []string{"venn"}, []string{s.Boxes[0].ID})
	require.Len(t, s.Boxes, 1)
}

func TestVennMoreThanThreeSetsAreRefused(t *testing.T) {
	in := vennInputOf(t, vennSample, scene.ProfileVector)
	in.RegionSets = append(in.RegionSets, in.RegionSets[0])
	_, _, err := Layout(in)
	require.Error(t, err)
}

func TestVennSmallCanvasKeepsMeasuredLabels(t *testing.T) {
	in := vennInputOf(t, "---\nconfig:\n  venn:\n    width: 4\n    height: 4\n---\nvenn-beta\nset A\nset B\nunion A,B[Z]\n", scene.ProfileVector)
	s, _, err := Layout(in)
	require.NoError(t, err)
	require.Len(t, s.Boxes, 4)
	require.Len(t, s.Labels, 3)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
	for i, label := range s.Labels {
		r := label.Rect
		require.GreaterOrEqual(t, r.X, int32(0))
		require.GreaterOrEqual(t, r.Y, int32(0))
		require.LessOrEqual(t, int64(r.X)+int64(r.W), int64(s.Canvas.W))
		require.LessOrEqual(t, int64(r.Y)+int64(r.H), int64(s.Canvas.H))
		for _, earlier := range s.Labels[:i] {
			b := earlier.Rect
			overlap := r.X < b.X+b.W && b.X < r.X+r.W && r.Y < b.Y+b.H && b.Y < r.Y+r.H
			require.False(t, overlap)
		}
	}
}
