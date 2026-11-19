package layout

import (
	"bytes"
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const eventmodelingSample = "eventmodeling\n" +
	"tf 01 ui Cart.Screen\n" +
	"tf 02 cmd AddItem { id: 7 }\n" +
	"tf 03 evt ItemAdded [[ItemData]]\n" +
	"rf 04 evt External.Changed\n" +
	"tf 05 pcr Sync ->> 04\n" +
	"data ItemData {\n  item: 7\n  count: 1\n}\n"

func eventmodelingErrors(ds []diag.Diagnostic) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			out = append(out, d)
		}
	}
	return out
}

func eventmodelingInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	require.Empty(t, eventmodelingErrors(d.Diagnostics))
	require.True(t, d.Supported())
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func TestEventmodelingInputIdentifiesLanesFramesAndRelations(t *testing.T) {
	in := eventmodelingInput(t, eventmodelingSample, scene.ProfileVector)
	require.Equal(t, "eventmodeling", in.Kind)
	require.Equal(t, scene.DirectionLR, in.Direction)
	var ids, parents, shapes []string
	for _, box := range in.Boxes {
		ids = append(ids, box.ID)
		parents = append(parents, box.Parent)
		shapes = append(shapes, box.Shape)
		require.Equal(t, box.Role == scene.RoleNode, box.Exclusive, box.ID)
	}
	require.Equal(t, []string{"lane0", "lane1", "lane100", "lane200", "lane201", "01", "02", "03", "04", "05"}, ids)
	require.Equal(t, []string{"", "", "", "", "", "lane1", "lane100", "lane200", "lane201", "lane0"}, parents)
	require.Equal(t, []string{"lane:0", "lane:1", "lane:100", "lane:200", "lane:201", "ui", "command", "event", "event", "processor"}, shapes)
	var routes []string
	for _, route := range in.Routes {
		routes = append(routes, route.ID+":"+route.From+">"+route.To)
		require.Equal(t, "point", route.MarkerEnd)
		require.False(t, route.Orthogonal)
	}
	require.Equal(t, []string{"e0:01>02", "e1:02>03", "e2:04>05"}, routes)
	var labels []string
	for _, label := range in.Labels {
		labels = append(labels, label.Owner+"="+label.Text)
	}
	require.Equal(t, []string{"lane0=UI/Automation", "lane1=UI/A: Cart", "lane100=Command/Read Model", "lane200=Events", "lane201=Stream: External"}, labels)
}

func TestEventmodelingFrameTextCarriesTheDataBlock(t *testing.T) {
	in := eventmodelingInput(t, eventmodelingSample, scene.ProfileVector)
	texts := map[string]string{}
	for _, box := range in.Boxes {
		texts[box.ID] = box.Text
	}
	require.Equal(t, "Screen", texts["01"])
	require.Equal(t, "AddItem\n\n id: 7", texts["02"])
	require.Equal(t, "ItemAdded\n\n  item: 7\n  count: 1", texts["03"])
}

func TestEventmodelingLayoutMeasuresDataBlocksAndWrapsLongNames(t *testing.T) {
	src := "eventmodeling\ntf 01 cmd " + strings.Repeat("LongName", 12) + " [[D]]\ntf 02 evt Plain\ndata D {\n" + strings.Repeat("  line\n", 8) + "}\n"
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := eventmodelingInput(t, src, profile)
		s, _, err := Layout(in)
		require.NoError(t, err)
		clause, failed, err := s.Validate()
		require.NoError(t, err)
		require.False(t, failed, "%v %v", profile, clause)
		var first, second int32
		for _, box := range s.Boxes {
			switch box.ID {
			case "01":
				first = box.Rect.H
			case "02":
				second = box.Rect.H
			}
		}
		require.Greater(t, first, second)
	}
}

func TestEventmodelingDumpsKeepModelIdentities(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := eventmodelingInput(t, eventmodelingSample, profile)
		var model bytes.Buffer
		require.NoError(t, WriteModelDump(&model, in))
		s, _, err := Layout(in)
		require.NoError(t, err)
		require.Len(t, s.Boxes, len(in.Boxes))
		require.Len(t, s.Routes, len(in.Routes))
		require.Len(t, s.Labels, len(in.Labels))
		for i, box := range in.Boxes {
			require.Equal(t, box.ID, s.Boxes[i].ID)
			require.Contains(t, model.String(), `"id":"`+box.ID+`"`)
		}
		for _, label := range s.Labels {
			require.NotEmpty(t, label.Lines)
		}
	}
}

func TestEventmodelingRejectsRoutesBetweenUnknownFrames(t *testing.T) {
	in := eventmodelingInput(t, eventmodelingSample, scene.ProfileCell)
	in.Routes = append(in.Routes, Route{ID: "bad", From: "01", To: "zz"})
	_, _, err := Layout(in)
	require.ErrorIs(t, err, errEventmodelingInput)
	in = eventmodelingInput(t, eventmodelingSample, scene.ProfileCell)
	in.Labels = append(in.Labels, Label{ID: "bad.label", Owner: "01", Text: "x"})
	_, _, err = Layout(in)
	require.ErrorIs(t, err, errEventmodelingInput)
}

func eventmodelingRandomSource(seed uint32) string {
	state := seed
	draw := func(lo, hi int) int {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		return lo + int(state%uint32(hi-lo+1))
	}
	types := []string{"ui", "cmd", "command", "evt", "event", "pcr", "processor", "rmo", "readmodel"}
	var b strings.Builder
	b.WriteString("eventmodeling\n")
	count := draw(2, 12)
	for i := range count {
		keyword := "tf"
		if draw(0, 3) == 0 {
			keyword = "rf"
		}
		name := fmt.Sprintf("Name%d", i)
		if draw(0, 2) == 0 {
			name = fmt.Sprintf("ns%d.%s", draw(0, 2), name)
		}
		if draw(0, 6) == 0 {
			name = strings.Repeat("W", draw(10, 60))
		}
		fmt.Fprintf(&b, "%s %03d %s %s", keyword, i+1, types[draw(0, len(types)-1)], name)
		if draw(0, 2) == 0 {
			for range draw(1, 2) {
				fmt.Fprintf(&b, " ->> %03d", draw(1, count+1))
			}
		}
		if draw(0, 3) == 0 {
			fmt.Fprintf(&b, " { k: v%d }", i)
		}
		b.WriteString("\n")
	}
	return b.String()
}

func TestEventmodelingRandomLayoutsSatisfyTheHardConstraints(t *testing.T) {
	for seed := uint32(1); seed <= 300; seed++ {
		src := eventmodelingRandomSource(seed)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in := eventmodelingInput(t, src, profile)
			s, _, err := Layout(in)
			require.NoError(t, err, "seed %d", seed)
			clause, failed, err := s.Validate()
			require.NoError(t, err, "seed %d", seed)
			require.False(t, failed, "seed %d %v %v\n%s", seed, profile, clause, src)
		}
	}
}
