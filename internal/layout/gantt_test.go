package layout

import (
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const ganttSample = "gantt\ntitle Plan\ndateFormat YYYY-MM-DD\nexcludes weekends\nsection Build\nCompile :crit, c1, 2014-01-03, 3d\nShip :milestone, m1, 2014-01-10, 0d\nclick c1 href \"https://example.com/c1\"\nclick m1 href \"javascript:void(0)\"\n"

func TestGanttLinksOwnTaskBoxes(t *testing.T) {
	d := ParseDiagram([]byte(ganttSample))
	links := d.Links()
	require.Len(t, links, 1)
	require.Equal(t, "t0", links[0].Owner)
	require.Equal(t, scene.GroupRoleNode, links[0].Role)
	require.Equal(t, "https://example.com/c1", links[0].URL)
}

func TestGanttModelDumpCarriesTaskRegionsAndEffectiveOptions(t *testing.T) {
	d := ParseDiagram([]byte(ganttSample))
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, in))
	dump := out.String()
	require.Contains(t, dump, `"axisFormat":"%Y-%m-%d","excludes":"weekends","weekday":"sunday","weekend":"saturday"`)
	require.Contains(t, dump, "[0,4,1,2777414400,2778278400,2778278400]")
	require.Contains(t, dump, "[1,1,1,2778624000,2778624000,2778624000]")
	require.Contains(t, dump, `{"id":"s0","role":"node","parent":"plot","exclusive":false}`)
	require.Contains(t, dump, `{"id":"t1.label","owner":"t1","text":"Ship","lines":[]}`)
}

func TestGanttLayoutDecodesWhatTheModelStageEncodes(t *testing.T) {
	d := ParseDiagram([]byte(ganttSample))
	in, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	chart := ganttFromInput(in)
	require.Equal(t, "Plan", chart.Title)
	require.Equal(t, []string{"Build"}, chart.Gantt.Sections)
	require.Len(t, chart.Gantt.Tasks, 2)
	require.True(t, chart.Gantt.Tasks[0].Crit)
	require.True(t, chart.Gantt.Tasks[1].Milestone)
	require.Equal(t, d.gantt.Tasks[0].StartSeconds, chart.Gantt.Tasks[0].Start)
	require.Equal(t, d.gantt.Tasks[0].RenderEnd, chart.Gantt.Tasks[0].RenderEnd)
	require.Equal(t, []string{"weekends"}, chart.Gantt.Excludes)
	require.Len(t, chart.Gantt.Rows, 3)
}
