package layout

import (
	"fmt"
	"math"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	agentflowmodel "github.com/gosuda/elegant-mermaid/internal/model/agentflow"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func TestFramedAgentflowContentClearsInnerRules(t *testing.T) {
	const text = "abcdefghijklmno"
	for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		for _, shape := range []string{"subroutine", "subprocess", "subproc", "framed-rectangle"} {
			for _, padding := range []int{-1, 0, 17} {
				t.Run(fmt.Sprintf("%s/%s/%d", profile, shape, padding), func(t *testing.T) {
					m := &agentflowmodel.Model{PaddingSet: padding >= 0, Padding: padding}
					_, size, err := agentflowContent(text, shape, m, profile, "")
					require.NoError(t, err)
					width, _, err := agentflowMeasured(text, profile, "")
					require.NoError(t, err)
					padX, _, err := agentflowPadding(m, profile)
					require.NoError(t, err)
					inset, err := agentflowConstant(profile, "padding")
					require.NoError(t, err)
					left := (size.W - width) / 2
					right := left + width
					inset = min(inset, size.W/3)
					require.GreaterOrEqual(t, left-inset, padX, "left rule consumed text padding")
					require.GreaterOrEqual(t, size.W-inset-right, padX, "right rule consumed text padding")
				})
			}
		}
	}
}

func TestToolLabelRendersEveryCell(t *testing.T) {
	text := renderDecorationCells(t, "agentflow-beta TB\nA[\"abcdefghijklmno\"]@{ shape: tool }\n")
	require.Contains(t, text, "abcdefghijklmno")
}

func TestStateRegionDividerPreservesParentTitle(t *testing.T) {
	for _, direction := range []string{"TB", "LR"} {
		t.Run(direction, func(t *testing.T) {
			source := "stateDiagram-v2\ndirection " + direction + "\nstate Outer {\ndirection " + direction + "\nA --> B\n--\nC --> D\n}\n"
			text := renderDecorationCells(t, source)
			require.Contains(t, text, "Outer")
		})
	}
}

func TestStateNoteRoutingPreservesTransitionLabel(t *testing.T) {
	for _, direction := range []string{"TB", "BT", "LR", "RL"} {
		t.Run(direction, func(t *testing.T) {
			source := "stateDiagram-v2\ndirection " + direction + "\nstate Auth {\n[*] --> Login\nLogin --> MFA : code\nMFA --> Success\n}\n[*] --> Auth\nAuth --> [*]\nNote right of Auth: Handles user auth\nNote right of MFA: One-time code\n"
			text := renderDecorationCells(t, source)
			require.Equal(t, 2, strings.Count(text, "code"))
			require.Contains(t, text, "Handles user auth")
			require.Contains(t, text, "One-time code")
		})
	}
}

func TestSwimlaneRoutesPreserveTransitionLabels(t *testing.T) {
	for _, name := range []string{
		"swimlanes~0013.mmd",
		"swimlanes~pr-check~12-disagree-exits-b-c.mmd",
		"swimlanes~pr-check~query-process.mmd",
		"swimlanes~pr-check~sales-process.mmd",
		"swimlanes~pr-check~mermaid-work.mmd",
	} {
		t.Run(name, func(t *testing.T) {
			source, err := os.ReadFile(filepath.Join("..", "..", "corpus", "swimlane", "mermaid", name))
			require.NoError(t, err)
			rendered := renderDecoration(t, string(source))
			require.Zero(t, rendered.RefusedClusters, "%s", rendered.Text)
		})
	}
}

func renderDecorationCells(t *testing.T, source string) string {
	t.Helper()
	rendered := renderDecoration(t, source)
	require.Zero(t, rendered.RefusedClusters, "%s", rendered.Text)
	require.Zero(t, rendered.RouteConflicts, "%s", rendered.Text)
	return strings.TrimSpace(string(rendered.Text))
}

func renderDecoration(t *testing.T, source string) cells.Result {
	t.Helper()
	d := ParseDiagram([]byte(source))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, diag.SeverityError, diagnostic.Severity, "%s: %s", diagnostic.Code, diagnostic.Message)
	}
	in, err := d.Input(scene.ProfileCell, scene.Options{})
	require.NoError(t, err)
	for _, family := range Families {
		if family.Kind != in.Kind {
			continue
		}
		s, _, err := family.Layout(in)
		require.NoError(t, err)
		valid, err := s.Check()
		require.NoError(t, err)
		require.True(t, valid)
		scene.ProjectCellAttachments(&s)
		rendered, err := cells.Render(s, cells.Options{})
		require.NoError(t, err)
		return rendered
	}
	t.Fatalf("missing family %s", in.Kind)
	return cells.Result{}
}

func TestStateSeparatorStopsAtChildEnvelope(t *testing.T) {
	parent := geom.Rect{W: 120, H: 100}
	cases := []struct {
		name string
		a, b geom.Rect
		want [2]geom.Point
	}{
		{"vertical", geom.Rect{X: 10, Y: 30, W: 30, H: 40}, geom.Rect{X: 60, Y: 20, W: 40, H: 60}, [2]geom.Point{{X: 50, Y: 20}, {X: 50, Y: 80}}},
		{"horizontal", geom.Rect{X: 20, Y: 10, W: 60, H: 20}, geom.Rect{X: 30, Y: 50, W: 40, H: 30}, [2]geom.Point{{X: 20, Y: 40}, {X: 80, Y: 40}}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got, err := regionSeparator(parent, tc.a, tc.b, 5)
			require.NoError(t, err)
			require.Equal(t, tc.want, got)
			reversed, err := regionSeparator(parent, tc.b, tc.a, 5)
			require.NoError(t, err)
			require.Equal(t, got, reversed)
		})
	}
}

func TestStateSeparatorRejectsInvalidBodyBounds(t *testing.T) {
	parent := geom.Rect{W: 120, H: 100}
	_, err := regionSeparator(parent, geom.Rect{X: math.MaxInt32 - 5, W: 10, H: 10}, geom.Rect{X: 10, W: 10, H: 10}, 5)
	require.ErrorIs(t, err, geom.ErrOverflow)
	_, err = regionSeparator(parent, geom.Rect{X: 200, Y: 20, W: 10, H: 10}, geom.Rect{X: 230, Y: 20, W: 10, H: 10}, 5)
	require.ErrorIs(t, err, errStateDomain)
}
