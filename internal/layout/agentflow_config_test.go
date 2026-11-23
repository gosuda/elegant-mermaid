package layout

import (
	"bytes"
	"encoding/json"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	agentflowmodel "github.com/gosuda/elegant-mermaid/internal/model/agentflow"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func TestAgentflowModelRetainsAuthoredPadding(t *testing.T) {
	cases := []struct {
		name, source, padding string
	}{
		{"absent", "agentflow-beta\nA\n", ""},
		{"zero", "---\nconfig:\n  flowchart:\n    padding: 0\n---\nagentflow-beta\nA\n", "0"},
		{"authored", "---\nconfig:\n  flowchart:\n    padding: 64\n---\nagentflow-beta\nA\n", "64"},
		{"outside integer range", "---\nconfig:\n  flowchart:\n    padding: 4294967296\n---\nagentflow-beta\nA\n", ""},
		{"init precedence", "---\nconfig:\n  flowchart:\n    padding: 64\n---\n%%{init: {\"flowchart\": {\"padding\": 17}}}%%\nagentflow-beta\nA\n", "17"},
	}
	for _, tc := range cases {
		for _, profile := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
			t.Run(tc.name+"/"+profile.String(), func(t *testing.T) {
				d := ParseDiagram([]byte(tc.source))
				in, err := d.Input(profile, scene.Options{})
				require.NoError(t, err)
				var buffer bytes.Buffer
				require.NoError(t, WriteModelDump(&buffer, in))
				var model struct {
					Options map[string]json.RawMessage `json:"options"`
				}
				require.NoError(t, json.Unmarshal(buffer.Bytes(), &model))
				require.Equal(t, tc.padding, string(model.Options["flowchart.padding"]))
			})
		}
	}
}

func TestAgentflowRejectsNegativePaddingWithoutNodes(t *testing.T) {
	_, _, err := FromAgentflow(&agentflowmodel.Model{PaddingSet: true, Padding: -1}, scene.ProfileCell, scene.Options{})
	require.ErrorIs(t, err, geom.ErrDomain)
}

func TestAgentflowRejectsCollapsedHeightOverflow(t *testing.T) {
	source := "---\nconfig:\n  flowchart:\n    padding: 16000000\n---\nagentflow-beta\nflow A[A]\nend\nA@{ view: \"collapsed\" }\n"
	d := ParseDiagram([]byte(source))
	_, err := d.Input(scene.ProfileVector, scene.Options{})
	require.ErrorIs(t, err, geom.ErrOverflow)
}
