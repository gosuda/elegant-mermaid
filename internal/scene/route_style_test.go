package scene

import (
	"strings"
	"testing"
)

func TestRouteStylesAreModelStageOnly(t *testing.T) {
	d := Dump{Kind: "flowchart", Options: DefaultOptions(), Routes: []Route{{ID: "e0", From: "A", To: "B", Orthogonal: true, MarkerStart: "circle", MarkerEnd: "cross", Stroke: "dotted"}}}
	layout := string(d.AppendJSON(nil))
	if strings.Contains(layout, `"marker_start"`) || strings.Contains(layout, `"marker_end"`) || strings.Contains(layout, `"stroke"`) {
		t.Fatal("layout bytes must not carry model-only route style keys", layout)
	}
	d.Stage = StageModel
	model := string(d.AppendJSON(nil))
	if !strings.Contains(model, `"orthogonal":true,"marker_start":"circle","marker_end":"cross","stroke":"dotted"`) {
		t.Fatal("model keys must follow orthogonal in fixed order", model)
	}
}
