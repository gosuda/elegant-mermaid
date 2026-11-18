package layout

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/interaction"
	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (d *Diagram) Links() []interaction.OwnerLink {
	switch {
	case d.sequence != nil:
		return d.sequenceLinks()
	case d.state != nil:
		return d.stateLinks()
	case d.agentflow != nil:
		return d.agentflowLinks()
	case d.gantt != nil:
		return d.ganttLinks()
	case d.flowchart != nil:
		return d.flowchartLinks()
	}
	return nil
}

func (d *Diagram) flowchartLinks() []interaction.OwnerLink {
	var out []interaction.OwnerLink
	for _, c := range d.flowchart.Clicks {
		url, ok := interaction.SafeURL(c.URL)
		if c.Kind != flowmodel.ClickLink || !ok {
			continue
		}
		for id := range strings.SplitSeq(c.Target, ",") {
			if id = strings.TrimSpace(id); id != "" {
				out = append(out, interaction.OwnerLink{Owner: id, Role: scene.GroupRoleNode, URL: url, Tooltip: c.Tip, HasTooltip: c.Tip != ""})
			}
		}
	}
	return out
}
