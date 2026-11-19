package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (d *Diagram) stateLinks() []interaction.OwnerLink {
	var out []interaction.OwnerLink
	for _, link := range d.state.Links {
		url, ok := interaction.SafeURL(link.URL.Value)
		if !ok {
			continue
		}
		tip := ""
		if link.Tooltip != nil {
			tip = link.Tooltip.Value
		}
		out = append(out, interaction.OwnerLink{Owner: link.Target, Role: scene.GroupRoleNode, URL: url, Tooltip: tip, HasTooltip: tip != ""})
	}
	return out
}

func (d *Diagram) agentflowLinks() []interaction.OwnerLink {
	var out []interaction.OwnerLink
	for _, link := range d.agentflow.Links {
		if link.URL == nil {
			continue
		}
		url, ok := interaction.SafeURL(*link.URL)
		if !ok {
			continue
		}
		tip := ""
		if link.Tooltip != nil {
			tip = *link.Tooltip
		}
		out = append(out, interaction.OwnerLink{Owner: link.ID, Role: scene.GroupRoleNode, URL: url, Tooltip: tip, HasTooltip: tip != ""})
	}
	return out
}
