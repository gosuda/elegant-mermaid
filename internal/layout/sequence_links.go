package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (d *Diagram) sequenceLinks() []interaction.OwnerLink {
	var out []interaction.OwnerLink
	for _, actor := range d.sequence.Actors {
		for _, link := range actor.Links {
			url, ok := interaction.SafeURL(link.Value)
			if !ok {
				continue
			}
			out = append(out, interaction.OwnerLink{Owner: actor.ID, Role: scene.GroupRoleNode, URL: url, Tooltip: link.Key, HasTooltip: link.Key != ""})
		}
	}
	return out
}
