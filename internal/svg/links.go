package svg

import (
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type linkKey struct {
	owner string
	role  scene.GroupRole
}

type anchor interaction.OwnerLink

func indexLinks(links []interaction.OwnerLink) map[linkKey]anchor {
	out := make(map[linkKey]anchor, len(links))
	for _, l := range links {
		if l.Owner != "" {
			out[linkKey{l.Owner, l.Role}] = anchor(l)
		}
	}
	return out
}

func (a anchor) open() string {
	out := "<a href='" + escape(a.URL) + "'>\n"
	if a.HasTooltip {
		out += "<title>" + escape(a.Tooltip) + "</title>\n"
	}
	return out
}
