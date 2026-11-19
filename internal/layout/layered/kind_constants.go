package layered

import "github.com/gosuda/elegant-mermaid/internal/scene"

func kindConstant(profile scene.Profile, kind, name string) int32 {
	return constant(profile, kind+"."+name)
}

func kindWrapWidth(profile scene.Profile, kind string) int32 {
	return kindConstant(profile, kind, "wrapping_width")
}

func canvasMargin(profile scene.Profile, kind string) int32 {
	if margin := kindConstant(profile, kind, "diagram_padding"); margin != 0 {
		return margin
	}
	return constant(profile, "canvas_margin")
}

func (p *Params) applyKindSpacing(profile scene.Profile, kind string) {
	if gap := kindConstant(profile, kind, "node_spacing"); gap != 0 {
		p.NodeGap = gap
	}
	if gap := kindConstant(profile, kind, "rank_spacing"); gap != 0 {
		p.RankGap = gap
	}
}
