package layered

import "github.com/gosuda/elegant-mermaid/internal/geom"

func appendBoxSizes(out *Input, in Input, index int) {
	if len(in.Sizes) > 0 {
		var size geom.Size
		if index < len(in.Sizes) {
			size = in.Sizes[index]
		}
		out.Sizes = append(out.Sizes, size)
	}
	if len(in.Exact) > 0 {
		out.Exact = append(out.Exact, index < len(in.Exact) && in.Exact[index])
	}
}
