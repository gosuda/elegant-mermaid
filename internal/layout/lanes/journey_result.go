package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (pl *journeyPlanner) isCell() bool { return pl.profile == scene.ProfileCell }

func (pl *journeyPlanner) faceBox(v vec) box {
	if pl.isCell() {
		return box{x: v.x, y: v.y, w: 1, h: 1}
	}
	r := pl.c.faceRadius
	return box{x: v.x - r, y: v.y - r, w: 2 * r, h: 2 * r}
}

func (pl *journeyPlanner) boxes() []box {
	var all []box
	if pl.in.Title != nil {
		all = append(all, pl.title)
	}
	all = append(all, pl.frames...)
	all = append(all, pl.tasks...)
	for _, v := range pl.faces {
		all = append(all, pl.faceBox(v))
	}
	return all
}

func (pl *journeyPlanner) extent() box {
	all := pl.boxes()
	if len(all) == 0 {
		return box{}
	}
	extent := all[0]
	for _, b := range all[1:] {
		extent = union(extent, b)
	}
	return extent
}

func journeyRects(f *frame, boxes []box) []geom.Rect {
	out := make([]geom.Rect, len(boxes))
	for i, b := range boxes {
		out[i] = f.rect(b)
	}
	return out
}

func (pl *journeyPlanner) result() (JourneyResult, error) {
	extent := pl.extent()
	f := &frame{dx: pl.c.canvasMargin - extent.x, dy: pl.c.canvasMargin - extent.y}
	res := JourneyResult{
		Canvas: geom.Size{W: f.fit(extent.w + 2*pl.c.canvasMargin), H: f.fit(extent.h + 2*pl.c.canvasMargin)},
		Frames: journeyRects(f, pl.frames),
		Bands:  journeyRects(f, pl.bands),
		Tasks:  journeyRects(f, pl.tasks),
		People: journeyRects(f, pl.people),
	}
	if pl.in.Title != nil {
		res.Title = f.rect(pl.title)
	}
	for _, v := range pl.faces {
		res.Faces = append(res.Faces, f.point(v))
	}
	if f.err != nil {
		return JourneyResult{}, f.err
	}
	res.Groups = pl.paint(f, res)
	return res, f.err
}
