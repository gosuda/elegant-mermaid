package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type frame struct {
	dx, dy int64
	err    error
}

func (f *frame) fit(v int64) int32 {
	if abs(v) > geom.CoordLimit {
		f.err = geom.ErrOverflow
		return 0
	}
	return int32(v)
}

func (f *frame) point(v vec) geom.Point {
	return geom.Point{X: f.fit(v.x + f.dx), Y: f.fit(v.y + f.dy)}
}

func (f *frame) rect(b box) geom.Rect {
	return geom.Rect{X: f.fit(b.x + f.dx), Y: f.fit(b.y + f.dy), W: f.fit(b.w), H: f.fit(b.h)}
}

func (f *frame) points(vs []vec) []geom.Point {
	out := make([]geom.Point, len(vs))
	for i, v := range vs {
		out[i] = f.point(v)
	}
	return out
}

func (pl *planner) isCell() bool { return pl.profile == scene.ProfileCell }

func (pl *planner) pointBox(v vec) box {
	if pl.isCell() {
		return box{x: v.x, y: v.y, w: 1, h: 1}
	}
	return box{x: v.x, y: v.y}
}

func (pl *planner) markerBox(v vec) box {
	if pl.isCell() {
		return box{x: v.x, y: v.y, w: 1, h: 1}
	}
	r := pl.c.commitRadius
	return box{x: v.x - r, y: v.y - r, w: 2 * r, h: 2 * r}
}

func (pl *planner) extent() box {
	var all []box
	for b := range pl.in.Branches {
		all = append(all, pl.lanes[b], pl.pointBox(pl.starts[b]), pl.pointBox(pl.ends[b]))
		if pl.shownLabel(b) != nil {
			all = append(all, pl.branches[b])
		}
	}
	for i, commit := range pl.in.Commits {
		all = append(all, pl.markerBox(pl.points[i]))
		if commit.Label != nil {
			all = append(all, pl.labels[i])
		}
		for _, tag := range pl.tags[i] {
			all = append(all, box{x: tag.x - pl.c.tagPad, y: tag.y - pl.c.tagPad, w: tag.w + 2*pl.c.tagPad, h: tag.h + 2*pl.c.tagPad})
		}
	}
	for _, route := range pl.routes {
		for _, v := range route {
			all = append(all, pl.pointBox(v))
		}
	}
	if len(all) == 0 {
		return box{}
	}
	extent := all[0]
	for _, b := range all[1:] {
		extent = union(extent, b)
	}
	return extent
}

func (pl *planner) result() (GitGraphResult, error) {
	extent := pl.extent()
	f := &frame{dx: pl.c.canvasMargin - extent.x, dy: pl.c.canvasMargin - extent.y}
	res := GitGraphResult{Canvas: geom.Size{W: f.fit(extent.w + 2*pl.c.canvasMargin), H: f.fit(extent.h + 2*pl.c.canvasMargin)}}
	for b := range pl.in.Branches {
		res.Lanes = append(res.Lanes, f.rect(pl.lanes[b]))
		res.BranchLabels = append(res.BranchLabels, f.rect(pl.branchText(b)))
	}
	for i := range pl.in.Commits {
		res.Points = append(res.Points, f.point(pl.points[i]))
		res.CommitLabels = append(res.CommitLabels, f.rect(pl.labels[i]))
		tags := make([]geom.Rect, len(pl.tags[i]))
		for k, tag := range pl.tags[i] {
			tags[k] = f.rect(tag)
		}
		res.TagLabels = append(res.TagLabels, tags)
	}
	for _, route := range pl.routes {
		res.Routes = append(res.Routes, f.points(route))
	}
	if f.err != nil {
		return GitGraphResult{}, f.err
	}
	res.Groups = pl.paint(f, res)
	return res, f.err
}

func (pl *planner) branchText(b int) box {
	label := pl.shownLabel(b)
	if label == nil {
		return box{}
	}
	outer := pl.branches[b]
	return box{x: outer.x + pl.c.branchPadX, y: outer.y + pl.c.branchPadY, w: int64(label.W), h: int64(label.H)}
}
