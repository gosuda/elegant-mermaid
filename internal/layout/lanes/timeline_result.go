package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (pl *timelinePlanner) isCell() bool { return pl.profile == scene.ProfileCell }

func (pl *timelinePlanner) pointBox(v vec) box {
	if pl.isCell() {
		return box{x: v.x, y: v.y, w: 1, h: 1}
	}
	return box{x: v.x, y: v.y}
}

func (pl *timelinePlanner) extent() box {
	extent := pl.pointBox(pl.axis[0])
	extent = union(extent, pl.pointBox(pl.axis[1]))
	if pl.in.Title != nil {
		extent = union(extent, pl.title)
	}
	for _, b := range pl.sections {
		extent = union(extent, b)
	}
	for i, period := range pl.periods {
		extent = union(extent, period)
		for _, b := range pl.events[i] {
			extent = union(extent, b)
		}
		for _, route := range pl.routes[i] {
			for _, v := range route {
				extent = union(extent, pl.pointBox(v))
			}
		}
	}
	return extent
}

func (pl *timelinePlanner) result() (TimelineResult, error) {
	extent := pl.extent()
	f := &frame{dx: pl.c.canvasMargin - extent.x, dy: pl.c.canvasMargin - extent.y}
	res := TimelineResult{Canvas: geom.Size{W: f.fit(extent.w + 2*pl.c.canvasMargin), H: f.fit(extent.h + 2*pl.c.canvasMargin)}}
	if pl.in.Title != nil {
		res.Title = f.rect(pl.title)
	}
	for _, b := range pl.sections {
		res.Sections = append(res.Sections, f.rect(b))
	}
	for i, period := range pl.periods {
		res.Periods = append(res.Periods, f.rect(period))
		events := make([]geom.Rect, len(pl.events[i]))
		for k, b := range pl.events[i] {
			events[k] = f.rect(b)
		}
		routes := make([][]geom.Point, len(pl.routes[i]))
		for k, route := range pl.routes[i] {
			routes[k] = f.points(route)
		}
		res.Events = append(res.Events, events)
		res.Routes = append(res.Routes, routes)
	}
	if f.err != nil {
		return TimelineResult{}, f.err
	}
	res.Groups = pl.paint(f, res)
	return res, f.err
}
