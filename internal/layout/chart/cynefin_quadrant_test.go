package chart

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestCynefinQuadrantsTileOddFrames(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for w := int64(1); w <= 9; w++ {
			for h := int64(1); h <= 9; h++ {
				assertCynefinTiling(t, profile, w, h)
			}
		}
	}
}

func assertCynefinTiling(t *testing.T, profile scene.Profile, w, h int64) {
	t.Helper()
	p := cynefinPlan{profile: profile, c: cynefinConsts{width: w, height: h}}
	var area int64
	var boxes []rect
	for _, name := range []string{"complex", "complicated", "clear", "chaotic"} {
		b := p.quadrant(name)
		assertCynefinQuadrant(t, &p, name, b, boxes)
		area += b.w * b.h
		boxes = append(boxes, b)
	}
	if area != w*h {
		t.Fatalf("%v %dx%d: covered area %d", profile, w, h, area)
	}
}

func assertCynefinQuadrant(t *testing.T, p *cynefinPlan, name string, b rect, earlierBoxes []rect) {
	t.Helper()
	profile, w, h := p.profile, p.c.width, p.c.height
	if b.x < 0 || b.y < 0 || b.w < 0 || b.h < 0 || b.right() > w || b.bottom() > h {
		t.Fatalf("%v %dx%d %s: invalid quadrant %+v", profile, w, h, name, b)
	}
	for _, earlier := range earlierBoxes {
		if min(b.right(), earlier.right()) > max(b.x, earlier.x) && min(b.bottom(), earlier.bottom()) > max(b.y, earlier.y) {
			t.Fatalf("%v %dx%d: overlapping quadrants", profile, w, h)
		}
	}
}
