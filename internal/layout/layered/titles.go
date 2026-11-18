package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sceneTitles(part Layout, o scene.Options, canvasPad int32) ([]Box, error) {
	titles := slices.Clone(part.Titles)
	margin := int64(canvasPad)
	for i := range titles {
		titles[i].Rect = orientRect(titles[i].Rect, o.Direction, part.Height)
		if err := translateBox(&titles[i], margin, margin); err != nil {
			return nil, err
		}
	}
	return titles, nil
}

func fixedTitles(s scene.Scene) []Box {
	var titles []Box
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleGroup {
			continue
		}
		for _, item := range group.Items {
			if text, ok := item.(*scene.Text); ok {
				titles = append(titles, Box{ID: group.Owner, Rect: text.Rect})
			}
		}
	}
	return titles
}

func unorientedTitles(s scene.Scene) ([]Box, error) {
	titles := fixedTitles(s)
	margin := -int64(constant(s.Options.Profile, "canvas_margin"))
	for i := range titles {
		if err := translateBox(&titles[i], margin, margin); err != nil {
			return nil, err
		}
		titles[i].Rect = inverseRect(titles[i].Rect, s.Options.Direction, s.Canvas.W, s.Canvas.H)
	}
	return titles, nil
}
