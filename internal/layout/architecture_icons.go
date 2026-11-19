package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	archmodel "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type IconPlacement uint8

const (
	PlaceEdge IconPlacement = iota
	PlaceService
	PlaceBadge
)

func architectureIconRefs(m *archmodel.Model) []IconRef {
	var refs []IconRef
	for _, g := range m.Groups {
		if g.Icon != "" {
			refs = append(refs, IconRef{Owner: g.ID, Name: g.Icon, Span: g.Span, Placement: PlaceBadge})
		}
	}
	for _, n := range m.Nodes {
		if !n.Junction && n.Icon != "" {
			refs = append(refs, IconRef{Owner: n.ID, Name: n.Icon, Span: n.Span, Placement: PlaceService})
		}
	}
	return refs
}

func (r IconRef) drawName() string {
	if r.Placement == PlaceEdge {
		return qualifiedIcon(r.Name)
	}
	return r.Name
}

func (r IconRef) group(s *scene.Scene) *scene.Group {
	role := scene.GroupRoleNode
	if r.Placement == PlaceBadge {
		role = scene.GroupRoleGroup
	}
	for _, g := range s.Groups {
		if g.Role == role && g.Owner == r.Owner {
			return g
		}
	}
	return nil
}

func (r IconRef) origin(rect geom.Rect, group *scene.Group, profile scene.Profile) geom.Point {
	switch r.Placement {
	case PlaceService:
		return centredOrigin(outlineRect(group, rect), profile)
	case PlaceBadge:
		inset, _ := layoutConstant(profile, "architecture.title_inset")
		return geom.Point{X: rect.X + inset, Y: rect.Y + inset}
	}
	return iconOrigin(rect, profile)
}

func outlineRect(group *scene.Group, fallback geom.Rect) geom.Rect {
	if group == nil {
		return fallback
	}
	for _, item := range group.Items {
		switch shape := item.(type) {
		case *scene.RoundRect:
			return shape.Rect
		case *scene.Rect:
			return shape.Rect
		}
	}
	return fallback
}

func centredOrigin(rect geom.Rect, profile scene.Profile) geom.Point {
	x, y := rect.X+rect.W/2, rect.Y+rect.H/2
	if profile == scene.ProfileCell {
		return geom.Point{X: x, Y: y}
	}
	return geom.Point{X: x - iconBoxHalf, Y: y - iconBoxHalf}
}
