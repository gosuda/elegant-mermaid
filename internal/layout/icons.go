package layout

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const iconBoxHalf = 768

type IconRef struct {
	Owner     string
	Name      string
	Span      source.Span
	Placement IconPlacement
}

func (d *Diagram) IconRefs() []IconRef {
	if d.architecture != nil {
		return architectureIconRefs(d.architecture)
	}
	if d.flowchart == nil {
		return nil
	}
	var refs []IconRef
	for _, n := range d.flowchart.Nodes {
		if name := n.Attrs["icon"]; name != "" {
			refs = append(refs, IconRef{Owner: n.ID, Name: name, Span: n.Span})
		}
	}
	return refs
}

func PlaceIcons(s *scene.Scene, refs []IconRef, packs []*icon.Pack) []diag.Diagnostic {
	var ds []diag.Diagnostic
	profile := s.Options.Profile
	for _, ref := range refs {
		rect, ok := boxRect(s, ref.Owner)
		if !ok {
			continue
		}
		group := ref.group(s)
		drawing := icon.Draw(packs, ref.drawName(), ref.origin(rect, group, profile), profile)
		if drawing.Missing {
			ds = append(ds, icon.MissingDiagnostic(ref.Name, ref.Span))
		}
		if group != nil {
			group.Items = slices.Insert(group.Items, overlayStart(group.Items), drawing.Items...)
		}
	}
	return ds
}

func qualifiedIcon(name string) string {
	if strings.Contains(name, ":") {
		return name
	}
	return ""
}

func iconOrigin(rect geom.Rect, profile scene.Profile) geom.Point {
	centre := rect.X + rect.W/2
	if profile == scene.ProfileCell {
		return geom.Point{X: centre, Y: rect.Y}
	}
	return geom.Point{X: centre - iconBoxHalf, Y: rect.Y - iconBoxHalf}
}

func boxRect(s *scene.Scene, id string) (geom.Rect, bool) {
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect, true
		}
	}
	return geom.Rect{}, false
}

func nodeGroup(s *scene.Scene, owner string) *scene.Group {
	for _, g := range s.Groups {
		if g.Role == scene.GroupRoleNode && g.Owner == owner {
			return g
		}
	}
	return nil
}

func isOverlay(p scene.Primitive) bool {
	switch p.(type) {
	case *scene.MarkerRef, *scene.SymbolRef, *scene.Text:
		return true
	}
	return false
}

func overlayStart(items []scene.Primitive) int {
	i := 0
	for i < len(items) && !isOverlay(items[i]) {
		i++
	}
	return i
}
