package layout

import (
	"fmt"
	"io"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func WriteModelDump(w io.Writer, in Input) error {
	d := scene.Dump{Stage: scene.StageModel, Kind: in.Kind, Options: in.Options}
	d.Options.Profile = in.Profile
	d.Options.Direction = in.Direction
	owners := labelOwners(in.Labels)
	for _, b := range in.Boxes {
		text := b.Text
		if in.Kind != architectureKind {
			text = modelBoxText(b, owners)
		}
		d.Boxes = append(d.Boxes, scene.Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive, Direction: b.Direction, Shape: b.Shape, Icon: b.Icon, Text: text})
	}
	for _, r := range in.Routes {
		if r.FromSide > geom.SideRight || r.ToSide > geom.SideRight {
			return fmt.Errorf("route %q has an invalid endpoint side: %w", r.ID, layered.ErrGraph)
		}
		d.Routes = append(d.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: r.Orthogonal, MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: modelMarkerEnd(r.MarkerEnd), Stroke: r.Line, FromSide: r.FromSide, ToSide: r.ToSide, MinLength: modelMinLength(in.Kind, r, owners)})
	}
	for _, l := range in.Labels {
		d.Labels = append(d.Labels, scene.Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	for _, set := range in.RegionSets {
		d.Regions = append(d.Regions, append([]int{set.Parent}, set.Regions...))
	}
	if err := layered.ValidateOwners(d.Boxes, d.Routes); err != nil {
		return err
	}
	_, err := w.Write(d.AppendJSON(nil))
	return err
}

func labelOwners(labels []Label) map[string]struct{} {
	owners := make(map[string]struct{}, len(labels))
	for _, l := range labels {
		owners[l.Owner] = struct{}{}
	}
	return owners
}

func modelBoxText(b Box, owners map[string]struct{}) string {
	if _, labelled := owners[b.ID]; labelled || b.Text == b.ID {
		return ""
	}
	return b.Text
}

func modelMinLength(kind string, r Route, owners map[string]struct{}) int32 {
	floor := int32(1)
	if _, labelled := owners[r.ID]; labelled {
		floor = 2
	}
	if length := edgeMinLength(kind, r); length > floor {
		return length
	}
	return 0
}

func modelMarkerEnd(marker string) string {
	if marker == "" {
		return "none"
	}
	return marker
}
