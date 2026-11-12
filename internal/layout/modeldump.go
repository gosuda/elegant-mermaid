package layout

import (
	"io"

	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func WriteModelDump(w io.Writer, in Input) error {
	d := scene.Dump{Stage: scene.StageModel, Kind: in.Kind, Options: in.Options}
	d.Options.Profile = in.Profile
	d.Options.Direction = in.Direction
	for _, b := range in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive, Direction: b.Direction})
	}
	for _, r := range in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: r.Orthogonal, MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: r.MarkerEnd, Stroke: r.Line})
	}
	for _, l := range in.Labels {
		d.Labels = append(d.Labels, scene.Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	if err := layered.ValidateOwners(d.Boxes, d.Routes); err != nil {
		return err
	}
	_, err := w.Write(d.AppendJSON(nil))
	return err
}
