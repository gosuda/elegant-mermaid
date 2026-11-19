package layout

import (
	"context"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	quadrantmodel "github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	quadrantparser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

const (
	quadrantKind   = "quadrant"
	quadrantFirstP = 5
	quadrantRegion = 3
)

func (d *Diagram) resolveQuadrant() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := quadrantparser.Parse(d.Source, d.Preprocessing.Removed)
	d.quadrant, resolved = quadrantmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.quadrant.AccTitle, d.quadrant.AccDescr
	return parsed, resolved
}

func (d *Diagram) quadrantInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromQuadrant(d.quadrant, profile, options)
}

func FromQuadrant(m *quadrantmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Profile = profile
	for _, entry := range m.Config {
		options.Config = append(options.Config, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	payload := quadrantPayload(m)
	skeleton := chartlayout.QuadrantSkeleton(payload)
	in := Input{Kind: quadrantKind, Profile: profile, Direction: scene.DirectionTB, Options: options, RegionSets: quadrantRegions(payload)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func quadrantPayload(m *quadrantmodel.Model) *chartlayout.Quadrant {
	q := &chartlayout.Quadrant{Title: m.Title, Tiles: m.Quadrants, XLeft: m.XLeft, XRight: m.XRight, YBottom: m.YBottom, YTop: m.YTop, Config: map[string]int64{}}
	for _, entry := range m.Config {
		q.Config[entry.Key] = entry.Value
	}
	for _, p := range m.Points {
		q.Points = append(q.Points, chartlayout.QuadrantPoint{X: p.X, Y: p.Y, Radius: p.Radius, Label: p.Text})
	}
	return q
}

func quadrantRegions(q *chartlayout.Quadrant) []layered.RegionSet {
	sets := make([]layered.RegionSet, len(q.Points))
	for i, p := range q.Points {
		sets[i] = layered.RegionSet{Parent: quadrantFirstP + i, Regions: []int{int(p.X), int(p.Y), int(p.Radius) + 1}}
	}
	return sets
}

func quadrantFromInput(in Input) *chartlayout.Quadrant {
	q := &chartlayout.Quadrant{Config: map[string]int64{}}
	for _, entry := range in.Options.Config {
		if n, err := strconv.ParseInt(entry.Value, 10, 64); err == nil {
			q.Config[entry.Key] = n
		}
	}
	for _, set := range in.RegionSets {
		if len(set.Regions) >= quadrantRegion {
			q.Points = append(q.Points, chartlayout.QuadrantPoint{X: int64(set.Regions[0]), Y: int64(set.Regions[1]), Radius: int64(set.Regions[2]) - 1})
		}
	}
	for _, l := range in.Labels {
		decodeQuadrantLabel(q, l)
	}
	return q
}

func decodeQuadrantLabel(q *chartlayout.Quadrant, l Label) {
	switch l.ID {
	case "title":
		q.Title = l.Text
	case "x.left":
		q.XLeft = l.Text
	case "x.right":
		q.XRight = l.Text
	case "y.bottom":
		q.YBottom = l.Text
	case "y.top":
		q.YTop = l.Text
	}
	decodeQuadrantOwnerLabel(q, l)
}

func decodeQuadrantOwnerLabel(q *chartlayout.Quadrant, l Label) {
	owner, ok := strings.CutSuffix(l.ID, ".label")
	if !ok || owner == "" {
		return
	}
	index, err := strconv.Atoi(owner[1:])
	switch {
	case err != nil:
	case owner[0] == 'q' && index >= 1 && index <= len(q.Tiles):
		q.Tiles[index-1] = l.Text
	case owner[0] == 'p' && index >= 0 && index < len(q.Points):
		q.Points[index].Label = l.Text
	}
}

func layoutQuadrant(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.LayoutQuadrant(context.Background(), quadrantFromInput(in), options)
}
