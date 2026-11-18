package layout

import (
	"context"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	infomodel "github.com/gosuda/elegant-mermaid/internal/model/info"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	infoparser "github.com/gosuda/elegant-mermaid/internal/syntax/info"
)

const infoKind = "info"

func (d *Diagram) resolveInfo() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := infoparser.Parse(d.Source, d.Preprocessing.Removed)
	d.info, resolved = infomodel.Resolve(ast)
	return parsed, resolved
}

func (d *Diagram) infoInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromInfo(d.info, profile, options), nil, nil
}

func FromInfo(m *infomodel.Model, profile scene.Profile, options scene.Options) Input {
	options = resolveOptions(options)
	options.Config = nil
	options.Profile = profile
	frame := chartlayout.InfoSkeleton(&chartmodel.Info{Text: "v" + m.Version})
	return Input{
		Kind: infoKind, Profile: profile, Direction: scene.DirectionTB, Options: options,
		Boxes:  []Box{{ID: frame.Box.ID, Role: frame.Box.Role}},
		Labels: []Label{{ID: frame.Label.ID, Owner: frame.Label.Owner, Text: frame.Label.Text}},
	}
}

func infoFromInput(in Input) *chartmodel.Info {
	for _, l := range in.Labels {
		if l.ID == "version" {
			return &chartmodel.Info{Text: l.Text}
		}
	}
	return &chartmodel.Info{}
}

func layoutInfo(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.LayoutInfo(context.Background(), infoFromInput(in), options)
}
