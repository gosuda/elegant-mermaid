package layout

import (
	"context"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	cynefinmodel "github.com/gosuda/elegant-mermaid/internal/model/cynefin"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	cynefinparser "github.com/gosuda/elegant-mermaid/internal/syntax/cynefin"
)

const cynefinKind = "cynefin"

func (d *Diagram) resolveCynefin() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := cynefinparser.Parse(d.Source, d.Preprocessing.Removed)
	d.cynefin, resolved = cynefinmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.cynefin.AccTitle, d.cynefin.AccDescr
	return parsed, resolved
}

func (d *Diagram) cynefinInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromCynefin(d.cynefin, profile, options), nil, nil
}

func FromCynefin(m *cynefinmodel.Model, profile scene.Profile, options scene.Options) Input {
	options = resolveOptions(options)
	options.Config = cynefinConfig(m)
	options.Profile = profile
	frame := chartlayout.CynefinSkeleton(cynefinPayload(m))
	in := Input{Kind: cynefinKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for _, b := range frame.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, r := range frame.Routes {
		in.Routes = append(in.Routes, Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: r.Orthogonal, MarkerStart: "none", MarkerEnd: "point", Line: "normal"})
	}
	for _, l := range frame.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in
}

func cynefinConfig(m *cynefinmodel.Model) []scene.Config {
	out := make([]scene.Config, 0, len(m.Config))
	for _, entry := range m.Config {
		out = append(out, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	slices.SortFunc(out, func(a, b scene.Config) int { return strings.Compare(a.Key, b.Key) })
	return out
}

func cynefinPayload(m *cynefinmodel.Model) *chartmodel.Cynefin {
	chart := &chartmodel.Cynefin{Title: m.Title}
	for _, entry := range m.Config {
		chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: entry.Value}})
	}
	for _, d := range m.Domains {
		domain := chartmodel.CynefinDomain{Name: d.Name}
		for _, item := range d.Items {
			domain.Items = append(domain.Items, item.Label)
		}
		chart.Domains = append(chart.Domains, domain)
	}
	for _, t := range m.Transitions {
		chart.Transitions = append(chart.Transitions, chartmodel.CynefinTransition{From: t.From, To: t.To, Label: t.Label})
	}
	return chart
}

func cynefinFromInput(in Input) *chartmodel.Cynefin {
	chart := &chartmodel.Cynefin{}
	for _, entry := range in.Options.Config {
		chart.Config = append(chart.Config, xychartConfigEntry(entry))
	}
	for _, b := range in.Boxes {
		if b.ID != "frame" {
			chart.Domains = append(chart.Domains, chartmodel.CynefinDomain{Name: b.ID})
		}
	}
	for _, l := range in.Labels {
		decodeCynefinLabel(chart, l)
	}
	for _, r := range in.Routes {
		chart.Transitions = append(chart.Transitions, chartmodel.CynefinTransition{From: r.From, To: r.To, Label: routeLabelText(in, r.ID)})
	}
	return chart
}

func routeLabelText(in Input, id string) string {
	i := slices.IndexFunc(in.Labels, func(l Label) bool { return l.Owner == id })
	if i < 0 {
		return ""
	}
	return in.Labels[i].Text
}

func decodeCynefinLabel(chart *chartmodel.Cynefin, l Label) {
	if l.ID == "title" {
		chart.Title = l.Text
		return
	}
	name, rest, ok := strings.Cut(l.ID, ".i")
	index, err := strconv.Atoi(rest)
	i := slices.IndexFunc(chart.Domains, func(d chartmodel.CynefinDomain) bool { return d.Name == name })
	if ok && err == nil && index >= 0 && i >= 0 && l.Owner == name {
		chart.Domains[i].Items = append(chart.Domains[i].Items, l.Text)
	}
}

func layoutCynefin(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.LayoutCynefin(context.Background(), cynefinFromInput(in), options)
}
