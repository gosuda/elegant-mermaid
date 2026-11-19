package layout

import (
	"context"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	treemapmodel "github.com/gosuda/elegant-mermaid/internal/model/treemap"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	treemapparser "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
)

const (
	treemapKind     = "treemap"
	treemapNameTag  = ".name"
	treemapValueTag = ".value"
)

func (d *Diagram) resolveTreemap() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := treemapparser.Parse(d.Source, d.Preprocessing.Removed)
	d.treemap, resolved = treemapmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.treemap.AccTitle, d.treemap.AccDescr
	return parsed, resolved
}

func (d *Diagram) treemapInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromTreemap(d.treemap, profile, options)
}

func FromTreemap(m *treemapmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = treemapConfig(m)
	options.Profile = profile
	flat := treemapFlat(m)
	skeleton, err := chartlayout.ModelSkeleton(treemapPayload(m, flat))
	if err != nil {
		return Input{}, nil, err
	}
	regions, err := treemapRegions(flat)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: treemapKind, Profile: profile, Direction: scene.DirectionTB, Options: options, RegionSets: regions}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func treemapConfig(m *treemapmodel.Model) []scene.Config {
	out := make([]scene.Config, len(m.Config))
	for i, entry := range m.Config {
		out[i] = scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)}
	}
	return out
}

type treemapSource struct {
	node   *treemapmodel.Node
	target *chartmodel.TreemapNode
	parent int
}

func treemapFlat(m *treemapmodel.Model) []treemapSource {
	var flat, stack []treemapSource
	for i := len(m.Roots) - 1; i >= 0; i-- {
		stack = append(stack, treemapSource{node: m.Roots[i], parent: -1})
	}
	for len(stack) > 0 {
		next := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		at := len(flat)
		flat = append(flat, next)
		for i := len(next.node.Children) - 1; i >= 0; i-- {
			stack = append(stack, treemapSource{node: next.node.Children[i], parent: at})
		}
	}
	return flat
}

func treemapPayload(m *treemapmodel.Model, flat []treemapSource) *chartmodel.Chart {
	chart := &chartmodel.Chart{Kind: chartmodel.KindTreemap, Title: m.Title, Treemap: &chartmodel.Treemap{}}
	for _, entry := range m.Config {
		chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: entry.Value}})
	}
	for i := range flat {
		source := &flat[i]
		source.target = &chartmodel.TreemapNode{Name: source.node.Name, Index: source.node.Index}
		if len(source.node.Children) == 0 {
			source.target.Value = chartmodel.Number(source.node.Value)
		}
		if source.parent < 0 {
			chart.Treemap.Roots = append(chart.Treemap.Roots, source.target)
			continue
		}
		parent := flat[source.parent].target
		parent.Children = append(parent.Children, source.target)
	}
	sums := make([]int64, len(flat))
	for i := len(flat) - 1; i >= 0; i-- {
		sums[i] += int64(flat[i].target.Value)
		if flat[i].parent >= 0 {
			sums[flat[i].parent] += sums[i]
		}
		if sums[i] != 0 {
			flat[i].target.ValueText = treemapmodel.FormatValue(sums[i])
		}
	}
	return chart
}

func treemapRegions(flat []treemapSource) ([]layered.RegionSet, error) {
	var leaves []int
	var raw []int64
	for i, source := range flat {
		if len(source.node.Children) == 0 {
			leaves = append(leaves, i)
			raw = append(raw, source.node.Value)
		}
	}
	norm, err := chartlayout.TreemapNormalize(raw)
	if err != nil {
		return nil, err
	}
	values := make([]int, len(flat))
	for k, i := range leaves {
		values[i] = int(norm[k])
	}
	return []layered.RegionSet{{Regions: values}}, nil
}

func treemapFromInput(in Input) *chartmodel.Chart {
	chart := &chartmodel.Chart{Kind: chartmodel.KindTreemap, Treemap: &chartmodel.Treemap{}}
	for _, entry := range in.Options.Config {
		if n, err := strconv.ParseInt(entry.Value, 10, 64); err == nil {
			chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n}})
		}
	}
	texts := make(map[string]string, len(in.Labels))
	for _, l := range in.Labels {
		texts[l.ID] = l.Text
	}
	chart.Title = texts["title"]
	var values []int
	if len(in.RegionSets) > 0 {
		values = in.RegionSets[0].Regions
	}
	nodes := make(map[string]*chartmodel.TreemapNode, len(in.Boxes))
	ordinal := 0
	for _, b := range in.Boxes {
		if b.ID == chartlayout.TreemapRootID {
			continue
		}
		node := &chartmodel.TreemapNode{Name: texts[b.ID+treemapNameTag], ValueText: texts[b.ID+treemapValueTag], Index: ordinal}
		if ordinal < len(values) {
			node.Value = chartmodel.Number(values[ordinal])
		}
		ordinal++
		nodes[b.ID] = node
		if parent, ok := nodes[b.Parent]; ok {
			parent.Children = append(parent.Children, node)
		} else {
			chart.Treemap.Roots = append(chart.Treemap.Roots, node)
		}
	}
	return chart
}

func treemapLimits(in Input) error {
	limits := resolveOptions(in.Options).Limits
	if nodes := int64(len(in.Boxes)); nodes > int64(limits.MaxNodes) {
		return &layered.LimitError{Resource: "nodes", Limit: int64(limits.MaxNodes), Actual: nodes}
	}
	var bytes int64
	for _, label := range in.Labels {
		bytes += int64(len(label.Text))
	}
	if bytes > int64(limits.MaxTextBytes) {
		return &layered.LimitError{Resource: "text bytes", Limit: int64(limits.MaxTextBytes), Actual: bytes}
	}
	return nil
}

func layoutTreemap(in Input) (scene.Scene, []diag.Diagnostic, error) {
	if err := treemapLimits(in); err != nil {
		return scene.Scene{}, nil, err
	}
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.Layout(context.Background(), treemapFromInput(in), options)
}
