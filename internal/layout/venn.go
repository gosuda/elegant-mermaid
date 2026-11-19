package layout

import (
	"context"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	vennmodel "github.com/gosuda/elegant-mermaid/internal/model/venn"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	vennparser "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

const (
	vennKind = "venn"

	vennTagSet     = 0
	vennTagOverlap = 1
	vennTagRegion  = 2
)

func (d *Diagram) resolveVenn() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := vennparser.Parse(d.Source, d.Preprocessing.Removed)
	d.venn, resolved = vennmodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) vennInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromVenn(d.venn, profile, options)
}

func FromVenn(m *vennmodel.Model, _ scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = vennConfig(m)
	options.Profile = scene.ProfileVector
	chart := vennPayload(m)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: vennKind, Profile: scene.ProfileVector, Direction: scene.DirectionTB, Options: options, RegionSets: vennRegions(chart.Venn)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func vennConfig(m *vennmodel.Model) []scene.Config {
	out := make([]scene.Config, 0, len(m.Config))
	for _, entry := range m.Config {
		out = append(out, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	slices.SortFunc(out, func(a, b scene.Config) int { return strings.Compare(a.Key, b.Key) })
	return out
}

func vennTexts(m *vennmodel.Model, key []string) []string {
	var out []string
	for _, t := range m.Texts {
		if slices.Equal(t.Sets, key) {
			out = append(out, t.Display)
		}
	}
	return out
}

func vennPayload(m *vennmodel.Model) *chartmodel.Chart {
	sets := m.Sets()
	ids := make([]string, len(sets))
	v := &chartmodel.Venn{}
	for i, s := range sets {
		ids[i] = s.ID
		v.Sets = append(v.Sets, chartmodel.VennSet{Label: s.Display, Size: chartmodel.Number(s.Size), Texts: vennTexts(m, []string{s.ID})})
	}
	var keys [][]string
	labels := map[int]string{}
	for _, s := range m.Subsets {
		if len(s.Sets) < 2 {
			continue
		}
		at := slices.IndexFunc(keys, func(k []string) bool { return slices.Equal(k, s.Sets) })
		if at < 0 {
			at = len(keys)
			keys = append(keys, s.Sets)
		}
		labels[at] = s.Display
		vennOverlap(v, ids, s)
	}
	for at, key := range keys {
		region := chartmodel.VennRegion{Sets: vennMembers(ids, key), Label: labels[at], Texts: vennTexts(m, key)}
		if region.Label != "" || len(region.Texts) > 0 {
			v.Regions = append(v.Regions, region)
		}
	}
	return &chartmodel.Chart{Kind: chartmodel.KindVenn, Title: m.Title, Venn: v}
}

func vennMembers(ids, key []string) []int {
	var out []int
	for _, id := range key {
		if i := slices.Index(ids, id); i >= 0 && !slices.Contains(out, i) {
			out = append(out, i)
		}
	}
	slices.Sort(out)
	return out
}

func vennOverlap(v *chartmodel.Venn, ids []string, s vennmodel.Subset) {
	if len(s.Sets) != 2 || s.Sets[0] == s.Sets[1] {
		return
	}
	pair := vennMembers(ids, s.Sets)
	if len(pair) != 2 {
		return
	}
	overlap := chartmodel.VennOverlap{A: pair[0], B: pair[1], Value: chartmodel.Number(s.Size)}
	for i := range v.Overlaps {
		if v.Overlaps[i].A == overlap.A && v.Overlaps[i].B == overlap.B {
			v.Overlaps[i].Value = overlap.Value
			return
		}
	}
	v.Overlaps = append(v.Overlaps, overlap)
}

func vennRegions(v *chartmodel.Venn) []layered.RegionSet {
	var sets []layered.RegionSet
	for _, s := range v.Sets {
		sets = append(sets, layered.RegionSet{Regions: []int{vennTagSet, zigzag(int64(s.Size))}})
	}
	for _, o := range v.Overlaps {
		sets = append(sets, layered.RegionSet{Regions: []int{vennTagOverlap, o.A, o.B, zigzag(int64(o.Value))}})
	}
	for _, r := range v.Regions {
		sets = append(sets, layered.RegionSet{Regions: append([]int{vennTagRegion}, r.Sets...)})
	}
	return sets
}

func vennFromInput(in Input) *chartmodel.Chart {
	v := &chartmodel.Venn{}
	chart := &chartmodel.Chart{Kind: chartmodel.KindVenn, Venn: v}
	for _, entry := range in.Options.Config {
		chart.Config = append(chart.Config, xychartConfigEntry(entry))
	}
	for _, set := range in.RegionSets {
		decodeVennRegion(v, set.Regions)
	}
	for _, l := range in.Labels {
		decodeVennLabel(chart, l)
	}
	return chart
}

func decodeVennRegion(v *chartmodel.Venn, r []int) {
	switch {
	case len(r) == 2 && r[0] == vennTagSet:
		v.Sets = append(v.Sets, chartmodel.VennSet{Size: chartmodel.Number(unzigzag(r[1]))})
	case len(r) == 4 && r[0] == vennTagOverlap:
		v.Overlaps = append(v.Overlaps, chartmodel.VennOverlap{A: r[1], B: r[2], Value: chartmodel.Number(unzigzag(r[3]))})
	case len(r) >= 1 && r[0] == vennTagRegion:
		v.Regions = append(v.Regions, chartmodel.VennRegion{Sets: slices.Clone(r[1:])})
	}
}

func decodeVennLabel(chart *chartmodel.Chart, l Label) {
	if l.ID == "title" {
		chart.Title = l.Text
		return
	}
	v := chart.Venn
	if index, rest, ok := vennOwnerOf(l.ID, "set"); ok && index < len(v.Sets) {
		decodeVennText(&v.Sets[index].Label, &v.Sets[index].Texts, rest, l.Text)
	}
	if index, rest, ok := vennOwnerOf(l.ID, "region"); ok && index < len(v.Regions) {
		decodeVennText(&v.Regions[index].Label, &v.Regions[index].Texts, rest, l.Text)
	}
}

func decodeVennText(label *string, texts *[]string, rest, text string) {
	if rest == ".label" {
		*label = text
		return
	}
	if strings.HasPrefix(rest, ".t") {
		*texts = append(*texts, text)
	}
}

func vennOwnerOf(id, prefix string) (index int, rest string, ok bool) {
	tail, found := strings.CutPrefix(id, prefix)
	if !found {
		return 0, "", false
	}
	digits := len(tail) - len(strings.TrimLeft(tail, "0123456789"))
	index, err := strconv.Atoi(tail[:digits])
	return index, tail[digits:], err == nil
}

func layoutVennChart(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = scene.ProfileVector
	return chartlayout.Layout(context.Background(), vennFromInput(in), options)
}
