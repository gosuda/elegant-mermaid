package layout

import (
	"context"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	ganttmodel "github.com/gosuda/elegant-mermaid/internal/model/gantt"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	ganttparser "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

const (
	ganttKind = "gantt"

	ganttMilestone = 1
	ganttVert      = 2
	ganttCrit      = 4
	ganttActive    = 8
	ganttDone      = 16
	ganttFields    = 5
)

func (d *Diagram) resolveGantt() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := ganttparser.Parse(d.Source, d.Preprocessing.Removed)
	d.gantt, resolved = ganttmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.gantt.AccTitle, d.gantt.AccDescr
	return parsed, resolved
}

func (d *Diagram) ganttInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromGantt(d.gantt, profile, options)
}

func (d *Diagram) ganttLinks() []interaction.OwnerLink {
	var out []interaction.OwnerLink
	for i, t := range d.gantt.Tasks {
		if t.HasLink {
			out = append(out, interaction.OwnerLink{Owner: "t" + strconv.Itoa(i), Role: scene.GroupRoleNode, URL: t.Link})
		}
	}
	return out
}

func FromGantt(m *ganttmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Profile = profile
	chart := ganttPayload(m)
	options.Config = ganttConfig(chart)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: ganttKind, Profile: profile, Direction: scene.DirectionTB, Options: options, RegionSets: ganttRegions(chart)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func ganttPayload(m *ganttmodel.Model) *chartmodel.Chart {
	g := &chartmodel.Gantt{
		Excludes: m.Excludes, Includes: m.Includes, Weekend: m.Weekend, Weekday: m.EffectiveWeekday(),
		TopAxis: m.EffectiveTopAxis(), AxisForm: m.EffectiveAxisFormat(),
	}
	g.TickEvery, g.TickUnit = m.TickRule()
	for _, s := range m.Sections {
		g.Sections = append(g.Sections, s.Label)
	}
	for _, t := range m.Tasks {
		renderEnd := t.EndSeconds
		if t.HasRenderEnd {
			renderEnd = t.RenderEnd
		}
		g.Tasks = append(g.Tasks, chartmodel.GanttTask{
			Label: t.Label, Section: t.Section, Start: t.StartSeconds, End: t.EndSeconds, RenderEnd: renderEnd,
			Milestone: t.Milestone, Vert: t.Vert, Crit: t.Crit, Active: t.Active, Done: t.Done,
		})
	}
	for _, row := range m.Rows {
		kind := chartmodel.GanttRowTask
		if row.Kind == ganttmodel.RowSection {
			kind = chartmodel.GanttRowSection
		}
		if kind == chartmodel.GanttRowTask && m.Tasks[row.Index].Vert {
			continue
		}
		g.Rows = append(g.Rows, chartmodel.GanttRow{Kind: kind, Index: row.Index})
	}
	chart := &chartmodel.Chart{Kind: chartmodel.KindGantt, Title: m.TitleLabel, Gantt: g}
	for _, key := range ganttIntegerKeys {
		if n, ok := m.ConfigInteger(key); ok {
			chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n}})
		}
	}
	return chart
}

var ganttIntegerKeys = []string{"barGap", "barHeight", "leftPadding", "rightPadding", "topPadding"}

func ganttConfig(chart *chartmodel.Chart) []scene.Config {
	g := chart.Gantt
	out := []scene.Config{
		scene.ConfigString("axisFormat", g.AxisForm),
		scene.ConfigString("weekday", g.Weekday),
		scene.ConfigString("weekend", g.Weekend),
	}
	for _, e := range chart.Config {
		out = append(out, scene.Config{Key: e.Key, Value: strconv.FormatInt(e.Value.Integer, 10)})
	}
	if len(g.Excludes) > 0 {
		out = append(out, scene.ConfigString("excludes", strings.Join(g.Excludes, ",")))
	}
	if len(g.Includes) > 0 {
		out = append(out, scene.ConfigString("includes", strings.Join(g.Includes, ",")))
	}
	if g.TickEvery > 0 {
		out = append(out, scene.ConfigString("tickInterval", strconv.FormatInt(g.TickEvery, 10)+g.TickUnit))
	}
	if g.TopAxis {
		out = append(out, scene.ConfigBool("topAxis", true))
	}
	slices.SortFunc(out, func(a, b scene.Config) int { return strings.Compare(a.Key, b.Key) })
	return out
}

func ganttRegions(c *chartmodel.Chart) []layered.RegionSet {
	sets := make([]layered.RegionSet, len(c.Gantt.Tasks))
	for i, t := range c.Gantt.Tasks {
		flags := 0
		for _, f := range []struct {
			on   bool
			flag int
		}{{t.Milestone, ganttMilestone}, {t.Vert, ganttVert}, {t.Crit, ganttCrit}, {t.Active, ganttActive}, {t.Done, ganttDone}} {
			if f.on {
				flags |= f.flag
			}
		}
		sets[i] = layered.RegionSet{Parent: i, Regions: []int{flags, t.Section + 1, zigzag(t.Start), zigzag(t.End), zigzag(t.RenderEnd)}}
	}
	return sets
}

func ganttFromInput(in Input) *chartmodel.Chart {
	g := &chartmodel.Gantt{}
	texts := make(map[string]string, len(in.Labels))
	for _, l := range in.Labels {
		texts[l.ID] = l.Text
	}
	chart := &chartmodel.Chart{Kind: chartmodel.KindGantt, Title: texts["title"], Gantt: g}
	for _, entry := range in.Options.Config {
		decodeGanttConfig(chart, xychartConfigEntry(entry))
	}
	for _, set := range in.RegionSets {
		if len(set.Regions) >= ganttFields {
			g.Tasks = append(g.Tasks, decodeGanttTask(set.Regions, texts["t"+strconv.Itoa(len(g.Tasks))+".label"]))
		}
	}
	for _, b := range in.Boxes {
		decodeGanttBox(g, texts, b.ID)
	}
	return chart
}

func decodeGanttTask(r []int, label string) chartmodel.GanttTask {
	return chartmodel.GanttTask{
		Label: label, Section: r[1] - 1, Start: unzigzag(r[2]), End: unzigzag(r[3]), RenderEnd: unzigzag(r[4]),
		Milestone: r[0]&ganttMilestone != 0, Vert: r[0]&ganttVert != 0, Crit: r[0]&ganttCrit != 0,
		Active: r[0]&ganttActive != 0, Done: r[0]&ganttDone != 0,
	}
}

func parseGanttBoxID(id string) (kind byte, index int, ok bool) {
	if len(id) < 2 || (id[0] != 's' && id[0] != 't') {
		return 0, 0, false
	}
	index, err := strconv.Atoi(id[1:])
	return id[0], index, err == nil
}

func decodeGanttBox(g *chartmodel.Gantt, texts map[string]string, id string) {
	kind, index, ok := parseGanttBoxID(id)
	if !ok {
		return
	}
	if kind == 's' {
		g.Sections = append(g.Sections, texts[id+".label"])
		g.Rows = append(g.Rows, chartmodel.GanttRow{Kind: chartmodel.GanttRowSection, Index: len(g.Sections) - 1})
		return
	}
	if index < len(g.Tasks) && !g.Tasks[index].Vert {
		g.Rows = append(g.Rows, chartmodel.GanttRow{Kind: chartmodel.GanttRowTask, Index: index})
	}
}

func decodeGanttConfig(chart *chartmodel.Chart, entry chartmodel.ConfigEntry) {
	g := chart.Gantt
	switch entry.Key {
	case "axisFormat":
		g.AxisForm = entry.Value.String
	case "weekday":
		g.Weekday = entry.Value.String
	case "weekend":
		g.Weekend = entry.Value.String
	case "excludes":
		g.Excludes = strings.Split(entry.Value.String, ",")
	case "includes":
		g.Includes = strings.Split(entry.Value.String, ",")
	case "topAxis":
		g.TopAxis = entry.Value.Bool
	case "tickInterval":
		decodeGanttTick(g, entry.Value.String)
	default:
		chart.Config = append(chart.Config, entry)
	}
}

func decodeGanttTick(g *chartmodel.Gantt, text string) {
	digits := 0
	for digits < len(text) && text[digits] >= '0' && text[digits] <= '9' {
		digits++
	}
	if n, err := strconv.ParseInt(text[:digits], 10, 64); err == nil {
		g.TickEvery, g.TickUnit = n, text[digits:]
	}
}

func layoutGantt(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.Layout(context.Background(), ganttFromInput(in), options)
}
