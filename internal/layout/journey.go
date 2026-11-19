package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	journeymodel "github.com/gosuda/elegant-mermaid/internal/model/journey"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	journeyparser "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

const (
	journeyKind         = "journey"
	journeyShapeTitle   = "title"
	journeyShapeSection = "section"
	journeyShapeTask    = "task"
	journeyShapePeople  = "people"
	journeyTitleBox     = "title"
	journeyWidthKey     = "width"
	journeyHeightKey    = "height"
	journeyMarginKey    = "diagramMarginX"
)

func (d *Diagram) resolveJourney() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := journeyparser.Parse(d.Source, d.Preprocessing.Removed)
	d.journey, resolved = journeymodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.journey.AccTitle, d.journey.AccDescr
	return parsed, resolved
}

func (d *Diagram) journeyInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromJourney(d.journey, profile, options)
	return input, diagnostics, nil
}

func FromJourney(m *journeymodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = journeyConfig(m.Config)
	options.Profile = profile
	in := Input{Kind: journeyKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	if m.TitleLabel != "" {
		in.Boxes = append(in.Boxes, Box{ID: journeyTitleBox, Role: scene.RoleNode, Shape: journeyShapeTitle, Exclusive: true, Text: m.TitleLabel})
	}
	bands := journeyBands(m.Tasks)
	for b, task := range bands.firsts {
		in.Boxes = append(in.Boxes, Box{ID: journeySectionID(b), Role: scene.RoleGroup, Shape: journeyShapeSection, Text: m.Tasks[task].SectionLabel})
	}
	for i, task := range m.Tasks {
		parent := ""
		if band := bands.of[i]; band >= 0 {
			parent = journeySectionID(band)
		}
		id := "t" + strconv.Itoa(i)
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: journeyShapeTask + ":" + strconv.Itoa(task.Score), Parent: parent, Exclusive: true, Text: task.Label})
		if people := journeyPeople(task.People); people != "" {
			in.Boxes = append(in.Boxes, Box{ID: id + ".people", Role: scene.RoleNode, Shape: journeyShapePeople, Parent: id, Text: people})
		}
	}
	return in, nil
}

func journeySectionID(band int) string { return "s" + strconv.Itoa(band) }

func journeyConfig(c journeymodel.Config) []scene.Config {
	var out []scene.Config
	for _, entry := range []struct {
		key   string
		value int64
		set   bool
	}{{journeyMarginKey, c.MarginX, c.MarginXSet}, {journeyHeightKey, c.Height, c.HeightSet}, {journeyWidthKey, c.Width, c.WidthSet}} {
		if entry.set {
			out = append(out, scene.Config{Key: entry.key, Value: strconv.FormatInt(entry.value, 10)})
		}
	}
	return out
}

func journeyPeople(names []string) string {
	var shown []string
	for _, name := range names {
		if name != "" {
			shown = append(shown, name)
		}
	}
	return strings.Join(shown, ", ")
}

type journeyBandIndex struct {
	of     []int
	firsts []int
}

func journeyBands(tasks []journeymodel.Task) journeyBandIndex {
	index := journeyBandIndex{of: make([]int, len(tasks))}
	previous := ""
	for i, task := range tasks {
		if task.Section != previous {
			previous = task.Section
			if task.Section != "" {
				index.firsts = append(index.firsts, i)
			}
		}
		index.of[i] = len(index.firsts) - 1
		if task.Section == "" {
			index.of[i] = -1
		}
	}
	return index
}
