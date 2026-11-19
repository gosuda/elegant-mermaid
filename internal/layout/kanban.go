package layout

import (
	"errors"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/grid"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	kanbanmodel "github.com/gosuda/elegant-mermaid/internal/model/kanban"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	kanbanparser "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
)

const (
	kanbanKind           = "kanban"
	kanbanSectionShape   = "kanbanSection"
	kanbanItemShape      = "kanbanItem"
	kanbanPaddingKey     = "padding"
	kanbanSectionKey     = "sectionWidth"
	kanbanBreak          = "<br>"
	kanbanCellPixelsX    = 8
	kanbanVectorPerPixel = 64
)

var errKanbanDomain = errors.New("kanban layout: invalid model")

func (d *Diagram) resolveKanban() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := kanbanparser.Parse(d.Source, d.Preprocessing.Removed)
	d.kanban, resolved = kanbanmodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) kanbanInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromKanban(d.kanban, profile, options)
	return input, diagnostics, nil
}

func FromKanban(m *kanbanmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	if m.Config.PaddingSet {
		options.Config = append(options.Config, scene.Config{Key: kanbanPaddingKey, Value: strconv.FormatInt(m.Config.Padding, 10)})
	}
	if m.Config.SectionWidthSet {
		options.Config = append(options.Config, scene.Config{Key: kanbanSectionKey, Value: strconv.FormatInt(m.Config.SectionWidth, 10)})
	}
	options.Profile = profile
	in := Input{Kind: kanbanKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for s, column := range m.Columns() {
		id := "s" + strconv.Itoa(s)
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleGroup, Shape: kanbanSectionShape, Text: kanbanTrim(m.Nodes[column.Section].Label)})
		for c, card := range column.Cards {
			in.Boxes = append(in.Boxes, Box{ID: id + ".c" + strconv.Itoa(c), Role: scene.RoleNode, Shape: kanbanItemShape, Parent: id, Exclusive: true, Text: kanbanCardText(m.Nodes[card])})
		}
	}
	return in, nil
}

func kanbanCardText(card kanbanmodel.Node) string {
	lines := []string{kanbanTrim(card.Label)}
	if card.Ticket != "" {
		lines = append(lines, "ticket: "+card.Ticket)
	}
	if card.Assigned != "" {
		lines = append(lines, "assigned: "+card.Assigned)
	}
	if card.HasPriority {
		lines = append(lines, "priority: "+card.Priority)
	}
	return strings.Join(lines, kanbanBreak)
}

func kanbanTrim(text string) string {
	return strings.TrimFunc(text, func(r rune) bool {
		switch r {
		case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
			return true
		}
		return r >= 0x2000 && r <= 0x200a
	})
}

type kanbanConstants struct {
	gutter, padding, sectionWidth, bandMin   int32
	cardPadX, cardPadY, cardGap, sectionMinH int32
	border, lineHeight, corner               int32
}

func loadKanbanConstants(in Input) (kanbanConstants, error) {
	var c kanbanConstants
	required := []struct {
		name string
		into *int32
	}{
		{"kanban.gutter", &c.gutter}, {"kanban.padding", &c.padding}, {"kanban.section_width", &c.sectionWidth},
		{"kanban.label_band_min", &c.bandMin}, {"kanban.card_pad_x", &c.cardPadX}, {"kanban.card_pad_y", &c.cardPadY},
		{"kanban.card_gap", &c.cardGap}, {"kanban.section_min_height", &c.sectionMinH},
		{"node_border", &c.border}, {"line_h", &c.lineHeight}, {"corner_radius", &c.corner},
	}
	for _, row := range required {
		value, ok := layoutConstant(in.Profile, row.name)
		if !ok {
			return kanbanConstants{}, errKanbanDomain
		}
		*row.into = value
	}
	return c, c.applyConfig(in)
}

func (c *kanbanConstants) applyConfig(in Input) error {
	for _, entry := range in.Options.Config {
		target := map[string]*int32{kanbanPaddingKey: &c.padding, kanbanSectionKey: &c.sectionWidth}[entry.Key]
		if target == nil {
			continue
		}
		px, err := strconv.ParseInt(entry.Value, 10, 64)
		if err != nil || px < 0 || px > int64(geom.CoordLimit) {
			return geom.ErrOverflow
		}
		units := px * kanbanVectorPerPixel
		if in.Profile == scene.ProfileCell {
			units = (px + kanbanCellPixelsX - 1) / kanbanCellPixelsX
		}
		if units > int64(geom.CoordLimit) {
			return geom.ErrOverflow
		}
		*target = int32(units)
	}
	return nil
}

type kanbanPlan struct {
	in       Input
	c        kanbanConstants
	sections []int
	cards    []int
	owner    map[string]int
	sizes    grid.KanbanInput
	titles   [][]measure.StyledLine
	texts    [][]measure.StyledLine
}

func kanbanLimits(in Input) error {
	limits := in.Options.Limits
	labelled := make(map[string]struct{}, len(in.Labels))
	var bytes int64
	for _, label := range in.Labels {
		labelled[label.Owner] = struct{}{}
		bytes += int64(len(label.Text))
	}
	for _, box := range in.Boxes {
		if _, ok := labelled[box.ID]; !ok {
			bytes += int64(len(box.Text))
		}
	}
	for _, c := range []struct {
		resource      string
		actual, limit int64
	}{
		{"nodes", int64(len(in.Boxes)), int64(limits.MaxNodes)},
		{"edges", int64(len(in.Routes)), int64(limits.MaxEdges)},
		{"text bytes", bytes, int64(limits.MaxTextBytes)},
	} {
		if c.actual > c.limit {
			return &layered.LimitError{Resource: c.resource, Limit: c.limit, Actual: c.actual}
		}
	}
	return nil
}

func newKanbanPlan(in Input) (*kanbanPlan, error) {
	if err := kanbanLimits(in); err != nil {
		return nil, err
	}
	c, err := loadKanbanConstants(in)
	if err != nil {
		return nil, err
	}
	p := &kanbanPlan{in: in, c: c, owner: map[string]int{}}
	for i, box := range in.Boxes {
		switch {
		case !kanbanIsSection(box):
			p.cards = append(p.cards, i)
		case box.Parent != "":
			return nil, errKanbanDomain
		default:
			p.owner[box.ID] = len(p.sections)
			p.sections = append(p.sections, i)
		}
	}
	return p, p.measure()
}

func kanbanIsSection(box Box) bool { return box.Role == scene.RoleGroup || box.Parent == "" }

func (p *kanbanPlan) text(box Box) string {
	for _, label := range p.in.Labels {
		if label.Owner == box.ID {
			return label.Text
		}
	}
	return box.Text
}

func (p *kanbanPlan) lines(text string, wrap int32) ([]measure.StyledLine, error) {
	lines, err := measure.StyledLines(text, max(wrap, 1), sequenceMetric(p.in.Profile, measure.RoleLabel))
	if err != nil {
		return nil, geom.ErrOverflow
	}
	return lines, nil
}

func (p *kanbanPlan) measure() error {
	cardWidth := p.c.sectionWidth - int32(geom.FloorDiv(3*int64(p.c.gutter), 2))
	for _, i := range p.sections {
		lines, err := p.lines(p.text(p.in.Boxes[i]), p.c.sectionWidth-2*p.c.cardPadX)
		if err != nil {
			return err
		}
		p.titles = append(p.titles, lines)
		p.sizes.Sections = append(p.sizes.Sections, grid.KanbanSection{LabelHeight: int32(len(lines)) * p.c.lineHeight})
	}
	for _, i := range p.cards {
		section, ok := p.owner[p.in.Boxes[i].Parent]
		if !ok {
			return errKanbanDomain
		}
		lines, err := p.lines(p.text(p.in.Boxes[i]), cardWidth-2*p.c.cardPadX)
		if err != nil {
			return err
		}
		p.texts = append(p.texts, lines)
		height := int64(max(len(lines), 1))*int64(p.c.lineHeight) + 2*int64(p.c.cardPadY) + 2*int64(p.c.border)
		if height > int64(geom.CoordLimit) {
			return geom.ErrOverflow
		}
		p.sizes.Cards = append(p.sizes.Cards, grid.KanbanCard{Section: section, Height: int32(height)})
	}
	return nil
}

func (p *kanbanPlan) params() grid.KanbanParams {
	return grid.KanbanParams{
		SectionWidth: p.c.sectionWidth, Gutter: p.c.gutter, SectionGap: p.c.cardGap, CardGap: p.c.cardGap,
		Padding: p.c.padding, Border: p.c.border, LabelBandMin: p.c.bandMin, SectionMinHeight: p.c.sectionMinH,
	}
}

func layoutKanban(in Input) (scene.Scene, []diag.Diagnostic, error) {
	in.Options = resolveOptions(in.Options)
	p, err := newKanbanPlan(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	placed, err := grid.Kanban(p.sizes, p.params())
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := p.dump(placed)
	return scene.Scene{Dump: dump, Groups: p.groups(placed)}, nil, nil
}

func (p *kanbanPlan) dump(placed grid.KanbanLayout) scene.Dump {
	options := p.in.Options
	options.Profile, options.Direction = p.in.Profile, p.in.Direction
	d := scene.Dump{Kind: kanbanKind, Options: options, Canvas: placed.Canvas}
	rects := make([]geom.Rect, len(p.in.Boxes))
	for k, i := range p.sections {
		rects[i] = placed.Sections[k]
	}
	for k, i := range p.cards {
		rects[i] = placed.Cards[k]
	}
	for i, box := range p.in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rects[i], Parent: box.Parent, Exclusive: box.Exclusive})
	}
	return d
}
