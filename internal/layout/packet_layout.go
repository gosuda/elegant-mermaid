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
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errPacketDomain = errors.New("packet layout: invalid model")

type packetText struct {
	lines []measure.StyledLine
	size  geom.Size
}

type packetBit struct {
	owner int
	trail bool
	rect  geom.Rect
	packetText
}

type packetBox struct {
	title       bool
	piece       int
	start, end  int64
	rect        geom.Rect
	text        packetText
	lead, trail *packetBit
}

type packetPlan struct {
	in      Input
	profile scene.Profile
	params  grid.PacketParams
	boxes   []packetBox
	bits    []*packetBit
	owner   map[string]int
}

func layoutPacket(in Input) (scene.Scene, []diag.Diagnostic, error) {
	in.Options = resolveOptions(in.Options)
	p, err := newPacketPlan(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	result, err := grid.Packet(p.gridInput(), p.params)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := p.dump(result)
	return scene.Scene{Dump: dump, Groups: p.groups()}, nil, nil
}

func newPacketPlan(in Input) (*packetPlan, error) {
	if err := packetLimits(in); err != nil {
		return nil, err
	}
	p := &packetPlan{in: in, profile: in.Profile, owner: make(map[string]int, len(in.Boxes))}
	if err := p.constants(); err != nil {
		return nil, err
	}
	if err := p.decodeBoxes(); err != nil {
		return nil, err
	}
	return p, p.decodeLabels()
}

func packetLimits(in Input) error {
	if nodes := int64(len(in.Boxes)); nodes > int64(in.Options.Limits.MaxNodes) {
		return &layered.LimitError{Resource: "nodes", Limit: int64(in.Options.Limits.MaxNodes), Actual: nodes}
	}
	owned := make(map[string]bool, len(in.Labels))
	var bytes int64
	for _, label := range in.Labels {
		owned[label.Owner] = true
		bytes += int64(len(label.Text))
	}
	for _, box := range in.Boxes {
		if !owned[box.ID] {
			bytes += int64(len(box.Text))
		}
	}
	if bytes > int64(in.Options.Limits.MaxTextBytes) {
		return &layered.LimitError{Resource: "text bytes", Limit: int64(in.Options.Limits.MaxTextBytes), Actual: bytes}
	}
	return nil
}

func (p *packetPlan) lineHeight(role scene.TextRole) int32 {
	if p.profile == scene.ProfileCell {
		return 1
	}
	return packetRole(role).LineHeightPx() * unitsPerPx
}

func (p *packetPlan) constants() error {
	required := []struct {
		name string
		into *int32
	}{
		{"packet.bits_per_row", &p.params.BitsPerRow}, {"packet.bit_width", &p.params.BitWidth}, {"packet.row_height", &p.params.RowHeight},
		{"packet.padding_x", &p.params.PaddingX}, {"packet.padding_y", &p.params.PaddingY}, {"packet.show_bits_pad", &p.params.ShowBitsPad},
		{"packet.margin_x", &p.params.MarginX}, {"line_h", &p.params.LineHeight},
	}
	for _, row := range required {
		value, ok := layoutConstant(p.profile, row.name)
		if !ok {
			return errPacketDomain
		}
		*row.into = value
	}
	p.params.ShowBits = true
	for _, entry := range p.in.Options.Config {
		if err := p.applyEntry(entry); err != nil {
			return err
		}
	}
	return nil
}

func (p *packetPlan) sizeField(key string) *int32 {
	switch key {
	case "rowHeight":
		return &p.params.RowHeight
	case "bitWidth":
		return &p.params.BitWidth
	case "paddingX":
		return &p.params.PaddingX
	case "paddingY":
		return &p.params.PaddingY
	}
	return nil
}

func (p *packetPlan) applyEntry(entry scene.Config) error {
	switch entry.Key {
	case packetShowBits:
		p.params.ShowBits = entry.Value == "true"
	case packetBitOrder:
		p.params.Descending = entry.Value == `"descending"`
	case "bitsPerRow":
		return packetCount(entry.Value, &p.params.BitsPerRow)
	default:
		return p.applySize(entry, p.sizeField(entry.Key))
	}
	return nil
}

func (p *packetPlan) applySize(entry scene.Config, into *int32) error {
	if into == nil || p.profile != scene.ProfileVector {
		return nil
	}
	px, err := strconv.ParseInt(entry.Value, 10, 64)
	if err != nil || px < 0 || px*unitsPerPx > int64(geom.CoordLimit) {
		return geom.ErrOverflow
	}
	*into = int32(px * unitsPerPx)
	return nil
}

func packetCount(text string, into *int32) error {
	value, err := strconv.ParseInt(text, 10, 32)
	if err != nil || value < 1 {
		return geom.ErrOverflow
	}
	*into = int32(value)
	return nil
}

func (p *packetPlan) decodeBoxes() error {
	pieces, next := 0, int64(0)
	for i, box := range p.in.Boxes {
		decoded, err := decodePacketBox(box, next)
		if err != nil {
			return err
		}
		if !decoded.title {
			decoded.piece = pieces
			pieces++
			next = decoded.end + 1
		}
		p.owner[box.ID] = i
		p.boxes = append(p.boxes, decoded)
	}
	return nil
}

func decodePacketBox(box Box, next int64) (packetBox, error) {
	if box.Role != scene.RoleNode {
		return packetBox{}, errPacketDomain
	}
	switch box.Shape {
	case packetTitleShape:
		return packetBox{title: true}, nil
	case "":
		return packetBox{start: next, end: next}, nil
	}
	fields := strings.Split(box.Shape, ";")
	if len(fields) != 3 || fields[0] != packetFieldShape {
		return packetBox{}, errPacketDomain
	}
	start, okStart := strings.CutPrefix(fields[1], "start=")
	end, okEnd := strings.CutPrefix(fields[2], "end=")
	first, errStart := strconv.ParseInt(start, 10, 64)
	last, errEnd := strconv.ParseInt(end, 10, 64)
	if !okStart || !okEnd || errStart != nil || errEnd != nil {
		return packetBox{}, errPacketDomain
	}
	return packetBox{start: first, end: last}, nil
}

func (p *packetPlan) measureText(text string, role scene.TextRole) (packetText, error) {
	metric := measure.CellMetric()
	if p.profile == scene.ProfileVector {
		metric = measure.ForRole(packetRole(role))
	}
	lines, err := measure.StyledLines(text, geom.I32Max, metric)
	if err != nil {
		return packetText{}, geom.ErrOverflow
	}
	height := int64(len(lines)) * int64(p.lineHeight(role))
	if height > int64(geom.CoordLimit) {
		return packetText{}, geom.ErrOverflow
	}
	return packetText{lines: lines, size: geom.Size{W: widestLine(lines), H: int32(height)}}, nil
}

func packetRole(role scene.TextRole) measure.Role {
	switch role {
	case scene.TextRoleTitle:
		return measure.RoleTitle
	case scene.TextRoleBody:
		return measure.RoleBody
	}
	return measure.RoleLabel
}

func (p *packetPlan) boxRole(i int) scene.TextRole {
	if p.boxes[i].title {
		return scene.TextRoleTitle
	}
	return scene.TextRoleLabel
}

func (p *packetPlan) decodeLabels() error {
	labelled := make([]bool, len(p.boxes))
	p.bits = make([]*packetBit, len(p.in.Labels))
	for j, label := range p.in.Labels {
		owner, known := p.owner[label.Owner]
		if !known {
			return errPacketDomain
		}
		switch {
		case label.ID == label.Owner+".label":
			text, err := p.measureText(label.Text, p.boxRole(owner))
			if err != nil {
				return err
			}
			p.boxes[owner].text, labelled[owner] = text, true
		case packetBitLabel(label.ID) && !p.boxes[owner].title:
			if err := p.attachBit(owner, j, label); err != nil {
				return err
			}
		default:
			return errPacketDomain
		}
	}
	return p.measureUnlabelled(labelled)
}

func (p *packetPlan) attachBit(owner, j int, label Label) error {
	text, err := p.measureText(label.Text, scene.TextRoleBody)
	if err != nil {
		return err
	}
	bit := &packetBit{owner: owner, trail: strings.HasSuffix(label.ID, ".trail"), packetText: text}
	p.bits[j] = bit
	if bit.trail {
		p.boxes[owner].trail = bit
		return nil
	}
	p.boxes[owner].lead = bit
	return nil
}

func (p *packetPlan) measureUnlabelled(labelled []bool) error {
	for i, box := range p.in.Boxes {
		if labelled[i] {
			continue
		}
		text, err := p.measureText(packetBoxText(box), p.boxRole(i))
		if err != nil {
			return err
		}
		p.boxes[i].text = text
	}
	return nil
}

func packetBoxText(box Box) string {
	if box.Text != "" {
		return box.Text
	}
	return box.ID
}

func (p *packetPlan) gridInput() grid.PacketInput {
	var in grid.PacketInput
	for _, box := range p.boxes {
		if box.title {
			in.HasTitle = true
			continue
		}
		piece := grid.PacketPiece{Start: box.start, End: box.end}
		if box.lead != nil {
			piece.Lead = box.lead.size
		}
		if box.trail != nil {
			piece.Trail = box.trail.size
		}
		in.Pieces = append(in.Pieces, piece)
	}
	return in
}
