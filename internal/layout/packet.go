package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	packetmodel "github.com/gosuda/elegant-mermaid/internal/model/packet"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	packetparser "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
)

const (
	packetKind       = "packet"
	packetTitleID    = "title"
	packetTitleShape = "title"
	packetFieldShape = "field"
	packetShowBits   = "showBits"
	packetBitOrder   = "bitOrder"
)

func (d *Diagram) resolvePacket() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := packetparser.Parse(d.Source, d.Preprocessing.Removed)
	d.packet, resolved = packetmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.packet.AccTitle, d.packet.AccDescr
	return parsed, resolved
}

func (d *Diagram) packetInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromPacket(d.packet, profile, options)
	return input, diagnostics, nil
}

func FromPacket(m *packetmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = packetConfig(m)
	options.Profile = profile
	in := Input{Kind: packetKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	if m.Title != "" {
		in.addPacketBox(packetTitleID, packetTitleShape, scene.TextRoleTitle, m.Title)
	}
	for i, piece := range m.Pieces {
		id := packetPieceID(i)
		shape := packetFieldShape + ";start=" + strconv.FormatInt(piece.Start, 10) + ";end=" + strconv.FormatInt(piece.End, 10)
		in.addPacketBox(id, shape, scene.TextRoleLabel, piece.Label)
		if m.ShowBits {
			in.addBitLabels(id, piece, m.Descending)
		}
	}
	return in, nil
}

func packetPieceID(index int) string { return "f" + strconv.Itoa(index) }

func packetConfig(m *packetmodel.Model) []scene.Config {
	out := make([]scene.Config, len(m.Config))
	for i, entry := range m.Config {
		switch entry.Kind {
		case packetmodel.ConfigBool:
			out[i] = scene.ConfigBool(entry.Key, entry.Bool)
		case packetmodel.ConfigString:
			out[i] = scene.ConfigString(entry.Key, entry.Text)
		default:
			out[i] = scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Int, 10)}
		}
	}
	return out
}

func (in *Input) addPacketBox(id, shape string, role scene.TextRole, text string) {
	in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: shape, Exclusive: true, Text: text})
	if text != id {
		in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: role, Text: text})
	}
}

func (in *Input) addBitLabels(owner string, piece packetmodel.Piece, descending bool) {
	lead, trail := piece.Start, piece.End
	if descending {
		lead, trail = trail, lead
	}
	if piece.End == piece.Start {
		in.Labels = append(in.Labels, Label{ID: owner + ".bit", Owner: owner, Role: scene.TextRoleBody, Text: strconv.FormatInt(lead, 10)})
		return
	}
	in.Labels = append(in.Labels,
		Label{ID: owner + ".lead", Owner: owner, Role: scene.TextRoleBody, Text: strconv.FormatInt(lead, 10)},
		Label{ID: owner + ".trail", Owner: owner, Role: scene.TextRoleBody, Text: strconv.FormatInt(trail, 10)},
	)
}

func packetBitLabel(id string) bool {
	return strings.HasSuffix(id, ".bit") || strings.HasSuffix(id, ".lead") || strings.HasSuffix(id, ".trail")
}
