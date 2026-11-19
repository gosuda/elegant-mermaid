package layout

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var packetProfiles = []scene.Profile{scene.ProfileVector, scene.ProfileCell}

func packetSource(t *testing.T, path string) string {
	t.Helper()
	data, err := os.ReadFile(path)
	require.NoError(t, err)
	return string(data)
}

func packetInput(t *testing.T, src string, profile scene.Profile) Input {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, diag.SeverityError, diagnostic.Severity, diagnostic.Message)
	}
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	return in
}

func packetScene(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	s, _, err := Layout(packetInput(t, src, profile))
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	return s
}

func renderedPacket(t *testing.T, s scene.Scene, charset cells.Charset) string {
	t.Helper()
	rendered, err := cells.Render(s, cells.Options{Charset: charset})
	require.NoError(t, err)
	return string(rendered.Text)
}

func TestPacketCorpusLaysOutValidly(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "packet", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src := packetSource(t, path)
		for _, profile := range packetProfiles {
			packetScene(t, src, profile)
		}
	}
}

func TestPacketModelDumpEncodesPiecesAndBitNumbers(t *testing.T) {
	in := packetInput(t, "packet\ntitle T\n0-3: \"a\"\n4: \"f1\"\n+60: \"c\"\n", scene.ProfileVector)
	ids := make([]string, len(in.Boxes))
	for i, b := range in.Boxes {
		ids[i] = b.ID + " " + b.Shape
		require.True(t, b.Exclusive)
	}
	require.Equal(t, []string{
		"title title", "f0 field;start=0;end=3", "f1 field;start=4;end=4", "f2 field;start=5;end=31", "f3 field;start=32;end=63", "f4 field;start=64;end=64",
	}, ids)
	labels := make([]string, len(in.Labels))
	for i, l := range in.Labels {
		labels[i] = l.ID + "=" + l.Text
	}
	require.Equal(t, []string{
		"title.label=T", "f0.label=a", "f0.lead=0", "f0.trail=3", "f1.bit=4",
		"f2.label=c", "f2.lead=5", "f2.trail=31", "f3.label=c", "f3.lead=32", "f3.trail=63", "f4.label=c", "f4.bit=64",
	}, labels)
}

func TestPacketModelDumpOptionsFollowTheConfig(t *testing.T) {
	src := "---\nconfig:\n  packet:\n    showBits: false\n    bitOrder: descending\n    bitsPerRow: 16\n    rowHeight: 40\n---\npacket\n0-3: \"a\"\n"
	in := packetInput(t, src, scene.ProfileVector)
	got := make([]string, len(in.Options.Config))
	for i, c := range in.Options.Config {
		got[i] = c.Key + "=" + c.Value
	}
	require.Equal(t, []string{`bitOrder="descending"`, "bitsPerRow=16", "rowHeight=40", "showBits=false"}, got)
	require.Empty(t, in.Labels[1:], "no bit numbers without showBits")
}

func TestPacketCellRendering(t *testing.T) {
	s := packetScene(t, "packet-beta\n0-7: \"Type\"\n8-15: \"Len\"\n", scene.ProfileCell)
	want := strings.Join([]string{
		"0             7 8            15",
		"┌─────────────┐ ┌─────────────┐",
		"│    Type     │ │     Len     │",
		"└─────────────┘ └─────────────┘",
		"",
		"",
	}, "\n")
	require.Equal(t, want, renderedPacket(t, s, cells.CharsetUnicode))
	ascii := renderedPacket(t, s, cells.CharsetASCII)
	require.Contains(t, ascii, "+-------------+ +-------------+")
}

func TestPacketCellRowsSplitAtTheConfiguredWidth(t *testing.T) {
	src := "---\nconfig:\n  packet:\n    bitsPerRow: 8\n    showBits: false\n---\npacket\n0-11: \"a\"\n12-15: \"b\"\n"
	want := strings.Join([]string{
		"",
		"┌─────────────┐",
		"│      a      │",
		"└─────────────┘",
		"",
		"┌─────┐ ┌─────┐",
		"│  a  │ │  b  │",
		"└─────┘ └─────┘",
		"",
		"",
	}, "\n")
	require.Equal(t, want, renderedPacket(t, packetScene(t, src, scene.ProfileCell), cells.CharsetUnicode))
}

func TestPacketDescendingNumbersRun_HighToLow(t *testing.T) {
	src := "---\nconfig:\n  packet:\n    bitOrder: descending\n    bitsPerRow: 16\n---\npacket\n0-7: \"DATA\"\n8-15: \"HIGH\"\n"
	text := renderedPacket(t, packetScene(t, src, scene.ProfileCell), cells.CharsetUnicode)
	first := strings.Split(text, "\n")[0]
	require.True(t, strings.HasPrefix(first, "15"), first)
	require.True(t, strings.HasSuffix(first, "0"), first)
	row := strings.Split(text, "\n")[2]
	require.Less(t, strings.Index(row, "HIGH"), strings.Index(row, "DATA"))
}

func TestPacketVectorConfigScalesPixels(t *testing.T) {
	src := "---\nconfig:\n  packet:\n    bitWidth: 10\n    bitsPerRow: 8\n    rowHeight: 20\n    paddingX: 2\n    paddingY: 4\n---\npacket\n0-3: \"a\"\n"
	s := packetScene(t, src, scene.ProfileVector)
	require.Equal(t, geom.Size{W: 8*10*64 + 128, H: 2560 + 1280}, s.Canvas)
	rect := s.Boxes[0].Rect
	require.Equal(t, geom.Rect{X: 64, Y: (4 + 16) * 64, W: (4*10 - 2) * 64, H: 20 * 64}, rect)
	cell := packetScene(t, src, scene.ProfileCell)
	require.Equal(t, int32(16), cell.Canvas.W, "pixel keys are ignored by the cell profile")
}

func TestPacketTitleFormsTheLastBand(t *testing.T) {
	for _, profile := range packetProfiles {
		s := packetScene(t, "packet\ntitle Hello\n0-7: \"a\"\n", profile)
		title, field := s.Boxes[0], s.Boxes[1]
		require.Equal(t, "title", title.ID)
		require.GreaterOrEqual(t, title.Rect.Y, field.Rect.Y+field.Rect.H)
		require.Equal(t, s.Canvas.H, title.Rect.Y+title.Rect.H)
		group := s.Groups[0]
		require.Equal(t, "title", group.Owner)
		require.Len(t, group.Items, 1)
		text, ok := group.Items[0].(*scene.Text)
		require.True(t, ok)
		require.Equal(t, scene.TextRoleTitle, text.Role)
	}
}

func TestPacketSceneItems(t *testing.T) {
	s := packetScene(t, "packet\n0-7: \"a\"\n8: \"b\"\n", scene.ProfileVector)
	require.Len(t, s.Groups, 2)
	first := s.Groups[0].Items
	require.Len(t, first, 4)
	rect, ok := first[0].(*scene.Rect)
	require.True(t, ok)
	require.Equal(t, "node", rect.Style)
	styles := []string{}
	aligns := []scene.Align{}
	for _, item := range first[1:] {
		text := item.(*scene.Text)
		styles = append(styles, text.Style)
		aligns = append(aligns, text.Align)
	}
	require.Equal(t, []string{"text", "text-muted", "text-muted"}, styles)
	require.Equal(t, []scene.Align{scene.AlignMiddle, scene.AlignStart, scene.AlignEnd}, aligns)
	single := s.Groups[1].Items
	require.Len(t, single, 3)
	require.Equal(t, scene.AlignMiddle, single[2].(*scene.Text).Align)
}

func TestPacketBitNumbersSitAboveTheirRow(t *testing.T) {
	for _, profile := range packetProfiles {
		s := packetScene(t, "packet\n0-15: \"a\"\n16-31: \"b\"\n32: \"c\"\n", profile)
		for _, label := range s.Labels {
			var owner scene.Box
			for _, box := range s.Boxes {
				if box.ID == label.Owner {
					owner = box
				}
			}
			require.Equal(t, owner.Rect.Y, label.Rect.Y+label.Rect.H, label.ID)
		}
	}
}

func TestPacketLimits(t *testing.T) {
	in := packetInput(t, "packet\n0-7: \"a\"\n", scene.ProfileCell)
	in.Options.Limits = scene.Limits{MaxNodes: 1, MaxEdges: 1, MaxTextBytes: 1 << 20}
	in.Boxes = append(in.Boxes, Box{ID: "f1", Role: scene.RoleNode, Shape: "field;start=8;end=8", Exclusive: true, Text: "f1"})
	_, _, err := Layout(in)
	var limit *layered.LimitError
	require.ErrorAs(t, err, &limit)
	require.Equal(t, "nodes", limit.Resource)
	in.Options.Limits.MaxNodes = 10
	in.Options.Limits.MaxTextBytes = 2
	_, _, err = Layout(in)
	require.ErrorAs(t, err, &limit)
	require.Equal(t, "text bytes", limit.Resource)
}

func TestPacketRejectsForeignInput(t *testing.T) {
	good := packetInput(t, "packet\n0-7: \"a\"\n", scene.ProfileCell)
	for name, edit := range map[string]func(*Input){
		"unknown shape":  func(in *Input) { in.Boxes[0].Shape = "circle" },
		"bad range":      func(in *Input) { in.Boxes[0].Shape = "field;start=x;end=3" },
		"missing field":  func(in *Input) { in.Boxes[0].Shape = "field;start=0" },
		"group box":      func(in *Input) { in.Boxes[0].Role = scene.RoleGroup },
		"stray label":    func(in *Input) { in.Labels = append(in.Labels, Label{ID: "f0.other", Owner: "f0", Text: "x"}) },
		"unknown owner":  func(in *Input) { in.Labels = append(in.Labels, Label{ID: "g.lead", Owner: "g", Text: "x"}) },
		"reversed range": func(in *Input) { in.Boxes[0].Shape = "field;start=5;end=3" },
	} {
		in := good
		in.Boxes = slices.Clone(good.Boxes)
		in.Labels = slices.Clone(good.Labels)
		edit(&in)
		_, _, err := Layout(in)
		require.Error(t, err, name)
	}
}

func TestPacketShapelessBoxesContinueTheBits(t *testing.T) {
	in := Input{Kind: "packet", Options: scene.DefaultOptions(), Profile: scene.ProfileCell, Boxes: []Box{{ID: "a", Exclusive: true}, {ID: "b", Exclusive: true}}}
	s, _, err := Layout(in)
	require.NoError(t, err)
	require.Less(t, s.Boxes[0].Rect.X, s.Boxes[1].Rect.X)
}

func TestPacketEmptyDocument(t *testing.T) {
	for _, profile := range packetProfiles {
		s := packetScene(t, "packet\n", profile)
		require.Empty(t, s.Boxes)
		require.Empty(t, s.Groups)
	}
}

func TestPacketSplitFieldsRepeatTheirLabel(t *testing.T) {
	s := packetScene(t, "packet\n0-63: \"wide\"\n", scene.ProfileCell)
	require.Len(t, s.Groups, 2)
	for _, group := range s.Groups {
		var found bool
		for _, item := range group.Items {
			if text, ok := item.(*scene.Text); ok && text.Style == "text" {
				found = true
				require.Equal(t, "wide", text.Lines[0][0].Text)
			}
		}
		require.True(t, found, group.Owner)
	}
}

func TestPacketCorpusTextContainsEveryLabel(t *testing.T) {
	src := packetSource(t, filepath.Join("..", "..", "corpus", "packet", "mermaid", "packet~0002.mmd"))
	text := renderedPacket(t, packetScene(t, src, scene.ProfileCell), cells.CharsetUnicode)
	for _, want := range []string{"Source Port", "Destination Port", "Length", "Checksum", "Data (variable length)", "UDP Packet"} {
		require.Contains(t, text, want)
	}
}
