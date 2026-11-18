package grid

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var (
	kanbanVector = KanbanParams{SectionWidth: 12800, Gutter: 640, SectionGap: 320, CardGap: 320, Padding: 512, Border: 0, LabelBandMin: 1600, SectionMinHeight: 3200}
	kanbanCell   = KanbanParams{SectionWidth: 25, Gutter: 1, SectionGap: 1, CardGap: 1, Padding: 1, Border: 1, LabelBandMin: 1, SectionMinHeight: 4}
)

func TestKanbanVectorColumnsAndCards(t *testing.T) {
	in := KanbanInput{
		Sections: []KanbanSection{{LabelHeight: 1280}, {LabelHeight: 1280}},
		Cards:    []KanbanCard{{Section: 0, Height: 2560}, {Section: 0, Height: 3840}},
	}
	out, err := Kanban(in, kanbanVector)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{{X: 512, Y: 512, W: 12800, H: 8960}, {X: 13632, Y: 512, W: 12800, H: 3200}}, out.Sections)
	require.Equal(t, []geom.Rect{{X: 992, Y: 2112, W: 11840, H: 2560}, {X: 992, Y: 4992, W: 11840, H: 3840}}, out.Cards)
	require.Equal(t, geom.Rect{X: 512, Y: 672, W: 12800, H: 1280}, out.Labels[0])
	require.Equal(t, geom.Size{W: 26944, H: 9984}, out.Canvas)
}

func TestKanbanCellColumnsAndCards(t *testing.T) {
	in := KanbanInput{
		Sections: []KanbanSection{{LabelHeight: 1}, {LabelHeight: 1}},
		Cards:    []KanbanCard{{Section: 0, Height: 3}, {Section: 0, Height: 4}},
	}
	out, err := Kanban(in, kanbanCell)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{{X: 1, Y: 1, W: 25, H: 12}, {X: 27, Y: 1, W: 25, H: 5}}, out.Sections)
	require.Equal(t, []geom.Rect{{X: 1, Y: 3, W: 24, H: 3}, {X: 1, Y: 7, W: 24, H: 4}}, out.Cards)
	require.Equal(t, geom.Rect{X: 1, Y: 2, W: 25, H: 1}, out.Labels[0])
	require.Equal(t, geom.Size{W: 53, H: 14}, out.Canvas)
}

func TestKanbanHeaderBandGrowsWithTallestLabel(t *testing.T) {
	in := KanbanInput{
		Sections: []KanbanSection{{LabelHeight: 2560}, {LabelHeight: 1280}},
		Cards:    []KanbanCard{{Section: 1, Height: 2560}},
	}
	out, err := Kanban(in, kanbanVector)
	require.NoError(t, err)
	require.Equal(t, int32(512+2560), out.Cards[0].Y)
	require.Equal(t, geom.Rect{X: 13632, Y: 512, W: 12800, H: 5760}, out.Sections[1])
	require.Equal(t, geom.Rect{X: 13632, Y: 512 + 640, W: 12800, H: 1280}, out.Labels[1])
}

func TestKanbanInterleavedCardsKeepDeclarationOrderPerSection(t *testing.T) {
	in := KanbanInput{
		Sections: []KanbanSection{{LabelHeight: 1280}, {LabelHeight: 1280}},
		Cards:    []KanbanCard{{Section: 1, Height: 640}, {Section: 0, Height: 640}, {Section: 1, Height: 640}},
	}
	out, err := Kanban(in, kanbanVector)
	require.NoError(t, err)
	require.Equal(t, out.Cards[1].Y, out.Cards[0].Y)
	require.Equal(t, out.Cards[0].Y+out.Cards[0].H+320, out.Cards[2].Y)
	require.Greater(t, out.Cards[0].X, out.Cards[1].X)
}

func TestKanbanEmptyDiagramIsAMargin(t *testing.T) {
	out, err := Kanban(KanbanInput{}, kanbanVector)
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 1024, H: 1024}, out.Canvas)
	require.Empty(t, out.Sections)
}

func TestKanbanEmptySectionHasMinimumHeight(t *testing.T) {
	out, err := Kanban(KanbanInput{Sections: []KanbanSection{{LabelHeight: 1280}}}, kanbanVector)
	require.NoError(t, err)
	require.Equal(t, int32(3200), out.Sections[0].H)
	out, err = Kanban(KanbanInput{Sections: []KanbanSection{{LabelHeight: 1}}}, kanbanCell)
	require.NoError(t, err)
	require.Equal(t, int32(5), out.Sections[0].H)
}

func TestKanbanCardsStayInsideTheirSectionAndApart(t *testing.T) {
	in := KanbanInput{Sections: []KanbanSection{{LabelHeight: 1280}}}
	for range 7 {
		in.Cards = append(in.Cards, KanbanCard{Section: 0, Height: 1920})
	}
	for _, p := range []KanbanParams{kanbanVector, kanbanCell} {
		if p.Border > 0 {
			in.Sections[0].LabelHeight = 1
			for i := range in.Cards {
				in.Cards[i].Height = 3
			}
		}
		out, err := Kanban(in, p)
		require.NoError(t, err)
		for i, card := range out.Cards {
			inside, err := geom.Contains(out.Sections[0], card)
			require.NoError(t, err)
			require.True(t, inside)
			if i > 0 {
				apart, err := geom.Intersects(out.Cards[i-1], card)
				require.NoError(t, err)
				require.False(t, apart)
			}
		}
	}
}

func TestKanbanRejectsInvalidInput(t *testing.T) {
	section := []KanbanSection{{LabelHeight: 1}}
	for name, run := range map[string]func() error{
		"section out of range": func() error {
			_, err := Kanban(KanbanInput{Sections: section, Cards: []KanbanCard{{Section: 1, Height: 1}}}, kanbanCell)
			return err
		},
		"negative section": func() error {
			_, err := Kanban(KanbanInput{Sections: section, Cards: []KanbanCard{{Section: -1, Height: 1}}}, kanbanCell)
			return err
		},
		"negative height": func() error {
			_, err := Kanban(KanbanInput{Sections: section, Cards: []KanbanCard{{Section: 0, Height: -1}}}, kanbanCell)
			return err
		},
		"negative label": func() error {
			_, err := Kanban(KanbanInput{Sections: []KanbanSection{{LabelHeight: -1}}}, kanbanCell)
			return err
		},
		"negative parameter": func() error {
			p := kanbanCell
			p.CardGap = -1
			_, err := Kanban(KanbanInput{Sections: section}, p)
			return err
		},
		"card as wide as nothing": func() error {
			p := kanbanCell
			p.SectionWidth = 1
			_, err := Kanban(KanbanInput{Sections: section}, p)
			return err
		},
	} {
		require.ErrorIs(t, run(), geom.ErrDomain, name)
	}
}

func TestKanbanOverflowIsAnError(t *testing.T) {
	in := KanbanInput{Sections: []KanbanSection{{LabelHeight: 1}}, Cards: []KanbanCard{{Section: 0, Height: int32(geom.CoordLimit)}, {Section: 0, Height: int32(geom.CoordLimit)}}}
	_, err := Kanban(in, kanbanVector)
	require.ErrorIs(t, err, geom.ErrOverflow)
	wide := kanbanVector
	wide.SectionWidth = int32(geom.CoordLimit)
	_, err = Kanban(KanbanInput{Sections: []KanbanSection{{}, {}}}, wide)
	require.ErrorIs(t, err, geom.ErrOverflow)
}
