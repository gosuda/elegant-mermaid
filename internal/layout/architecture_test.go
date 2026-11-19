package layout

import (
	"bytes"
	"errors"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const archDemo = `architecture-beta
  group api(cloud)[API]
  service db(database)[Database] in api
  service app(server)[App] in api
  service raw[Raw]
  junction j
  db:R -[reads]- L:app
  app:B --> T:j
  j:R -- L:raw
`

func archDiagram(t *testing.T, src string) *Diagram {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		require.NotEqual(t, diag.SeverityError, diagnostic.Severity, diagnostic.Message)
	}
	return d
}

func archScene(t *testing.T, src string, profile scene.Profile, packs ...string) (scene.Scene, *Diagram, []diag.Diagnostic) {
	t.Helper()
	d := archDiagram(t, src)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := Layout(in)
	require.NoError(t, err)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause)
	var parsed []*icon.Pack
	for _, text := range packs {
		pack, err := icon.Parse([]byte(text))
		require.NoError(t, err)
		parsed = append(parsed, pack)
	}
	return s, d, PlaceIcons(&s, d.IconRefs(), parsed)
}

func TestArchitectureCorpusLaysOutValidly(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "corpus", "architecture", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src := readFile(t, path)
		for _, profile := range blockProfiles {
			archScene(t, src, profile)
		}
	}
}

func TestArchitectureModelDumpShapes(t *testing.T) {
	in, err := archDiagram(t, archDemo+"  align row db app\n").Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	var out bytes.Buffer
	require.NoError(t, WriteModelDump(&out, in))
	dump := out.String()
	for _, want := range []string{
		`"id":"api","role":"group","parent":"","exclusive":false,"direction":"","shape":"group;icon=cloud","text":"API"`,
		`"id":"db","role":"node","parent":"api","exclusive":true,"shape":"service;icon=database;align=0:r:0","text":"Database"`,
		`"id":"app","role":"node","parent":"api","exclusive":true,"shape":"service;icon=server;align=0:r:1","text":"App"`,
		`"id":"raw","role":"node","parent":"","exclusive":true,"shape":"service","text":"Raw"`,
		`"id":"j","role":"node","parent":"","exclusive":true,"shape":"junction"`,
		`"from_side":"R","to_side":"L"`,
		`"id":"e1","from":"app","to":"j","orthogonal":true,"from_side":"B","to_side":"T"`,
	} {
		require.Contains(t, dump, want)
	}
}

func TestArchitectureEdgeMarkersFollowInto(t *testing.T) {
	d := archDiagram(t, "architecture-beta\nservice a(server)\nservice b(server)\nservice c(server)\na:R <--> L:b\nb:R -- L:c\n")
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, "point", in.Routes[0].MarkerStart)
	require.Equal(t, "point", in.Routes[0].MarkerEnd)
	require.Empty(t, in.Routes[1].MarkerStart)
	require.Empty(t, in.Routes[1].MarkerEnd)
	require.Equal(t, geom.SideRight, in.Routes[0].FromSide)
	require.Equal(t, geom.SideLeft, in.Routes[0].ToSide)
}

func TestArchitectureIconTextEscapesShapeSeparators(t *testing.T) {
	d := archDiagram(t, "architecture-beta\nservice a \"x;y=z%\"\n")
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	require.Equal(t, "service;icontext=x%3By%3Dz%25", in.Boxes[0].Shape)
	require.Equal(t, archShapeSpec{Kind: "service", IconText: "x;y=z%"}, parseArchShape(in.Boxes[0].Shape))
	require.Equal(t, "x%3By%3Dz%25", escapeShape("x;y=z%"))
	require.Equal(t, "x;y=z%", unescapeShape("x%3By%3Dz%25"))
}

func TestArchitectureConfigScalesPaddingAndIcons(t *testing.T) {
	base := "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n"
	cfg := "---\nconfig:\n  architecture:\n    padding: 80\n    iconSize: 40\n---\n" + base
	for _, profile := range blockProfiles {
		plain, _, _ := archScene(t, base, profile)
		scaled, _, _ := archScene(t, cfg, profile)
		require.NotEqual(t, plain.Boxes[0].Rect.W, scaled.Boxes[0].Rect.W, profile.String())
	}
	s, _, _ := archScene(t, cfg, scene.ProfileVector)
	require.Equal(t, int32(40*64), s.Boxes[0].Rect.W)
}

func TestArchitectureServicePaintsOutlineIconAndLabel(t *testing.T) {
	s, d, ds := archScene(t, archDemo, scene.ProfileVector)
	require.Empty(t, ds)
	require.NotEmpty(t, d.IconRefs())
	items := nodeGroup(&s, "db").Items
	var kinds []string
	for _, item := range items {
		switch item.(type) {
		case *scene.RoundRect:
			kinds = append(kinds, "outline")
		case *scene.Path, *scene.Polyline, *scene.Ellipse:
			kinds = append(kinds, "icon")
		case *scene.Text:
			kinds = append(kinds, "text")
		}
	}
	require.Equal(t, "outline", kinds[0])
	require.Equal(t, "text", kinds[len(kinds)-1])
	require.Greater(t, len(kinds), 2)
}

func TestArchitectureJunctionPaintsMarker(t *testing.T) {
	vector, _, _ := archScene(t, archDemo, scene.ProfileVector)
	require.IsType(t, &scene.Ellipse{}, nodeGroup(&vector, "j").Items[0])
	cell, _, _ := archScene(t, archDemo, scene.ProfileCell)
	symbol, ok := nodeGroup(&cell, "j").Items[0].(*scene.SymbolRef)
	require.True(t, ok)
	require.Equal(t, "disc", symbol.Symbol)
}

func TestArchitectureGroupBadgeAndServiceIconUseThePipeline(t *testing.T) {
	const pack = `{"prefix":"p","width":16,"height":16,"icons":{"box":{"body":"<path d=\"M0 0h16v16H0z\"/>"}}}`
	src := "architecture-beta\ngroup g(p:box)[G]\nservice a(p:box)[A] in g\nservice b(p:gone)\nservice c(nothing)\n"
	s, _, ds := archScene(t, src, scene.ProfileVector, pack)
	require.Len(t, ds, 2)
	for _, d := range ds {
		require.Equal(t, "icon/pack-missing", d.Code)
	}
	require.Contains(t, ds[0].Message, "p:gone")
	require.Contains(t, ds[1].Message, "nothing")
	groupItems := groupGroup(&s, "g").Items
	var badge *scene.Path
	for _, item := range groupItems {
		if p, ok := item.(*scene.Path); ok {
			badge = p
		}
	}
	require.NotNil(t, badge)
	frame, ok := boxRect(&s, "g")
	require.True(t, ok)
	first := badge.Commands[0].(*scene.MoveTo).P
	require.GreaterOrEqual(t, first.X, frame.X)
	require.GreaterOrEqual(t, first.Y, frame.Y)
	require.Less(t, first.X, frame.X+frame.W)
	outline := nodeGroup(&s, "a").Items[0].(*scene.RoundRect).Rect
	var service *scene.Path
	for _, item := range nodeGroup(&s, "a").Items {
		if p, ok := item.(*scene.Path); ok {
			service = p
		}
	}
	require.NotNil(t, service)
	at := service.Commands[0].(*scene.MoveTo).P
	require.Equal(t, outline.X+outline.W/2-768, at.X)
	require.Equal(t, outline.Y+outline.H/2-768, at.Y)
}

func groupGroup(s *scene.Scene, owner string) *scene.Group {
	for _, g := range s.Groups {
		if g.Role == scene.GroupRoleGroup && g.Owner == owner {
			return g
		}
	}
	return nil
}

func TestArchitectureCellIconsAreSymbols(t *testing.T) {
	s, _, ds := archScene(t, archDemo, scene.ProfileCell)
	require.Empty(t, ds)
	var symbols []string
	for _, item := range nodeGroup(&s, "db").Items {
		if symbol, ok := item.(*scene.SymbolRef); ok {
			symbols = append(symbols, symbol.Symbol)
		}
	}
	require.Equal(t, []string{"database"}, symbols)
}

func TestArchitectureEdgeLabelRecordFollowsTheRoute(t *testing.T) {
	s, _, _ := archScene(t, archDemo, scene.ProfileVector)
	require.Len(t, s.Labels, 1)
	require.Equal(t, "e0.label", s.Labels[0].ID)
	require.Equal(t, "e0", s.Labels[0].Owner)
	require.Equal(t, []string{"reads"}, s.Labels[0].Lines)
	require.Greater(t, s.Labels[0].Rect.W, int32(0))
}

func TestArchitectureLimitsAreEnforced(t *testing.T) {
	d := archDiagram(t, archDemo)
	in, err := d.Input(scene.ProfileVector, scene.Options{Limits: scene.Limits{MaxNodes: 3}})
	require.NoError(t, err)
	_, _, err = Layout(in)
	require.ErrorIs(t, err, layered.ErrTooLarge)
	limit, ok := errors.AsType[*layered.LimitError](err)
	require.True(t, ok)
	require.Equal(t, "nodes", limit.Resource)
	in, err = d.Input(scene.ProfileVector, scene.Options{Limits: scene.Limits{MaxTextBytes: 4}})
	require.NoError(t, err)
	_, _, err = Layout(in)
	limit, ok = errors.AsType[*layered.LimitError](err)
	require.True(t, ok)
	require.Equal(t, "text bytes", limit.Resource)
}

func TestArchitectureChainWithinTheFuelRaisesNoDiagnostic(t *testing.T) {
	var src strings.Builder
	src.WriteString("architecture-beta\n")
	for i := range 6 {
		src.WriteString("service s" + string(rune('a'+i)) + "(server)\n")
	}
	for i := range 5 {
		src.WriteString("s" + string(rune('a'+i)) + ":R -- L:s" + string(rune('a'+i+1)) + "\n")
	}
	d := archDiagram(t, src.String())
	in, err := d.Input(scene.ProfileVector, scene.Options{})
	require.NoError(t, err)
	_, ds, err := Layout(in)
	require.NoError(t, err)
	require.Empty(t, ds)
}

func TestArchitectureAlignmentSharesARow(t *testing.T) {
	src := "architecture-beta\nservice a(server)\nservice b(server)\nservice c(server)\na:R -- L:b\nb:B -- T:c\nalign row a c\n"
	s, _, _ := archScene(t, src, scene.ProfileVector)
	a, _ := boxRect(&s, "a")
	c, _ := boxRect(&s, "c")
	require.Equal(t, a.Y, c.Y)
}

func TestArchitectureGroupModifierKeepsNodeEndpoints(t *testing.T) {
	src := "architecture-beta\ngroup g1(cloud)[G1]\ngroup g2(cloud)[G2]\nservice a(server) in g1\nservice b(server) in g2\na{group}:R -- L:b{group}\n"
	s, _, _ := archScene(t, src, scene.ProfileVector)
	require.Equal(t, "a", s.Routes[0].From)
	require.Equal(t, "b", s.Routes[0].To)
}
