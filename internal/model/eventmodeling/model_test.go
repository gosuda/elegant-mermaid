package eventmodeling_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
)

func resolve(t *testing.T, text string) (*model.Model, []diag.Diagnostic) {
	t.Helper()
	prep := syntax.Preprocess([]byte(text))
	document, parsed := parser.Parse([]byte(text), prep.Removed)
	require.Empty(t, parsed)
	return model.Resolve(document)
}

type summary struct {
	Boxes     [][]any    `json:"boxes"`
	Lanes     [][]any    `json:"lanes"`
	Relations [][]string `json:"relations"`
}

func summarize(m *model.Model) summary {
	s := summary{Boxes: [][]any{}, Lanes: [][]any{}, Relations: [][]string{}}
	for _, frame := range m.Frames {
		s.Boxes = append(s.Boxes, []any{frame.Name, frame.Lane})
	}
	for _, lane := range m.Lanes {
		s.Lanes = append(s.Lanes, []any{lane.Index, lane.Label})
	}
	for _, relation := range m.Relations {
		s.Relations = append(s.Relations, []string{m.Frames[relation.Source].Name, m.Frames[relation.Target].Name})
	}
	return s
}

func TestStateMatchesUpstream(t *testing.T) {
	sources, err := filepath.Glob(filepath.Join("..", "..", "..", "spec", "golden", "eventmodeling", "cases", "*.mmd"))
	require.NoError(t, err)
	corpus, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "eventmodeling", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, sources)
	require.NotEmpty(t, corpus)
	for _, path := range sources {
		compareState(t, path, strings.TrimSuffix(path, ".mmd")+".state.json")
	}
	golden := filepath.Join("..", "..", "..", "spec", "golden", "eventmodeling", "corpus")
	for _, path := range corpus {
		compareState(t, path, filepath.Join(golden, strings.TrimSuffix(filepath.Base(path), ".mmd")+".state.json"))
	}
}

func compareState(t *testing.T, sourcePath, goldenPath string) {
	t.Helper()
	text, err := os.ReadFile(sourcePath)
	require.NoError(t, err)
	want, err := os.ReadFile(goldenPath)
	require.NoError(t, err)
	m, ds := resolve(t, string(text))
	require.Empty(t, ds, sourcePath)
	got, err := json.Marshal(summarize(m))
	require.NoError(t, err)
	require.Equal(t, strings.TrimSpace(string(want)), string(got), sourcePath)
}

func TestDuplicateFrameIDsPreserveDeclarations(t *testing.T) {
	text := "eventmodeling\ntf 01 ui A\nrf 01 cmd B\ntf 1 evt C\ntf 01 evt D\n"
	m, ds := resolve(t, text)
	require.Len(t, ds, 2)
	require.Len(t, m.Frames, 4)
	for i, at := range []int{1, 3} {
		require.Equal(t, "eventmodeling/duplicate-frame-id", ds[i].Code)
		require.Equal(t, diag.SeverityError, ds[i].Severity)
		require.Equal(t, m.Frames[at].Span, ds[i].Span)
		require.Equal(t, []diag.Related{{Span: m.Frames[0].Span, Message: "first declared here"}}, ds[i].Related)
	}
	require.Equal(t, []string{"01", "01", "1", "01"}, []string{
		m.Frames[0].Name, m.Frames[1].Name, m.Frames[2].Name, m.Frames[3].Name,
	})
	require.False(t, m.Frames[0].Reset)
	require.True(t, m.Frames[1].Reset)
}

func TestFrameFields(t *testing.T) {
	m, _ := resolve(t, "eventmodeling\nrf 07 readmodel Cart.Items\ntf 08 pcr A.B.C\n")
	first, second := m.Frames[0], m.Frames[1]
	require.True(t, first.Reset)
	require.Equal(t, model.CategoryReadModel, first.Category)
	require.Equal(t, "readmodel", first.Type)
	require.Equal(t, "Items", first.Display)
	require.Equal(t, "Cart", first.Namespace)
	require.False(t, second.Reset)
	require.Equal(t, model.CategoryProcessor, second.Category)
	require.Equal(t, "A.B.C", second.Display)
	require.Empty(t, second.Namespace)
	require.Equal(t, "readmodel", model.CategoryReadModel.String())
}

func TestPayloadMatchesJavaScript(t *testing.T) {
	cases := []struct{ source, want string }{
		{"tf 01 ui A { a: 1 }", " a: 1"},
		{"tf 01 ui A \"text\"", ""},
		{"tf 01 ui A 'x'", ""},
		{"tf 01 ui A {}", ""},
		{"tf 01 ui A {x}", ""},
		{"tf 01 ui A { \"a\": [1,2] }", " \"a\": [1,2]"},
		{"tf 01 ui A {a}}", "a"},
		{"tf 01 ui A {😀}", "\ufffd"},
		{"tf 01 ui A {a😀}", "a\ufffd"},
		{"tf 01 ui A `json` {ab}", "a"},
	}
	for _, c := range cases {
		m, _ := resolve(t, "eventmodeling\n"+c.source+"\n")
		require.True(t, m.Frames[0].HasData, c.source)
		require.Equal(t, c.want, m.Frames[0].Data, c.source)
	}
	typed, _ := resolve(t, "eventmodeling\ntf 01 ui A `json` {ab}\n")
	require.Equal(t, "json", typed.Frames[0].DataType)
}

func TestReferencedPayloadMatchesJavaScript(t *testing.T) {
	cases := []struct{ block, want string }{
		{"{\n a\n b\n}\n", " a\n b\n"},
		{"{\n}\n", "\n"},
		{"{  \n a\n}", "  \n a\n"},
		{"{\n a\n\n}\n", " a\n\n"},
		{"{\n x😀\n}\n", " x😀\n"},
		{"{\r\n a\r\n}\r\n", " a\n"},
		{"{\r a\r}\r", " a\n"},
	}
	for _, c := range cases {
		m, _ := resolve(t, "eventmodeling\ntf 01 ui A [[D]] { inline }\ndata D "+c.block)
		require.True(t, m.Frames[0].HasData, c.block)
		require.Equal(t, c.want, m.Frames[0].Data, c.block)
	}
}

func TestUnresolvedReferenceKeepsInline(t *testing.T) {
	m, _ := resolve(t, "eventmodeling\ntf 01 ui A [[Nope]] { keep }\ntf 02 ui B [[Nope]]\ndata D {\n x\n}\n")
	require.True(t, m.Frames[0].HasData)
	require.Equal(t, " keep", m.Frames[0].Data)
	require.False(t, m.Frames[1].HasData)
}

func TestFirstDataDeclarationWins(t *testing.T) {
	m, _ := resolve(t, "eventmodeling\ntf 01 ui A [[D]]\ndata D {\n first\n}\ndata D {\n second\n}\n")
	require.Equal(t, " first\n", m.Frames[0].Data)
}

func TestEntitiesNotesAndGwtCreateNothing(t *testing.T) {
	m, _ := resolve(t, "eventmodeling\nentity A\nnote 01 {\n hi\n}\ngwt 01 given ui A then evt A\ntf 01 ui A\n")
	require.Len(t, m.Frames, 1)
	require.Empty(t, m.Relations)
}
