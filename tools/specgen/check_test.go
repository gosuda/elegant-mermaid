package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"
)

func writeFile(t *testing.T, path, content string) {
	t.Helper()
	require.NoError(t, os.MkdirAll(filepath.Dir(path), 0o755))
	require.NoError(t, os.WriteFile(path, []byte(content), 0o644))
}

func writeKindsFixture(t *testing.T, root string) {
	t.Helper()
	kinds := []kindInput{{
		ID:       "flowchart",
		Family:   "layered",
		Keywords: []kindKeyword{{Text: "graph", Case: "sensitive"}, {Text: "flowchart", Case: "sensitive"}},
		Aliases:  slices.Clone(upstreamDetectorIDs),
	}}
	data, err := json.Marshal(kinds)
	require.NoError(t, err)
	writeFile(t, filepath.Join(root, "spec", "data", "kinds.json"), string(data))
}

func writeFontFixture(t *testing.T, root string) {
	t.Helper()
	fontRoot := filepath.Join(dataRoot(t), "spec", "data", "fonts")
	for _, name := range []string{"Inter-Regular.ttf", "Inter-SemiBold.ttf"} {
		data, err := os.ReadFile(filepath.Join(fontRoot, name))
		require.NoError(t, err)
		writeFile(t, filepath.Join(root, "spec", "data", "fonts", name), string(data))
	}
}

func TestStrictJSONRejectsDuplicateKeys(t *testing.T) {
	var target map[string]int
	err := unmarshalStrict([]byte(`{"a":1,"a":2}`), &target)
	require.ErrorContains(t, err, "duplicate key")
}

func TestStrictJSONRejectsNestedDuplicateKeys(t *testing.T) {
	var target map[string]any
	err := unmarshalStrict([]byte(`{"outer":{"b":1,"b":2}}`), &target)
	require.ErrorContains(t, err, "duplicate key")
}

func TestStrictJSONRejectsTrailing(t *testing.T) {
	var target map[string]int
	require.Error(t, unmarshalStrict([]byte(`{"a":1} {}`), &target))
}

func TestStrictJSONAcceptsRepeatedKeysInSeparateArrays(t *testing.T) {
	var target struct {
		Items []map[string]int `json:"items"`
	}
	require.NoError(t, unmarshalStrict([]byte(`{"items":[{"k":1},{"k":2}]}`), &target))
	require.Len(t, target.Items, 2)
}

func TestRequirementDuplicateIDsDetected(t *testing.T) {
	seen := make(map[string]string)
	first := checkRequirementLines("detection-01 The header MUST match [just go-check]\n", "spec/detection.md", seen)
	require.Empty(t, first)
	second := checkRequirementLines("detection-01 Another MUST line [just go-check]\n", "spec/other.md", seen)
	require.Len(t, second, 1)
	require.Contains(t, second[0], "requirement ID detection-01 repeats")
}

func TestRequirementAcceptsThreeDigitIDsAndDigitRecipes(t *testing.T) {
	seen := make(map[string]string)
	problems := checkRequirementLines("layered-001 The rank MUST be feasible [just d3-check]\n", "spec/layered.md", seen)
	require.Empty(t, problems)
}

func TestRequirementRejectsUnknownRecipe(t *testing.T) {
	seen := make(map[string]string)
	problems := checkRequirementLines("detection-02 The header MUST match [just not-a-recipe]\n", "spec/detection.md", seen)
	require.Len(t, problems, 1)
	require.Contains(t, problems[0], "unknown recipe")
}

func TestRequirementRejectsLineWithoutID(t *testing.T) {
	seen := make(map[string]string)
	problems := checkRequirementLines("The header MUST match [just go-check]\n", "spec/detection.md", seen)
	require.Len(t, problems, 1)
	require.Contains(t, problems[0], "no ID")
}

func TestCheckDetectsHandEditedGeneratedFile(t *testing.T) {
	root := t.TempDir()
	writeKindsFixture(t, root)
	writeFontFixture(t, root)
	require.NoError(t, generateRoot(root, discard{}))
	require.NoError(t, checkRoot(root, discard{}))

	generated := filepath.Join(root, "internal", "gen", "kinds.go")
	original, err := os.ReadFile(generated)
	require.NoError(t, err)
	require.NoError(t, os.WriteFile(generated, append(original, 'x'), 0o644))

	err = checkRoot(root, discard{})
	require.ErrorContains(t, err, "problem")
	require.NoError(t, os.WriteFile(generated, original, 0o644))
	require.NoError(t, checkRoot(root, discard{}))
}

func TestAbsentInputsGenerateEmptyTables(t *testing.T) {
	root := t.TempDir()
	writeFontFixture(t, root)
	require.NoError(t, generateRoot(root, discard{}))
	for _, name := range []string{"kinds", "markers", "glyphjoin", "seriestext", "strokeok", "entities"} {
		data, err := os.ReadFile(filepath.Join(root, "internal", "gen", name+".go"))
		require.NoError(t, err, name)
		require.Contains(t, string(data), "[]", "%s must hold an empty table", name)
	}
	require.NoError(t, checkRoot(root, discard{}))
}

func TestGenerateIsIdempotent(t *testing.T) {
	root := t.TempDir()
	writeFontFixture(t, root)
	writeFile(t, filepath.Join(root, "spec", "data", "scripts.json"), `[{"base":"U+0031","sup":"U+00B9","sub":"U+2081"}]`)
	require.NoError(t, generateRoot(root, discard{}))
	first, err := os.ReadFile(filepath.Join(root, "internal", "gen", "scripts.go"))
	require.NoError(t, err)
	require.NoError(t, generateRoot(root, discard{}))
	second, err := os.ReadFile(filepath.Join(root, "internal", "gen", "scripts.go"))
	require.NoError(t, err)
	require.Equal(t, string(first), string(second))
}
