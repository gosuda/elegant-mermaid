package main

import (
	"bytes"
	"os"
	"path"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestHeaderTokenSkipsFrontmatterAndDirectives(t *testing.T) {
	for name, tc := range map[string]struct {
		source string
		want   string
	}{
		"plain": {
			source: "flowchart TD\n  A --> B\n",
			want:   "flowchart",
		},
		"leading blank and space": {
			source: "\n\n  \t flowchart LR\n",
			want:   "flowchart",
		},
		"frontmatter": {
			source: "---\ntitle: demo\nconfig:\n  theme: forest\n---\ngraph TD\n",
			want:   "graph",
		},
		"frontmatter then directive": {
			source: "---\ntheme: forest\n---\n%%{init: {'theme':'dark'}}%%\nsequenceDiagram\n",
			want:   "sequenceDiagram",
		},
		"multiline directive": {
			source: "%%{init: { 'theme': 'default' ,\n  'gitGraph': { 'rotateCommitLabel': false }\n} }%%\ngitGraph BT:\n",
			want:   "gitGraph",
		},
		"comment lines": {
			source: "%% a comment\n%%\n%% another\nclassDiagram\n",
			want:   "classDiagram",
		},
		"crlf frontmatter": {
			source: "---\r\ntheme: forest\r\n---\r\nerDiagram\r\n",
			want:   "erDiagram",
		},
		"crlf directive": {
			source: "%%{init: {'theme':'dark'}}%%\r\nstateDiagram-v2\r\n",
			want:   "stateDiagram-v2",
		},
		"no header": {
			source: "---\ntheme: forest\n---\n\n%% only comments\n",
			want:   "",
		},
		"empty source": {
			source: "",
			want:   "",
		},
		"header token stops at space": {
			source: "gitGraph BT:\n  commit id: \"Alpha\"\n",
			want:   "gitGraph",
		},
		"header token keeps hyphen and underscore": {
			source: "railroad-ebnf-beta\n",
			want:   "railroad-ebnf-beta",
		},
	} {
		t.Run(name, func(t *testing.T) {
			require.Equal(t, tc.want, headerToken([]byte(tc.source)))
		})
	}
}

func TestRegistryClassifiesKeywords(t *testing.T) {
	root := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(root, "spec", "data"), 0o755))
	require.NoError(t, os.WriteFile(
		filepath.Join(root, filepath.FromSlash(kindRegistryPath)),
		[]byte(`[
  {"id":"flowchart","keywords":[{"text":"graph","case":"sensitive"},{"text":"flowchart","case":"sensitive"}],"aliases":["flowchart-v2"]},
  {"id":"ishikawa","keywords":[{"text":"ishikawa","case":"insensitive"}],"aliases":[]},
  {"id":"railroad","keywords":[{"text":"railroad-ebnf-beta","case":"insensitive"}],"aliases":["railroadEbnf"]}
]`),
		0o644,
	))
	reg, err := loadRegistry(filepath.Join(root, filepath.FromSlash(kindRegistryPath)))
	require.NoError(t, err)

	require.Equal(t, "flowchart", reg.classify([]byte("graph TD\n")))
	require.Equal(t, "ishikawa", reg.classify([]byte("ISHIKAWA\n")))
	require.Equal(t, "railroad", reg.classify([]byte("Railroad-Ebnf-Beta\n")))
	require.Equal(t, unknownKind, reg.classify([]byte("flowcharter TD\n")))
	require.Equal(t, outOfScopeKind, reg.classify([]byte("zenuml\n")))
	require.Equal(t, unknownKind, reg.classify(nil))
}

func TestRegistryMapsDirectoryNames(t *testing.T) {
	root := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(root, "spec", "data"), 0o755))
	require.NoError(t, os.WriteFile(
		filepath.Join(root, filepath.FromSlash(kindRegistryPath)),
		[]byte(`[
  {"id":"class","keywords":[],"aliases":["classDiagram"]},
  {"id":"er","keywords":[{"text":"erDiagram","case":"sensitive"}],"aliases":["er"]},
  {"id":"gitgraph","keywords":[{"text":"gitGraph","case":"sensitive"}],"aliases":["gitGraph"]},
  {"id":"swimlane","keywords":[{"text":"swimlane-beta","case":"sensitive"}],"aliases":["swimlane"]},
  {"id":"treeview","keywords":[{"text":"treeView-beta","case":"sensitive"}],"aliases":["treeView"]}
]`),
		0o644,
	))
	reg, err := loadRegistry(filepath.Join(root, filepath.FromSlash(kindRegistryPath)))
	require.NoError(t, err)

	require.Equal(t, "class", directoryKind(t, reg, "class-diagram"))
	require.Equal(t, "er", directoryKind(t, reg, "er-diagram"))
	require.Equal(t, "gitgraph", directoryKind(t, reg, "git"))
	require.Equal(t, "swimlane", directoryKind(t, reg, "swimlanes"))
	require.Equal(t, "treeview", directoryKind(t, reg, "tree-view"))
	require.Equal(t, "class", directoryKind(t, reg, "classDiagram"))
}

func directoryKind(t *testing.T, reg *registry, directory string) string {
	t.Helper()
	kind, ok := reg.kindOfDirectory(directory)
	require.Truef(t, ok, "directory %q resolved to no kind", directory)
	return kind
}

func TestExtractFences(t *testing.T) {
	source := strings.Join([]string{
		"# Title",
		"",
		"```mermaid",
		"flowchart LR",
		"  A --> B",
		"```",
		"",
		"```mermaid-example",
		"sequenceDiagram",
		"  A->>B: hi",
		"```",
		"",
		"```javascript",
		"const x = 1;",
		"```",
		"",
		"~~~~mermaid",
		"pie",
		`  "Dogs": 4`,
		"~~~~",
		"",
		"```",
		"no info string",
		"```",
		"",
	}, "\n")

	fences, err := extractFences([]byte(source))
	require.NoError(t, err)
	require.Len(t, fences, 3)
	require.Equal(t, "flowchart LR\n  A --> B\n", string(fences[0]))
	require.Equal(t, "sequenceDiagram\n  A->>B: hi\n", string(fences[1]))
	require.Equal(t, "pie\n  \"Dogs\": 4\n", string(fences[2]))
}

func TestExtractFencesKeepsIndentedContentAndCRLF(t *testing.T) {
	source := "```mermaid\r\n  flowchart LR\r\n    A --> B\r\n```\r\n"
	fences, err := extractFences([]byte(source))
	require.NoError(t, err)
	require.Len(t, fences, 1)
	require.Equal(t, "  flowchart LR\r\n    A --> B\r\n", string(fences[0]))
}

func TestExtractFencesRequiresClosingFence(t *testing.T) {
	_, err := extractFences([]byte("```mermaid\nflowchart LR\n"))
	require.Error(t, err)
}

func TestExtractFencesRejectsShorterCloser(t *testing.T) {
	fences, err := extractFences([]byte("````mermaid\nflowchart LR\n```\n````\n"))
	require.NoError(t, err)
	require.Equal(t, "flowchart LR\n```\n", string(fences[0]))
}

func TestInputHalfSplitsAtSeparator(t *testing.T) {
	for name, tc := range map[string]struct {
		source string
		want   string
	}{
		"separator after source": {
			source: "graph LR\nA --> B\n---\n+---+ +---+\n",
			want:   "graph LR\nA --> B\n",
		},
		"crlf separator": {
			source: "graph LR\r\nA --> B\r\n---\r\n+---+\r\n",
			want:   "graph LR\r\nA --> B\r\n",
		},
		"config prefix before separator": {
			source: "maxWidth = 5\ngraph LR\nA --> B\n---\n+---+\n",
			want:   "maxWidth = 5\ngraph LR\nA --> B\n",
		},
		"no separator": {
			source: "graph LR\nA --> B\n",
			want:   "graph LR\nA --> B\n",
		},
		"separator first": {
			source: "---\n+---+\n",
			want:   "",
		},
	} {
		t.Run(name, func(t *testing.T) {
			require.Equal(t, tc.want, string(inputHalf([]byte(tc.source))))
		})
	}
}
func TestHarvestRefusesMermaidLinterBeforeWriting(t *testing.T) {
	root := fixtureTree(t)
	planted := filepath.Join(root, filepath.FromSlash(".references/mermaid-linter/docs/semantic-rules.md"))
	require.NoError(t, os.MkdirAll(filepath.Dir(planted), 0o755))
	require.NoError(t, os.WriteFile(planted, []byte("```mermaid\nflowchart LR\n```\n"), 0o644))

	spec := sourceSpec{repository: "mermaid-linter", paths: []string{"docs"}, suffix: ".md"}
	sources := append(slices.Clone(fixtureSources), spec)
	_, err := executeSources([]string{"-root", root}, sources)
	require.ErrorContains(t, err, "mermaid-linter")
	require.NoDirExists(t, filepath.Join(root, "corpus"))
}

func TestFixtureNameIsDerivedFromSourcePath(t *testing.T) {
	for name, tc := range map[string]struct {
		file sourceFile
		want string
	}{
		"e2e": {
			file: sourceFile{
				repository: "mermaid",
				sourcePath: "e2e/diagrams/flowchart/pr-check/1-shapes-layout-default.mmd",
			},
			want: "flowchart~pr-check~1-shapes-layout-default.mmd",
		},
		"maid keeps only the base name": {
			file: sourceFile{
				repository: "maid",
				sourcePath: "test-fixtures/flowchart/invalid/no-diagram-type.mmd",
			},
			want: "no-diagram-type.mmd",
		},
		"txt becomes mmd": {
			file: sourceFile{
				repository: "mermaid-ascii",
				sourcePath: "cmd/testdata/er-ascii/classic_order_example.txt",
			},
			want: "cmd~testdata~er-ascii~classic_order_example.mmd",
		},
	} {
		t.Run(name, func(t *testing.T) {
			got, err := fixtureName(tc.file)
			require.NoError(t, err)
			require.Equal(t, tc.want, got)
		})
	}
}

func TestRefuseReferenceRepositories(t *testing.T) {
	for _, hostPath := range []string{
		".references/mermaid-linter/LICENSE",
		".references/mermaid-linter/docs/semantic-rules.md",
		".references/mermaid-linter",
	} {
		require.Errorf(t, refuseReference(hostPath), "path %q was not refused", hostPath)
	}
	for _, hostPath := range []string{
		".references/mermaid/LICENSE",
		".references/mermaid-linter-copy/x.mmd",
		"corpus/flowchart/mermaid/x.mmd",
	} {
		require.NoErrorf(t, refuseReference(hostPath), "path %q was refused", hostPath)
	}
}

func TestSPDXOfLicenceText(t *testing.T) {
	for name, tc := range map[string]struct {
		text string
		want string
	}{
		"mit":     {text: "The MIT License (MIT)\n\nCopyright (c) 2014\n", want: "MIT"},
		"isc":     {text: "ISC License\n\nCopyright (c) 2025 Probelabs\n", want: "ISC"},
		"apache2": {text: "\n                                 Apache License\n", want: "Apache-2.0"},
	} {
		t.Run(name, func(t *testing.T) {
			spdx, err := spdxOf([]byte(tc.text))
			require.NoError(t, err)
			require.Equal(t, tc.want, spdx)
		})
	}
	_, err := spdxOf([]byte("All rights reserved\n"))
	require.Error(t, err)
}

func TestHarvestFixtureTreeIsIdempotent(t *testing.T) {
	root := fixtureTree(t)
	first, err := execute([]string{"-root", root})
	require.NoError(t, err)
	require.Contains(t, first, "copied 3 fixtures")

	before := snapshotTree(t, root)
	second, err := execute([]string{"-root", root})
	require.NoError(t, err)
	require.Equal(t, first, second)
	require.Equal(t, before, snapshotTree(t, root))
}

func TestHarvestRemovesStaleFixture(t *testing.T) {
	root := fixtureTree(t)
	_, err := execute([]string{"-root", root})
	require.NoError(t, err)

	stale := filepath.Join(root, "corpus", "flowchart", "maid", "valid", "stale.mmd")
	require.NoError(t, os.WriteFile(stale, []byte("flowchart LR\n"), 0o644))
	_, err = execute([]string{"-root", root})
	require.NoError(t, err)
	require.NoFileExists(t, stale)
}

func TestHarvestFilesByHeaderAndSeparator(t *testing.T) {
	root := fixtureTree(t)
	_, err := execute([]string{"-root", root})
	require.NoError(t, err)

	asciiPath := filepath.Join(root, "corpus", unknownKind, "mermaid-ascii", "cmd~testdata~padded.mmd")
	content, err := os.ReadFile(asciiPath)
	require.NoError(t, err)
	require.Equal(t, "paddingX=2\ngraph LR\nA --> B\n", string(content))

	manifest, err := os.ReadFile(filepath.Join(root, "corpus", manifestName))
	require.NoError(t, err)
	require.Equal(t, 3, bytes.Count(manifest, []byte(`"path"`)))
	require.True(t, bytes.HasSuffix(manifest, []byte("]\n")))
	require.True(t, advertisedOrder(t, manifest))

	divergences, err := os.ReadFile(filepath.Join(root, "corpus", divergenceName))
	require.NoError(t, err)
	require.Equal(t, "[]\n", string(divergences))
}

func advertisedOrder(t *testing.T, manifest []byte) bool {
	t.Helper()
	var paths []string
	for line := range strings.SplitSeq(string(manifest), "\n") {
		rest, ok := strings.CutPrefix(strings.TrimSpace(line), `"path": "`)
		if !ok {
			continue
		}
		value, _, _ := strings.Cut(rest, `"`)
		paths = append(paths, value)
	}
	return slices.IsSorted(paths)
}

func fixtureTree(t *testing.T) string {
	t.Helper()
	root := t.TempDir()
	write := func(rel, content string) {
		full := filepath.Join(root, filepath.FromSlash(rel))
		require.NoError(t, os.MkdirAll(filepath.Dir(full), 0o755))
		require.NoError(t, os.WriteFile(full, []byte(content), 0o644))
	}
	for _, spec := range fixtureSources {
		for _, rel := range spec.paths {
			sourceRoot := path.Join(referencesRoot, spec.repository, rel)
			require.NoError(t, os.MkdirAll(filepath.Join(root, filepath.FromSlash(sourceRoot)), 0o755))
		}
	}
	write(kindRegistryPath, `[
  {"id":"flowchart","keywords":[{"text":"graph","case":"sensitive"},{"text":"flowchart","case":"sensitive"}],"aliases":["flowchart-v2"]},
  {"id":"sequence","keywords":[{"text":"sequenceDiagram","case":"sensitive"}],"aliases":["sequence"]}
]`)
	write(".references/maid/LICENSE", "ISC License\n\nCopyright (c) 2025 Probelabs\n")
	write(".references/maid/test-fixtures/flowchart/valid/one.mmd", "flowchart LR\n  A --> B\n")
	write(".references/mermaid/LICENSE", "The MIT License (MIT)\n\nCopyright (c) 2014\n")
	write(".references/mermaid/e2e/diagrams/sequence/pr-check/two.mmd", "sequenceDiagram\n  A->>B: hi\n")
	write(".references/mermaid-ascii/LICENSE", "MIT License\n\nCopyright (c) 2023 Alexander Grooff\n")
	write(".references/mermaid-ascii/cmd/testdata/padded.txt", "paddingX=2\ngraph LR\nA --> B\n---\n+---+  +---+\n")
	return root
}

func snapshotTree(t *testing.T, root string) map[string]string {
	t.Helper()
	snapshot := map[string]string{}
	require.NoError(t, filepath.WalkDir(root, func(name string, entry os.DirEntry, err error) error {
		require.NoError(t, err)
		if entry.IsDir() {
			return nil
		}
		content, readErr := os.ReadFile(name)
		require.NoError(t, readErr)
		rel, relErr := filepath.Rel(root, name)
		require.NoError(t, relErr)
		snapshot[filepath.ToSlash(rel)] = digest(content)
		return nil
	}))
	return snapshot
}
