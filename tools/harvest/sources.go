package main

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"slices"
	"strings"
)

type sourceFile struct {
	repository string
	group      string
	hostPath   string
	sourcePath string
	validity   string
}

type block struct {
	kind        string
	attribution string
	group       string
	name        string
	content     []byte
}

type fixture struct {
	corpusPath  string
	repository  string
	source      string
	licence     string
	attribution string
	content     []byte
}

type sourceSpec struct {
	repository string
	paths      []string
	suffix     string
	validity   string
}

var fixtureSources = []sourceSpec{
	{repository: "mermaid", paths: []string{"e2e/diagrams"}, suffix: ".mmd"},
	{repository: "mermaid", paths: []string{"packages/mermaid/src/docs/syntax"}, suffix: ".md"},
	{repository: "mermaid-cli", paths: []string{"test-positive"}, suffix: ".mmd"},
	{repository: "mermaid-rs-renderer", paths: []string{
		"tests/fixtures",
		"benches/fixtures",
		"docs/comparison_sources",
	}, suffix: ".mmd"},
	{repository: "mermaid-ascii", paths: []string{
		"cmd/testdata",
		"pkg/graph/testdata",
	}, suffix: ".txt"},
	{repository: "beautiful-mermaid", paths: []string{
		"src/__tests__/testdata",
	}, suffix: ".txt"},
	{repository: "maid", paths: maidPaths, suffix: ".mmd"},
}

var maidPaths = maidFixturePaths()

func maidFixturePaths() []string {
	var paths []string
	for _, kind := range []string{"class", "flowchart", "pie", "sequence", "state"} {
		for _, validity := range []string{"valid", "invalid"} {
			paths = append(paths, path.Join("test-fixtures", kind, validity))
		}
	}
	return paths
}

type harvester struct {
	root        string
	reg         *registry
	sources     []sourceSpec
	licences    map[string]string
	licencePath map[string]string
}

func newHarvester(root string, reg *registry, sources []sourceSpec) *harvester {
	return &harvester{
		root:        root,
		reg:         reg,
		sources:     sources,
		licences:    make(map[string]string, len(sources)),
		licencePath: make(map[string]string, len(sources)),
	}
}

func (h *harvester) hostPath(rel string) string {
	return filepath.Join(h.root, filepath.FromSlash(rel))
}

func (h *harvester) collect() ([]fixture, error) {
	var out []fixture
	for _, spec := range h.sources {
		files, err := h.sourceFiles(spec)
		if err != nil {
			return nil, err
		}
		for _, file := range files {
			produced, err := h.expand(file)
			if err != nil {
				return nil, err
			}
			out = append(out, produced...)
		}
	}
	slices.SortFunc(out, func(a, b fixture) int { return strings.Compare(a.corpusPath, b.corpusPath) })
	for i := 1; i < len(out); i++ {
		if out[i-1].corpusPath == out[i].corpusPath {
			return nil, fmt.Errorf("two fixtures claim %s", out[i].corpusPath)
		}
	}
	return out, nil
}

func (h *harvester) sourceFiles(spec sourceSpec) ([]sourceFile, error) {
	var files []sourceFile
	for _, rel := range spec.paths {
		if err := h.checkSourceRoot(spec.repository, rel); err != nil {
			return nil, err
		}
		root := path.Join(referencesRoot, spec.repository, rel)
		err := filepath.WalkDir(h.hostPath(root), func(name string, entry fs.DirEntry, err error) error {
			if err != nil {
				return fmt.Errorf("walk %s: %w", name, err)
			}
			if entry.IsDir() || !strings.HasSuffix(entry.Name(), spec.suffix) {
				return nil
			}
			file, err := h.describe(spec, name)
			if err != nil {
				return err
			}
			files = append(files, file)
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	slices.SortFunc(files, func(a, b sourceFile) int { return strings.Compare(a.hostPath, b.hostPath) })
	return files, nil
}

func (h *harvester) checkSourceRoot(repository, rel string) error {
	full := h.hostPath(path.Join(referencesRoot, repository, rel))
	info, err := os.Stat(full)
	if err != nil {
		return fmt.Errorf("fixture source %s: %w", full, err)
	}
	if !info.IsDir() {
		return fmt.Errorf("fixture source %s is not a directory", full)
	}
	return nil
}

func (h *harvester) describe(spec sourceSpec, name string) (sourceFile, error) {
	rel, err := filepath.Rel(h.root, name)
	if err != nil {
		return sourceFile{}, fmt.Errorf("locate %s under %s: %w", name, h.root, err)
	}
	hostPath := filepath.ToSlash(rel)
	prefix := path.Join(referencesRoot, spec.repository) + "/"
	sourcePath, ok := strings.CutPrefix(hostPath, prefix)
	if !ok {
		return sourceFile{}, fmt.Errorf("fixture %s lies outside %s", hostPath, prefix)
	}
	validity := spec.validity
	if spec.repository == "maid" {
		validity = maidValidity(sourcePath)
	}
	file := sourceFile{
		repository: spec.repository,
		sourcePath: sourcePath,
		hostPath:   hostPath,
		group:      spec.repository,
		validity:   validity,
	}
	if validity != "" {
		file.group = spec.repository + "/" + validity
	}
	return file, nil
}

func maidValidity(sourcePath string) string {
	for _, validity := range []string{"valid", "invalid"} {
		if slices.Contains(strings.Split(sourcePath, "/"), validity) {
			return validity
		}
	}
	return ""
}

func (h *harvester) expand(file sourceFile) ([]fixture, error) {
	if err := refuseReference(file.hostPath); err != nil {
		return nil, err
	}
	licence, err := h.licence(file.repository)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(h.hostPath(file.hostPath))
	if err != nil {
		return nil, fmt.Errorf("read fixture %s: %w", file.hostPath, err)
	}
	blocks, err := h.blocks(file, data)
	if err != nil {
		return nil, err
	}
	produced := make([]fixture, 0, len(blocks))
	for _, b := range blocks {
		produced = append(produced, fixture{
			corpusPath:  path.Join(b.kind, b.group, b.name),
			repository:  file.repository,
			source:      file.sourcePath,
			licence:     licence,
			attribution: b.attribution,
			content:     b.content,
		})
	}
	return produced, nil
}

func refuseReference(hostPath string) error {
	refused := path.Join(referencesRoot, refusedRoot)
	clean := path.Clean(hostPath)
	if clean == refused || strings.HasPrefix(clean, refused+"/") {
		return fmt.Errorf("refusing source path %q: %s ships no licence", hostPath, refusedRoot)
	}
	return nil
}

func (h *harvester) blocks(file sourceFile, data []byte) ([]block, error) {
	if strings.HasSuffix(file.hostPath, ".md") {
		return h.documentationFences(file, data)
	}
	content := data
	if strings.HasSuffix(file.hostPath, ".txt") {
		content = inputHalf(data)
	}
	name, err := fixtureName(file)
	if err != nil {
		return nil, err
	}
	kind, attribution := h.corpusKind(file, data)
	return []block{{
		kind:        kind,
		attribution: attribution,
		group:       file.group,
		name:        name,
		content:     content,
	}}, nil
}

func (h *harvester) corpusKind(file sourceFile, data []byte) (string, string) {
	if directory, ok := e2eDirectory(file); ok {
		if id, ok := h.reg.kindOfDirectory(directory); ok {
			return id, attributionDirectory
		}
	}
	kind := h.reg.classify(data)
	if kind == outOfScopeKind {
		return kind, attributionOutOfScope
	}
	if kind == unknownKind {
		return kind, attributionUnknown
	}
	return kind, attributionHeader
}

func e2eDirectory(file sourceFile) (string, bool) {
	if file.repository != "mermaid" {
		return "", false
	}
	rest, ok := strings.CutPrefix(file.sourcePath, "e2e/diagrams/")
	if !ok {
		return "", false
	}
	directory, _, _ := strings.Cut(rest, "/")
	return directory, true
}

func (h *harvester) documentationFences(file sourceFile, data []byte) ([]block, error) {
	fences, err := extractFences(data)
	if err != nil {
		return nil, fmt.Errorf("extract fences from %s: %w", file.hostPath, err)
	}
	stem := strings.TrimSuffix(path.Base(file.sourcePath), ".md")
	produced := make([]block, 0, len(fences))
	for i, content := range fences {
		name := fmt.Sprintf("%s%s%04d.mmd", stem, nameSeparator, i+1)
		if err := checkName(name); err != nil {
			return nil, err
		}
		kind, attribution := h.corpusKind(file, content)
		produced = append(produced, block{
			kind:        kind,
			attribution: attribution,
			group:       file.group,
			name:        name,
			content:     content,
		})
	}
	return produced, nil
}

func fixtureName(file sourceFile) (string, error) {
	rel := file.sourcePath
	if file.repository == "maid" {
		rel = path.Base(file.sourcePath)
	} else if rest, ok := strings.CutPrefix(file.sourcePath, "e2e/diagrams/"); ok {
		rel = rest
	}
	name := strings.TrimSuffix(strings.ReplaceAll(rel, "/", nameSeparator), path.Ext(rel)) + ".mmd"
	if err := checkName(name); err != nil {
		return "", err
	}
	return name, nil
}

func checkName(name string) error {
	if name == "" || name == "." || name == ".." {
		return fmt.Errorf("fixture name %q is not usable", name)
	}
	for i := 0; i < len(name); i++ {
		c := name[i]
		switch {
		case c >= '0' && c <= '9', c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z':
		case c == '.', c == '_', c == '-', c == '~':
		default:
			return fmt.Errorf("fixture name %q holds byte %q", name, c)
		}
	}
	return nil
}

type fence struct {
	character byte
	length    int
	accept    bool
	content   [][]byte
}

func extractFences(src []byte) ([][]byte, error) {
	var (
		fences [][]byte
		open   *fence
	)
	for _, line := range lineOffsets(src) {
		trimmed := trimSpaceTab(line.content(src))
		if open == nil {
			if next, ok := fenceOpener(trimmed); ok {
				open = &next
			}
			continue
		}
		if isFenceCloser(trimmed, *open) {
			if open.accept {
				fences = append(fences, joinLines(open.content))
			}
			open = nil
			continue
		}
		open.content = append(open.content, slices.Clone(line.raw(src)))
	}
	if open != nil {
		return nil, errors.New("documentation fence is not closed")
	}
	return fences, nil
}

func joinLines(lines [][]byte) []byte {
	size := 0
	for _, line := range lines {
		size += len(line) + 1
	}
	out := make([]byte, 0, size)
	for _, line := range lines {
		out = append(out, line...)
		out = append(out, '\n')
	}
	return out
}

func fenceOpener(line []byte) (fence, bool) {
	character, length := fenceRun(line)
	if length < 3 {
		return fence{}, false
	}
	info := strings.TrimSpace(string(line[length:]))
	if info == "" {
		return fence{character: character, length: length}, true
	}
	word, _, _ := strings.Cut(info, " ")
	accept := word == "mermaid" || word == "mermaid-example"
	return fence{character: character, length: length, accept: accept}, true
}

func isFenceCloser(line []byte, open fence) bool {
	character, length := fenceRun(line)
	if character != open.character || length < open.length {
		return false
	}
	return strings.TrimSpace(string(line[length:])) == ""
}

func fenceRun(line []byte) (byte, int) {
	for _, character := range []byte{'`', '~'} {
		count := 0
		for count < len(line) && line[count] == character {
			count++
		}
		if count > 0 {
			return character, count
		}
	}
	return 0, 0
}

func (h *harvester) licence(repository string) (string, error) {
	if spdx, ok := h.licences[repository]; ok {
		return spdx, nil
	}
	rel, data, err := h.licenceFile(repository)
	if err != nil {
		return "", err
	}
	spdx, err := spdxOf(data)
	if err != nil {
		return "", fmt.Errorf("licence %s: %w", rel, err)
	}
	h.licences[repository] = spdx
	h.licencePath[repository] = rel
	return spdx, nil
}

func (h *harvester) licenceFile(repository string) (string, []byte, error) {
	directory := path.Join(referencesRoot, repository)
	for _, name := range []string{"LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"} {
		rel := path.Join(directory, name)
		data, err := os.ReadFile(h.hostPath(rel))
		if err != nil {
			continue
		}
		return rel, data, nil
	}
	return "", nil, fmt.Errorf("repository %q holds no licence file", repository)
}

func spdxOf(data []byte) (string, error) {
	head := asciiLower(string(data))
	if len(head) > 4096 {
		head = head[:4096]
	}
	for _, candidate := range []struct {
		spdx   string
		needle string
	}{
		{spdx: "ISC", needle: "isc license"},
		{spdx: "MIT", needle: "mit license"},
		{spdx: "Apache-2.0", needle: "apache license"},
	} {
		if strings.Contains(head, candidate.needle) {
			return candidate.spdx, nil
		}
	}
	return "", errors.New("licence text names no licence this tool recognises")
}

func digest(content []byte) string {
	sum := sha256.Sum256(content)
	return hex.EncodeToString(sum[:])
}
