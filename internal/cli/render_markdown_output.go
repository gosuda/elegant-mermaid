package cli

import (
	"bytes"
	"errors"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"

	"github.com/gosuda/elegant-mermaid/internal/fileerr"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
)

type markdownOutput struct {
	path string
	data []byte
}

func writeMarkdownOutputs(input string, raw []byte, blocks []markdown.Block, artifacts []markdownArtifact, o commandOptions) error {
	if err := validateMarkdownOutputPath(o.output, !o.artifactsSet || markdownHost(o.output)); err != nil {
		return err
	}
	paths := markdownArtifactPaths(input, o, len(artifacts))
	outputs := make([]markdownOutput, 0, len(artifacts)+1)
	for i, artifact := range artifacts {
		outputs = append(outputs, markdownOutput{path: paths[i], data: artifact.data})
	}
	if markdownHost(o.output) {
		data, err := rewriteMarkdown(raw, blocks, artifacts, paths, o.output)
		if err != nil {
			return err
		}
		outputs = append(outputs, markdownOutput{path: o.output, data: data})
	}
	return commitMarkdownOutputs(outputs)
}

func validateMarkdownOutputPath(path string, inspect bool) error {
	if path == "" {
		return nil
	}
	if err := validateMarkdownOutputName(path); err != nil {
		return err
	}
	if !inspect {
		return nil
	}
	info, err := os.Lstat(path)
	if err == nil && info.IsDir() {
		return fileerr.Write(path, syscall.EISDIR)
	}
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return fileerr.Write(path, err)
	}
	return nil
}

// The caller has excluded the empty, unspecified output operand.
func validateMarkdownOutputName(path string) error {
	base := filepath.Base(path)
	if base == "." || base == ".." || os.IsPathSeparator(path[len(path)-1]) {
		return fileerr.Write(path, syscall.EISDIR)
	}
	return nil
}

func markdownArtifactPaths(input string, o commandOptions, count int) []string {
	name := o.output
	if name == "" {
		name = input
	}
	stem, ext := markdownStem(filepath.Base(name))
	directory := outputDirectory(o.output)
	if o.output == "" || markdownHost(o.output) {
		ext = "." + markdownFormatExtension(o.format)
	}
	if markdownHost(o.output) {
		directory = joinOutputPath(outputDirectory(o.output), stem+".assets")
	}
	if o.artifactsSet {
		directory = o.artifacts
	}
	paths := make([]string, count)
	for i := range paths {
		paths[i] = joinOutputPath(directory, stem+"-"+strconv.Itoa(i+1)+ext)
	}
	return paths
}

func markdownStem(name string) (string, string) {
	ext := filepath.Ext(name)
	if ext == name {
		return name, ""
	}
	return strings.TrimSuffix(name, ext), ext
}

func markdownFormatExtension(format string) string {
	if format == "text" {
		return "txt"
	}
	return format
}

func commitMarkdownOutputs(outputs []markdownOutput) error {
	for _, output := range outputs {
		if err := os.MkdirAll(outputDirectory(output.path), 0o755); err != nil {
			return fileerr.Write(output.path, err)
		}
	}
	for _, output := range outputs {
		if err := atomicOutput(output.path, output.data); err != nil {
			return fileerr.Write(output.path, err)
		}
	}
	return nil
}

// The scanner's raw spans are replaced in declaration order. All bytes in the
// gaps are copied verbatim, including invalid UTF-8 and mixed line endings.
func rewriteMarkdown(raw []byte, blocks []markdown.Block, artifacts []markdownArtifact, paths []string, output string) ([]byte, error) {
	text := make([]byte, 0, len(raw))
	previous := 0
	for i, block := range blocks {
		link, err := markdownRelativeLink(output, paths[i])
		if err != nil {
			return nil, fileerr.Write(output, err)
		}
		text = append(text, raw[previous:block.Span.Start]...)
		text = append(text, markdownOpenerPrefix(raw, block)...)
		text = append(text, "!["...)
		text = append(text, markdownAltText(artifacts[i].title)...)
		text = append(text, "]("...)
		text = append(text, link...)
		text = append(text, ')')
		text = append(text, markdownBlockEnding(raw, block)...)
		previous = block.Span.End
	}
	return append(text, raw[previous:]...), nil
}

func markdownOpenerPrefix(raw []byte, block markdown.Block) []byte {
	text := raw[block.Span.Start:block.Span.End]
	// A scanner-produced opener has a fence marker, and its container prefix
	// contains none of these bytes.
	return text[:bytes.IndexAny(text, "`~:")]
}

func markdownBlockEnding(raw []byte, block markdown.Block) []byte {
	end := block.Span.End
	if end == block.Span.Start {
		return nil
	}
	switch raw[end-1] {
	case '\r':
		return raw[end-1 : end]
	case '\n':
		start := end - 1
		if start > block.Span.Start && raw[start-1] == '\r' {
			start--
		}
		return raw[start:end]
	default:
		return nil
	}
}

func markdownAltText(title string) string {
	if title == "" {
		return "diagram"
	}
	var text strings.Builder
	for _, b := range []byte(title) {
		switch b {
		case '\r':
			text.WriteString("&#13;")
		case '\n':
			text.WriteString("&#10;")
		default:
			if strings.ContainsRune("!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~", rune(b)) {
				text.WriteByte('\\')
			}
			text.WriteByte(b)
		}
	}
	return text.String()
}

func markdownRelativeLink(host, artifact string) (string, error) {
	directory, err := resolvedOutputDirectory(outputDirectory(host))
	if err != nil {
		return "", err
	}
	parent, err := resolvedOutputDirectory(outputDirectory(artifact))
	if err != nil {
		return "", err
	}
	relative, err := filepath.Rel(directory, filepath.Join(parent, filepath.Base(artifact)))
	if err != nil {
		return "", err
	}
	return markdownLinkPath(filepath.ToSlash(relative)), nil
}

func markdownLinkPath(path string) string {
	const hex = "0123456789ABCDEF"
	var text strings.Builder
	for _, b := range []byte(path) {
		if markdownURLByte(b) {
			text.WriteByte(b)
			continue
		}
		text.WriteByte('%')
		text.WriteByte(hex[b>>4])
		text.WriteByte(hex[b&15])
	}
	return text.String()
}

func markdownURLByte(b byte) bool {
	return b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b >= '0' && b <= '9' || strings.ContainsRune("-._~/", rune(b))
}
