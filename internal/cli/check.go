package cli

import (
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func terminalWriter(v any) bool {
	f, ok := v.(*os.File)
	if !ok {
		return false
	}
	s, err := f.Stat()
	return err == nil && s.Mode()&os.ModeCharDevice != 0
}
func ColourEnabled(mode string, terminal bool, getenv func(string) string) bool {
	if mode != "auto" {
		return mode == "always"
	}
	if getenv("NO_COLOR") != "" {
		return false
	}
	force := getenv("FORCE_COLOR")
	if getenv("CLICOLOR_FORCE") == "1" || (force != "" && force != "0") {
		return true
	}
	if getenv("CLICOLOR") == "0" || getenv("TERM") == "dumb" {
		return false
	}
	return terminal
}
func colourEnabled(mode string, cfg Config) bool {
	return ColourEnabled(mode, terminalWriter(cfg.Stdout), os.Getenv)
}
func renderColour(mode string, cfg Config) cells.ColorMode {
	if !colourEnabled(mode, cfg) {
		return cells.ColorNone
	}
	if slices.Contains([]string{"truecolor", "24bit"}, os.Getenv("COLORTERM")) {
		return cells.ColorTruecolor
	}
	if strings.HasSuffix(os.Getenv("TERM"), "256color") {
		return cells.ColorANSI256
	}
	return cells.ColorANSI16
}
func darkBackground(value string) bool {
	parts := strings.Split(value, ";")
	if len(parts) < 2 {
		return false
	}
	for _, p := range parts {
		if _, err := strconv.ParseUint(p, 10, 8); err != nil {
			return false
		}
	}
	n, _ := strconv.Atoi(parts[len(parts)-1])
	return n <= 6 || n == 8
}
func writeDiagnostics(w io.Writer, path string, src []byte, ds []diag.Diagnostic, color bool) error {
	if color {
		return diag.RenderTextColour(w, path, src, ds, diag.FrameOptions{})
	}
	return diag.RenderText(w, path, src, ds, diag.FrameOptions{})
}
func checkCommand(cfg Config) error {
	o, paths, err := commandFlags("check", cfg.Args[1:])
	if err != nil {
		return err
	}
	if err = validateChoice(o.format, "--output-format", "text", "json"); err != nil {
		return err
	}
	if err = validateChoice(o.color, "--color", "auto", "always", "never"); err != nil {
		return err
	}
	inputs, err := collectCheckPaths(paths)
	if err != nil {
		return err
	}
	if len(inputs) == 0 {
		_, err = fmt.Fprintln(cfg.Stderr, "no Mermaid files found in .")
		return err
	}
	return checkInputs(cfg, o, inputs)
}

func checkInputs(cfg Config, o commandOptions, inputs []string) error {
	var err error
	var files []diag.FileDiagnostics
	failed := false
	for _, path := range inputs {
		src, e := modelSource(cfg, path)
		if e != nil {
			return e
		}
		if path == "-" {
			path = "<stdin>"
		}
		f, e := checkInput(path, src)
		if e != nil {
			return e
		}
		files = append(files, f)
		failed = failed || hasErrors(f.Diagnostics)
	}
	if o.format == "json" {
		_, err = cfg.Stdout.Write(diag.AppendDocument(nil, files))
	} else {
		err = writeCheckText(cfg, files, o.color)
	}
	if err != nil {
		return err
	}
	if failed {
		return &ExitError{Code: 1}
	}
	return nil
}

func markdownHost(path string) bool {
	return slices.Contains([]string{".md", ".markdown", ".mdx"}, filepath.Ext(path))
}

func checkInput(path string, src []byte) (diag.FileDiagnostics, error) {
	if !markdownHost(path) {
		f, _, err := parseInput(path, src)
		return f, err
	}
	src, firstBad := source.RepairUTF8(src)
	host := diag.FileDiagnostics{Path: path, Source: src}
	if firstBad >= 0 {
		host.Diagnostics = append(host.Diagnostics, diag.Diagnostic{
			Code: "source/invalid-utf8", Severity: diag.SeverityError,
			Message: "invalid UTF-8 at byte " + strconv.Itoa(firstBad),
			Span:    source.Span{Start: firstBad, End: firstBad + len("\uFFFD")},
			Help:    "Save the source as UTF-8.",
		})
	}
	for _, block := range markdown.Blocks(src) {
		f, _, err := parseInput(path, block.Source)
		if err != nil {
			return host, err
		}
		for _, d := range f.Diagnostics {
			host.Diagnostics = append(host.Diagnostics, hostDiagnostic(block, d))
		}
	}
	diag.Sort(host.Diagnostics)
	return host, nil
}

func hostDiagnostic(block markdown.Block, d diag.Diagnostic) diag.Diagnostic {
	d.Span = hostSpan(block, d.Span)
	for i := range d.Related {
		d.Related[i].Span = hostSpan(block, d.Related[i].Span)
	}
	for i := range d.Fixes {
		for j := range d.Fixes[i].Edits {
			edit := &d.Fixes[i].Edits[j]
			edit.Span = hostSpan(block, edit.Span)
		}
	}
	return d
}

func hostSpan(block markdown.Block, span source.Span) source.Span {
	return source.Span{Start: block.HostOffset(span.Start), End: block.HostOffset(span.End)}
}
func writeCheckText(cfg Config, files []diag.FileDiagnostics, color string) error {
	for _, f := range files {
		if err := writeDiagnostics(cfg.Stdout, f.Path, f.Source, f.Diagnostics, colourEnabled(color, cfg)); err != nil {
			return err
		}
	}
	return nil
}
func checkPaths(path string) ([]string, error) {
	if path == "-" {
		return []string{path}, nil
	}
	var paths []string
	err := filepath.WalkDir(path, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return fmt.Errorf("cannot read %s: %w", p, err)
		}
		if d.Type()&os.ModeSymlink != 0 {
			return nil
		}
		if d.IsDir() {
			if p != path && (strings.HasPrefix(d.Name(), ".") || d.Name() == "node_modules" || d.Name() == "target") {
				return filepath.SkipDir
			}
			return nil
		}
		if slices.Contains([]string{".mmd", ".mermaid", ".md", ".markdown", ".mdx"}, filepath.Ext(p)) {
			paths = append(paths, p)
		}
		return nil
	})
	return paths, err
}

func collectCheckPaths(paths []string) ([]string, error) {
	implicit := len(paths) == 0
	if implicit {
		paths = []string{"."}
	}
	var inputs []string
	for _, path := range paths {
		found, err := checkPaths(path)
		if err != nil {
			return nil, err
		}
		if len(found) == 0 && !implicit {
			return nil, fmt.Errorf("no Mermaid files found in %s", path)
		}
		inputs = append(inputs, found...)
	}
	slices.Sort(inputs)
	return inputs, nil
}
