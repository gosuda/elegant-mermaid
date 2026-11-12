package cli

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	model "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/svg"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

type commandOptions struct {
	input, output, format, theme, background, charset, color, svgText string
	width                                                             int
}

func commandFlags(command string, args []string) (commandOptions, []string, error) {
	o := commandOptions{charset: "unicode", color: "auto", svgText: "font"}
	fs := flag.NewFlagSet(command, flag.ContinueOnError)
	fs.SetOutput(io.Discard)
	fs.StringVar(&o.color, "color", "auto", "")
	if command == "check" {
		fs.StringVar(&o.format, "output-format", "text", "")
	} else {
		fs.StringVar(&o.input, "i", "", "")
		fs.StringVar(&o.output, "o", "", "")
		fs.StringVar(&o.format, "e", "", "")
		fs.StringVar(&o.theme, "t", "", "")
		fs.StringVar(&o.background, "b", "", "")
		fs.StringVar(&o.charset, "charset", "unicode", "")
		fs.StringVar(&o.svgText, "svg-text", "font", "")
		fs.IntVar(&o.width, "width", 0, "")
	}
	var positional []string
	for len(args) > 0 {
		a := args[0]
		args = args[1:]
		if a == "--" {
			positional = append(positional, args...)
			break
		}
		if !isModelFlag(a) {
			positional = append(positional, a)
			continue
		}
		name := strings.TrimLeft(strings.SplitN(a, "=", 2)[0], "-")
		if fs.Lookup(name) == nil {
			return o, nil, fmt.Errorf("unknown flag %s; run emd %s --help", a, command)
		}
		part, rest, err := flagPart(a, args)
		if err != nil {
			return o, nil, err
		}
		args = rest
		if err := fs.Parse(part); err != nil {
			return o, nil, invalidValue(part[len(part)-1], "--width", "non-negative integers")
		}
	}
	return o, positional, nil
}
func invalidValue(value, name, accepted string) error {
	return fmt.Errorf("invalid value %s for %s; expected one of: %s", value, name, accepted)
}
func validateChoice(value, name string, choices ...string) error {
	if !slices.Contains(choices, value) {
		return invalidValue(value, name, strings.Join(choices, ", "))
	}
	return nil
}

func parseInput(path string, src []byte) (diag.FileDiagnostics, *model.Model, error) {
	p := syntax.Preprocess(src)
	d := syntax.Detect(src, p.Removed)
	f := diag.FileDiagnostics{Path: path, Kind: d.Kind, Source: src, Diagnostics: append(p.Diags, d.Diagnostics...)}
	if !d.Found {
		return f, nil, nil
	}
	if d.Kind != "flowchart" {
		return f, nil, fmt.Errorf("unsupported diagram kind: %s", d.Kind)
	}
	ast, ds := parser.Parse(src, p.Removed)
	f.Diagnostics = append(f.Diagnostics, ds...)
	m, ds := model.Resolve(src, ast)
	f.Diagnostics = append(f.Diagnostics, ds...)
	diag.Sort(f.Diagnostics)
	return f, m, nil
}

func renderCommand(cfg Config) error {
	o, paths, err := commandFlags("render", cfg.Args[1:])
	if err != nil {
		return err
	}
	if len(paths) > 1 {
		return errors.New("render accepts one INPUT")
	}
	if len(paths) > 0 && o.input != "" {
		return errors.New("pass input either as INPUT or with -i, not both")
	}
	path := o.input
	if len(paths) > 0 {
		path = paths[0]
	}
	if path == "" {
		path = "-"
	}
	if err = resolveRenderOptions(&o, cfg); err != nil {
		return err
	}
	return renderInput(cfg, o, path)
}

func renderInput(cfg Config, o commandOptions, path string) error {
	src, err := modelSource(cfg, path)
	if err != nil {
		return err
	}
	if path == "-" {
		path = "<stdin>"
	}
	f, m, err := parseInput(path, src)
	if err != nil {
		return err
	}
	if err = writeDiagnostics(cfg.Stderr, path, src, f.Diagnostics, colourEnabled(o.color, cfg)); err != nil {
		return err
	}
	if hasErrors(f.Diagnostics) {
		return &ExitError{Code: 1}
	}
	profile := scene.ProfileVector
	if o.format == "text" {
		profile = scene.ProfileCell
	}
	in, _ := layout.FromFlowchart(m, profile, scene.Options{MaxWidth: int32(o.width)})
	s, ds, err := layout.Layout(in)
	if err != nil {
		return resultError(cfg, err)
	}
	if err = diag.RenderText(cfg.Stderr, path, src, ds, diag.FrameOptions{}); err != nil {
		return err
	}
	return serializeScene(cfg, o, s, svg.Options{Theme: o.theme, Background: o.background, Kind: "flowchart", Title: m.AccTitle, Description: m.AccDescr})
}

func serializeScene(cfg Config, o commandOptions, s scene.Scene, svgOptions svg.Options) error {
	var err error
	var out bytes.Buffer
	if o.format == "svg" {
		err = svg.Write(&out, s, svgOptions)
	} else {
		var r cells.Result
		r, err = cells.Render(s, cells.Options{Charset: renderCharset(o.charset), Color: renderColour(o.color, cfg), Theme: o.theme})
		out.Write(r.Text)
	}
	if err != nil {
		return resultError(cfg, err)
	}
	if o.output != "" {
		return atomicOutput(o.output, out.Bytes())
	}
	_, err = cfg.Stdout.Write(out.Bytes())
	return err
}
func resultError(cfg Config, err error) error {
	if _, e := fmt.Fprintln(cfg.Stderr, err); e != nil {
		return e
	}
	return &ExitError{Code: 1}
}
func renderCharset(s string) cells.Charset {
	if s == "ascii" {
		return cells.CharsetASCII
	}
	return cells.CharsetUnicode
}
func resolveRenderOptions(o *commandOptions, cfg Config) error {
	if err := inferFormat(o, cfg); err != nil {
		return err
	}
	if err := validateBackground(o.background); err != nil {
		return err
	}
	for _, c := range []struct {
		value, name string
		choices     []string
	}{{o.format, "-e", []string{"svg", "text"}}, {o.charset, "--charset", []string{"unicode", "ascii"}}, {o.color, "--color", []string{"auto", "always", "never"}}, {o.svgText, "--svg-text", []string{"font"}}} {
		if err := validateChoice(c.value, c.name, c.choices...); err != nil {
			return err
		}
	}
	if o.width < 0 || int64(o.width) > 2147483647 {
		return invalidValue(fmt.Sprint(o.width), "--width", "non-negative integers")
	}
	if o.theme == "" {
		o.theme = "elegant-light"
		if o.format == "text" && darkBackground(os.Getenv("COLORFGBG")) {
			o.theme = "elegant-dark"
		}
	}
	return validateChoice(o.theme, "-t", "elegant-light", "elegant-dark")
}
func atomicOutput(path string, data []byte) (err error) {
	f, err := os.CreateTemp(filepath.Dir(path), ".emd-*")
	if err != nil {
		return err
	}
	defer func() {
		removeErr := os.Remove(f.Name())
		if removeErr != nil && !errors.Is(removeErr, os.ErrNotExist) {
			err = errors.Join(err, removeErr)
		}
	}()
	_, err = f.Write(data)
	closeErr := f.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	return os.Rename(f.Name(), path)
}

func flagPart(a string, args []string) ([]string, []string, error) {
	if strings.Contains(a, "=") {
		return []string{a}, args, nil
	}
	if len(args) == 0 {
		return nil, nil, fmt.Errorf("missing value for %s", a)
	}
	return []string{a, args[0]}, args[1:], nil
}

func inferFormat(o *commandOptions, cfg Config) error {
	if o.format != "" {
		return nil
	}
	o.format = "svg"
	if terminalWriter(cfg.Stdout) {
		o.format = "text"
	}
	if o.output == "" {
		return nil
	}
	switch filepath.Ext(o.output) {
	case ".svg":
		o.format = "svg"
	case ".txt":
		o.format = "text"
	case ".png":
		o.format = "png"
	default:
		return fmt.Errorf("cannot infer the output format from %s; pass -e", o.output)
	}
	return nil
}

func validateBackground(background string) error {
	if background != "" && !regexp.MustCompile(`^#(?:[0-9a-fA-F]{3}|[0-9a-fA-F]{6})$`).MatchString(background) {
		return invalidValue(background, "-b", "#rgb, #rrggbb")
	}
	return nil
}
