package cli

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"syscall"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/fileerr"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"github.com/gosuda/elegant-mermaid/internal/svg"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	themes "github.com/gosuda/elegant-mermaid/internal/theme"
	"github.com/gosuda/elegant-mermaid/raster"
)

type stringList []string

func (l *stringList) String() string { return strings.Join(*l, ",") }

func (l *stringList) Set(value string) error {
	*l = append(*l, value)
	return nil
}

type commandOptions struct {
	input, output, format, theme, background, charset, color, svgText, config string
	artifacts                                                                 string
	artifactsSet                                                              bool
	width, scale                                                              int
	iconPacks                                                                 stringList
	site                                                                      syntax.ConfigValue
	packs                                                                     []*icon.Pack
	outlines                                                                  *scenelink.Outlines
}

func commandFlags(command string, args []string) (commandOptions, []string, error) {
	o := commandOptions{charset: "unicode", color: "auto", svgText: "font", scale: 2}
	fs := flag.NewFlagSet(command, flag.ContinueOnError)
	fs.SetOutput(io.Discard)
	fs.StringVar(&o.color, "color", "auto", "")
	if command == "check" {
		fs.StringVar(&o.format, "output-format", "text", "")
	} else {
		fs.StringVar(&o.input, "i", "", "")
		fs.StringVar(&o.output, "o", "", "")
		fs.Func("a", "", func(value string) error {
			o.artifacts, o.artifactsSet = value, true
			return nil
		})
		fs.StringVar(&o.format, "e", "", "")
		fs.StringVar(&o.theme, "t", "", "")
		fs.StringVar(&o.background, "b", "", "")
		fs.StringVar(&o.charset, "charset", "unicode", "")
		fs.StringVar(&o.svgText, "svg-text", "font", "")
		fs.Func("width", "", func(value string) error {
			return setDecimalInt(&o.width, value, 0, math.MaxInt32)
		})
		fs.Func("s", "", func(value string) error {
			return setDecimalInt(&o.scale, value, 1, 8)
		})
		fs.StringVar(&o.config, "c", "", "")
		fs.Var(&o.iconPacks, "icon-pack", "")
	}
	var positional []string
	for len(args) > 0 {
		a := args[0]
		args = args[1:]
		if a == "--" {
			positional = append(positional, args...)
			break
		}
		if !isFlagArg(a) {
			positional = append(positional, a)
			continue
		}
		token, ok := splitFlag(a)
		if !ok || fs.Lookup(token.name) == nil {
			return o, nil, unknownFlag(a, command)
		}
		name := token.name
		part, rest, err := flagPart(a, args)
		if err != nil {
			return o, nil, err
		}
		args = rest
		if err := fs.Parse(part); err != nil {
			return o, nil, badNumber(name, part)
		}
	}
	return o, positional, nil
}

func setDecimalInt(target *int, value string, minimum, maximum int) error {
	number, err := strconv.ParseInt(value, 10, 32)
	if err != nil {
		return err
	}
	if number < int64(minimum) || number > int64(maximum) {
		return strconv.ErrRange
	}
	*target = int(number)
	return nil
}

func invalidValue(value, name, accepted string) error {
	return fmt.Errorf("invalid value %s for %s; expected one of: %s", value, name, accepted)
}

func badNumber(name string, part []string) error {
	value := part[len(part)-1]
	if len(part) == 1 {
		_, value, _ = strings.Cut(part[0], "=")
	}
	if name == "s" {
		return invalidValue(value, "-s", "1..8")
	}
	return invalidValue(value, "--width", "non-negative integers")
}

func validateChoice(value, name string, choices ...string) error {
	if !slices.Contains(choices, value) {
		return invalidValue(value, name, strings.Join(choices, ", "))
	}
	return nil
}

func parseDiagram(path string, src []byte) (diag.FileDiagnostics, *layout.Diagram) {
	d := layout.ParseDiagram(src)
	f := diag.FileDiagnostics{Path: path, Kind: d.Kind, Source: d.Source, Diagnostics: d.Diagnostics}
	return f, d
}

func parseInput(path string, src []byte) (diag.FileDiagnostics, *layout.Diagram, error) {
	f, d := parseDiagram(path, src)
	if d.Found && !d.Supported() {
		return f, d, errors.New("unsupported diagram kind")
	}
	return f, d, nil
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
	if err = resolveMarkdownOptions(&o, path); err != nil {
		return err
	}
	if err = resolveRenderOptions(&o, cfg); err != nil {
		return err
	}
	if err = loadRenderInputs(&o); err != nil {
		return err
	}
	return renderInput(cfg, o, path)
}

func renderInput(cfg Config, o commandOptions, path string) error {
	src, err := modelSource(cfg, path)
	if err != nil {
		return err
	}
	if markdownHost(path) {
		return renderMarkdown(cfg, o, path, src)
	}
	if path == "-" {
		path = "<stdin>"
	}
	f, m, err := parseInput(path, src)
	if err != nil {
		return err
	}
	effective, err := m.EffectiveConfig(o.site)
	if err != nil {
		return err
	}
	f.Diagnostics = m.DiagnosticsFor(effective)
	if err = rejectInvalidSource(cfg, o, f); err != nil {
		return err
	}
	s, ds, err := layoutDiagram(o, m, effective)
	if err != nil {
		return resultError(cfg, err)
	}
	if err = diag.RenderText(cfg.Stderr, path, src, ds, diag.FrameOptions{}); err != nil {
		return err
	}
	return serializeScene(cfg, o, s, svgOptionsOf(o, m, effective))
}

func rejectInvalidSource(cfg Config, o commandOptions, f diag.FileDiagnostics) error {
	if err := writeDiagnostics(cfg.Stderr, f.Path, f.Source, f.Diagnostics, colourEnabled(o.color, cfg)); err != nil {
		return err
	}
	if hasErrors(f.Diagnostics) {
		return &ExitError{Code: 1}
	}
	return nil
}

func layoutDiagram(o commandOptions, m *layout.Diagram, effective syntax.EffectiveConfig) (scene.Scene, []diag.Diagnostic, error) {
	profile := scene.ProfileVector
	if o.format == "text" {
		profile = scene.ProfileCell
	}
	in, err := m.InputConfigured(profile, scene.Options{MaxWidth: int32(o.width)}, effective)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	in.IconPacks = o.packs
	s, ds, err := layout.Layout(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	ds = append(ds, layout.PlaceIcons(&s, m.IconRefs(), o.packs)...)
	return s, ds, nil
}

func svgOptionsOf(o commandOptions, m *layout.Diagram, effective syntax.EffectiveConfig) svg.Options {
	return svg.Options{Theme: o.theme, Background: o.background, Text: svgTextMode(o.svgText), Outlines: o.outlines, Kind: m.Kind, Title: m.AccTitle, Description: m.AccDescr, Look: layout.SceneLook(effective.Look), FontFamily: effective.FontFamily, Links: m.Links()}
}

func loadRenderInputs(o *commandOptions) error {
	if o.config != "" {
		text, err := readOperand(o.config)
		if err != nil {
			return err
		}
		if o.site, err = layout.ParseSiteConfig(text); err != nil {
			return fmt.Errorf("%s: %w", o.config, err)
		}
	}
	for _, path := range o.iconPacks {
		data, err := readOperand(path)
		if err != nil {
			return err
		}
		pack, err := icon.Parse(data)
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}
		o.packs = append(o.packs, pack)
	}
	if o.svgText == "paths" && o.format == "svg" {
		var err error
		if o.outlines, err = interOutlines(); err != nil {
			return err
		}
	}
	return nil
}

func readOperand(path string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fileerr.Read(path, err)
	}
	return data, nil
}

func serializeScene(cfg Config, o commandOptions, s scene.Scene, svgOptions svg.Options) error {
	data, err := encodeScene(cfg, o, s, svgOptions)
	if errors.Is(err, mermaid.ErrBadConfig) {
		return err
	}
	if err != nil {
		return resultError(cfg, err)
	}
	if o.output != "" {
		if err = atomicOutput(o.output, data); err != nil {
			return fileerr.Write(o.output, err)
		}
		return nil
	}
	_, err = cfg.Stdout.Write(data)
	return err
}

func encodeScene(cfg Config, o commandOptions, s scene.Scene, svgOptions svg.Options) ([]byte, error) {
	switch o.format {
	case "svg":
		var out bytes.Buffer
		err := svg.Write(&out, s, svgOptions)
		return out.Bytes(), err
	case "png":
		return encodePNG(o, s)
	default:
		r, err := cells.Render(s, cells.Options{Charset: renderCharset(o.charset), Color: renderColour(o.color, cfg), Theme: o.theme})
		return r.Text, err
	}
}

func encodePNG(o commandOptions, s scene.Scene) ([]byte, error) {
	wrapped, ok := scenelink.NewScene(s).(*mermaid.Scene)
	if !ok {
		return nil, errors.New("cannot wrap the scene for rasterization")
	}
	pixels, err := raster.RGBA(wrapped, raster.RGBAOptions{Options: raster.Options{Scale: o.scale, Background: o.background}, Theme: o.theme})
	if err != nil {
		return nil, err
	}
	return raster.EncodePNG(pixels)
}

func svgTextMode(s string) svg.TextMode {
	if s == "paths" {
		return svg.TextPaths
	}
	return svg.TextFont
}

func interOutlines() (*scenelink.Outlines, error) {
	fonts, ok := scenelink.OutlinesOf(raster.InterOutlines())
	if !ok {
		return nil, errors.New("cannot load the embedded glyph outlines")
	}
	return &fonts, nil
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
	if err := validateRenderValues(*o); err != nil {
		return err
	}
	if o.format == "png" && o.output == "" && !o.artifactsSet && terminalWriter(cfg.Stdout) {
		return errors.New("cannot write PNG to a terminal; use -o FILE.png or redirect stdout to a file")
	}
	return resolveTheme(o, cfg)
}

func validateRenderValues(o commandOptions) error {
	if err := validateBackground(o.background); err != nil {
		return err
	}
	for _, c := range []struct {
		value, name string
		choices     []string
	}{{o.format, "-e", []string{"svg", "png", "text"}}, {o.charset, "--charset", []string{"unicode", "ascii"}}, {o.color, "--color", []string{"auto", "always", "never"}}, {o.svgText, "--svg-text", []string{"font", "paths"}}} {
		if err := validateChoice(c.value, c.name, c.choices...); err != nil {
			return err
		}
	}
	if o.width < 0 || int64(o.width) > 2147483647 {
		return invalidValue(fmt.Sprint(o.width), "--width", "non-negative integers")
	}
	if o.scale < 1 || o.scale > 8 {
		return invalidValue(fmt.Sprint(o.scale), "-s", "1..8")
	}
	return nil
}

func resolveTheme(o *commandOptions, cfg Config) error {
	if o.theme == "" {
		o.theme = "elegant-light"
		if o.format == "text" && darkBackground(cfg.Terminal.ColorFGBG) {
			o.theme = "elegant-dark"
		}
	}
	return validateChoice(o.theme, "-t", themes.Names()...)
}

func atomicOutput(path string, data []byte) (err error) {
	if info, statErr := os.Lstat(path); statErr == nil && info.IsDir() {
		return syscall.EISDIR
	}
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
