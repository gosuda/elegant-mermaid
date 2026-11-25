package cli

import (
	"errors"
	"fmt"
	"io"
	"os"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/fileerr"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func layoutModel(cfg Config) error {
	o, err := layoutFlags(cfg.Args[1:])
	if err != nil {
		return err
	}
	if o.metrics && o.profile == scene.ProfileCell {
		return errors.New("--metrics needs --profile vector")
	}
	if o.dumped && !o.metrics {
		return errors.New("--dump requires --metrics")
	}
	if o.dumped {
		return writeDumpMetrics(cfg, o.dump)
	}
	return layoutSource(cfg, o)
}

func layoutSource(cfg Config, o layoutOptions) error {
	path := o.path
	profile := o.profile
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
	if err := diag.RenderText(cfg.Stderr, path, f.Source, f.Diagnostics, diag.FrameOptions{}); err != nil {
		return err
	}
	if hasErrors(f.Diagnostics) {
		return &ExitError{Code: 1}
	}
	in, err := m.Input(profile, scene.Options{})
	if err != nil {
		return resultError(cfg, err)
	}
	if o.metrics {
		return writeSourceMetrics(cfg, path, src, in, m)
	}
	return writeLayoutResult(cfg, path, src, in, o.model)
}

func writeLayoutResult(cfg Config, path string, src []byte, in layout.Input, model bool) error {
	if model {
		return layout.WriteModelDump(cfg.Stdout, in)
	}
	s, diagnostics, err := layout.Layout(in)
	if err != nil {
		return resultError(cfg, err)
	}
	if err = diag.RenderText(cfg.Stderr, path, src, diagnostics, diag.FrameOptions{}); err != nil {
		return err
	}
	_, err = cfg.Stdout.Write(s.AppendJSON(nil))
	return err
}

func hasErrors(ds []diag.Diagnostic) bool {
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			return true
		}
	}
	return false
}

func modelSource(cfg Config, path string) ([]byte, error) {
	if path != "-" {
		src, err := os.ReadFile(path)
		if err != nil {
			return nil, fileerr.Read(path, err)
		}
		return src, nil
	}
	input := cfg.Stdin
	if input == nil {
		input = os.Stdin
	}
	if terminalWriter(input) {
		return nil, errors.New("missing INPUT; pass a path or pipe Mermaid source")
	}
	src, err := io.ReadAll(input)
	if err != nil {
		return nil, fileerr.Read(stdinPath, err)
	}
	return src, nil
}

type layoutOptions struct {
	path          string
	profile       scene.Profile
	dump          string
	model         bool
	metrics       bool
	dumped        bool
	positionalSet bool
}

func layoutFlags(args []string) (layoutOptions, error) {
	o := layoutOptions{path: "-", profile: scene.ProfileVector}
	for len(args) > 0 {
		arg := args[0]
		args = args[1:]
		switch {
		case arg == "--":
			return o, o.setPaths(args)
		case isFlagArg(arg):
			var err error
			if args, err = o.setFlag(arg, args); err != nil {
				return o, err
			}
		default:
			if err := o.setPath(arg); err != nil {
				return o, err
			}
		}
	}
	return o, nil
}

func (o *layoutOptions) setPaths(paths []string) error {
	for _, path := range paths {
		if err := o.setPath(path); err != nil {
			return err
		}
	}
	return nil
}

func (o *layoutOptions) setPath(path string) error {
	if o.positionalSet {
		return errors.New("layout accepts one INPUT")
	}
	o.path, o.positionalSet = path, true
	return nil
}

func (o *layoutOptions) setFlag(arg string, rest []string) ([]string, error) {
	token, ok := splitFlag(arg)
	if !ok {
		return nil, unknownFlag(arg, "layout")
	}
	switch token.name {
	case "metrics":
		on, err := token.switchValue()
		o.metrics = on
		return rest, err
	case "profile", "stage", "dump":
		value, rest, err := token.operand(arg, rest)
		if err != nil {
			return nil, err
		}
		return rest, o.setValue(token.name, value)
	}
	return nil, unknownFlag(arg, "layout")
}

func (o *layoutOptions) setValue(name, value string) error {
	switch {
	case name == "dump":
		o.dump, o.dumped = value, true
	case name == "stage" && (value == "model" || value == "layout"):
		o.model = value == "model"
	case name == "profile" && value == "vector":
		o.profile = scene.ProfileVector
	case name == "profile" && value == "cell":
		o.profile = scene.ProfileCell
	case name == "stage":
		return invalidValue(value, "--stage", "model, layout")
	default:
		return invalidValue(value, "--profile", "vector, cell")
	}
	return nil
}

func writeDumpMetrics(cfg Config, path string) error {
	data, err := os.ReadFile(path)
	if err != nil {
		return fileerr.Read(path, err)
	}
	d, err := scene.ReadMetricDump(data)
	if err != nil {
		return fmt.Errorf("%s: %w", path, err)
	}
	m, err := scene.MeasureMetrics(&d, 0)
	if err != nil {
		return resultError(cfg, err)
	}
	_, err = cfg.Stdout.Write(m.AppendJSON(nil))
	return err
}

func writeSourceMetrics(cfg Config, path string, src []byte, in layout.Input, model *layout.Diagram) error {
	s, ds, err := layout.Layout(in)
	if err != nil {
		return resultError(cfg, err)
	}
	if err = diag.RenderText(cfg.Stderr, path, src, ds, diag.FrameOptions{}); err != nil {
		return err
	}
	cell, err := model.Input(scene.ProfileCell, scene.Options{})
	if err != nil {
		return resultError(cfg, err)
	}
	cs, _, err := layout.Layout(cell)
	if err != nil {
		return resultError(cfg, err)
	}
	rendered, err := cells.Render(cs, cells.Options{})
	if err != nil {
		return resultError(cfg, err)
	}
	m, err := scene.MeasureMetrics(&s.Dump, rendered.RefusedClusters)
	if err != nil {
		return resultError(cfg, err)
	}
	m.HardOK = m.HardOK && rendered.RouteConflicts == 0
	_, err = cfg.Stdout.Write(m.AppendJSON(nil))
	return err
}
