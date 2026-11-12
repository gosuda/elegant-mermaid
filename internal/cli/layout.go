package cli

import (
	"errors"
	"fmt"
	"io"
	"os"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func layoutModel(cfg Config) error {
	metrics, dump, args, err := metricArgs(cfg.Args)
	if err != nil {
		return err
	}
	cfg.Args = args
	parseArgs := args[1:]
	path, profile, err := modelArgs(parseArgs)
	if err != nil {
		return err
	}
	if metrics && profile == scene.ProfileCell {
		return errors.New("--metrics needs --profile vector")
	}
	if dump != "" {
		return writeDumpMetrics(cfg, dump)
	}
	return layoutSource(cfg, path, profile, metrics)
}

func layoutSource(cfg Config, path string, profile scene.Profile, metrics bool) error {
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
	if hasErrors(f.Diagnostics) {
		if err := diag.RenderText(cfg.Stderr, path, f.Source, f.Diagnostics, diag.FrameOptions{}); err != nil {
			return err
		}
		return &ExitError{Code: 1}
	}
	in, err := m.Input(profile, scene.Options{})
	if err != nil {
		return err
	}
	if metrics {
		return writeSourceMetrics(cfg, path, src, in, m)
	}
	return writeLayoutResult(cfg, path, src, in)
}

func writeLayoutResult(cfg Config, path string, src []byte, in layout.Input) error {
	if modelStage(cfg.Args[1:]) {
		return layout.WriteModelDump(cfg.Stdout, in)
	}
	s, diagnostics, err := layout.Layout(in)
	if err != nil {
		return err
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
			return nil, fmt.Errorf("cannot read %s: %w", path, err)
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
	return io.ReadAll(input)
}

func modelArgs(args []string) (string, scene.Profile, error) {
	path := "-"
	profile := scene.ProfileVector
	positional := false
	flags := true
	for i := 0; i < len(args); i++ {
		a := args[i]
		if flags && a == "--" {
			flags = false
			continue
		}
		if flags && modelValueFlag(a) {
			n, err := consumeModelFlag(args[i:], &profile)
			if err != nil {
				return "", profile, err
			}
			i += n
			continue
		}
		if flags && isModelFlag(a) {
			return "", profile, fmt.Errorf("unknown flag %s; run emd layout --help", a)
		}
		if positional {
			return "", profile, errors.New("layout accepts one INPUT")
		}
		path = a
		positional = true
	}
	return path, profile, nil
}

func modelValueFlag(a string) bool {
	return a == "--stage" || a == "--profile"
}

func isModelFlag(a string) bool {
	return len(a) > 1 && a[0] == '-'
}

func consumeModelFlag(args []string, profile *scene.Profile) (int, error) {
	if len(args) < 2 {
		return 0, fmt.Errorf("missing value for %s", args[0])
	}
	return 1, modelFlag(args[0], args[1], profile)
}

func modelFlag(flag, value string, profile *scene.Profile) error {
	if flag == "--stage" {
		if value != "model" && value != "layout" {
			return fmt.Errorf("invalid value %s for --stage; expected one of: model, layout", value)
		}
		return nil
	}
	switch value {
	case "vector":
		*profile = scene.ProfileVector
	case "cell":
		*profile = scene.ProfileCell
	default:
		return fmt.Errorf("invalid value %s for --profile; expected one of: vector, cell", value)
	}
	return nil
}

func modelStage(args []string) bool {
	for i := 0; i+1 < len(args); i++ {
		if args[i] == "--" {
			break
		}
		if args[i] == "--stage" && args[i+1] == "model" {
			return true
		}
	}
	return false
}

func metricArgs(args []string) (bool, string, []string, error) {
	out := make([]string, 0, len(args))
	metrics := false
	dump := ""
	for i := 0; i < len(args); i++ {
		if args[i] == "--" {
			out = append(out, args[i:]...)
			break
		}
		switch args[i] {
		case "--metrics":
			metrics = true
		case "--dump":
			if i+1 == len(args) {
				return false, "", nil, errors.New("missing value for --dump")
			}
			i++
			dump = args[i]
		default:
			out = append(out, args[i])
		}
	}
	if dump != "" && !metrics {
		return false, "", nil, errors.New("--dump requires --metrics")
	}
	return metrics, dump, out, nil
}
func writeDumpMetrics(cfg Config, path string) error {
	data, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	d, err := scene.ReadMetricDump(data)
	if err != nil {
		return err
	}
	m, err := scene.MeasureMetrics(&d, 0)
	if err != nil {
		return err
	}
	_, err = cfg.Stdout.Write(m.AppendJSON(nil))
	return err
}
func writeSourceMetrics(cfg Config, path string, src []byte, in layout.Input, model *layout.Diagram) error {
	s, ds, err := layout.Layout(in)
	if err != nil {
		return err
	}
	if err = diag.RenderText(cfg.Stderr, path, src, ds, diag.FrameOptions{}); err != nil {
		return err
	}
	cell, err := model.Input(scene.ProfileCell, scene.Options{})
	if err != nil {
		return err
	}
	cs, _, err := layout.Layout(cell)
	if err != nil {
		return err
	}
	rendered, err := cells.Render(cs, cells.Options{})
	if err != nil {
		return err
	}
	m, err := scene.MeasureMetrics(&s.Dump, rendered.RefusedClusters)
	if err != nil {
		return err
	}
	m.HardOK = m.HardOK && rendered.RouteConflicts == 0
	_, err = cfg.Stdout.Write(m.AppendJSON(nil))
	return err
}
