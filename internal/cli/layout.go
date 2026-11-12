package cli

import (
	"errors"
	"fmt"
	"io"
	"os"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	model "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func layoutModel(cfg Config) error {
	path, profile, err := modelArgs(cfg.Args[1:])
	if err != nil {
		return err
	}
	src, err := modelSource(cfg, path)
	if err != nil {
		return err
	}
	if path == "-" {
		path = "<stdin>"
	}
	p := syntax.Preprocess(src)
	detection := syntax.Detect(src, p.Removed)
	ds := append(p.Diags, detection.Diagnostics...)
	if detection.Found && detection.Kind != "flowchart" {
		return fmt.Errorf("unsupported diagram kind: %s", detection.Kind)
	}
	file, parsed := parser.Parse(src, p.Removed)
	ds = append(ds, parsed...)
	m, resolved := model.Resolve(src, file)
	ds = append(ds, resolved...)
	diag.Sort(ds)
	if hasErrors(ds) {
		if err := diag.RenderText(cfg.Stderr, path, src, ds, diag.FrameOptions{}); err != nil {
			return err
		}
		return &ExitError{Code: 1}
	}
	in, _ := layout.FromFlowchart(m, profile, scene.Options{})
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
		return os.ReadFile(path)
	}
	input := cfg.Stdin
	if input == nil {
		input = os.Stdin
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
