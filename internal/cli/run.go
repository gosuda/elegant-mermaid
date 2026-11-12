package cli

import (
	"context"
	"errors"
	"fmt"
	"io"

	mermaid "github.com/gosuda/elegant-mermaid"
)

const usage = "Usage: emd COMMAND [OPTIONS]\n  render   Render Mermaid as SVG, PNG, or terminal text\n  check    Check syntax and semantics without changing files\n  lint     Check lint rules and optionally apply fixes\n  view     Watch and display a diagram in the terminal\n  layout   Print canonical layout data\n  explain  Explain a diagnostic code\n"

type Config struct {
	Args   []string
	Stdout io.Writer
	Stderr io.Writer
	Stdin  io.Reader
}
type ExitError struct{ Code int }

func (e *ExitError) Error() string { return "command failed" }
func Run(ctx context.Context, cfg Config) error {
	err := run(ctx, cfg)
	if err == nil {
		return nil
	}
	if _, ok := errors.AsType[*ExitError](err); ok {
		return err
	}
	if _, e := io.WriteString(cfg.Stderr, err.Error()+"\n"); e != nil {
		return errors.Join(&ExitError{Code: 2}, e)
	}
	return &ExitError{Code: 2}
}
func run(ctx context.Context, cfg Config) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	if len(cfg.Args) == 0 {
		if _, err := io.WriteString(cfg.Stderr, usage); err != nil {
			return err
		}
		return &ExitError{Code: 2}
	}
	switch cfg.Args[0] {
	case "-h", "--help":
		_, err := io.WriteString(cfg.Stdout, usage)
		return err
	case "--version":
		_, err := io.WriteString(cfg.Stdout, "emd "+mermaid.Version+"\n")
		return err
	}
	if len(cfg.Args) == 2 && (cfg.Args[1] == "--help" || cfg.Args[1] == "-h") {
		return commandHelp(cfg)
	}
	return dispatch(cfg)
}

func dispatch(cfg Config) error {
	switch cfg.Args[0] {
	case "render":
		return renderCommand(cfg)
	case "check":
		return checkCommand(cfg)
	case "layout":
		return layoutModel(cfg)
	case "kernel-eval":
		return kernelEval(cfg)
	default:
		return fmt.Errorf("unknown command %s; run emd --help", cfg.Args[0])
	}
}
func commandHelp(cfg Config) error {
	var text string
	switch cfg.Args[0] {
	case "render":
		text = "Render Mermaid as SVG or terminal text\nUsage: emd render [INPUT] [-i INPUT] [-o OUTPUT] [-e svg|text] [-t THEME] [-b BACKGROUND] [--charset unicode|ascii] [--color auto|always|never] [--width COLS] [--svg-text font]\nDefaults: input stdin; output stdout; format inferred; theme elegant-light (elegant-dark on a dark terminal for text); background theme bg; charset unicode; color auto; width 0; svg-text font. Themes: elegant-light, elegant-dark.\nExample: emd render demo.mmd -e text\n"
	case "check":
		text = "Check syntax and semantics without changing files\nUsage: emd check [PATH...] [--output-format text|json] [--color auto|always|never]\nDefaults: paths .; output-format text; color auto.\nExample: emd check docs/\n"
	case "layout":
		text = "Print canonical layout data\nUsage: emd layout [INPUT] [--profile vector|cell] [--metrics]\nDefaults: input stdin; profile vector; metrics off. --metrics prints vector layout quality metrics.\nExample: emd layout demo.mmd --profile cell\n"
	default:
		return fmt.Errorf("unknown command %s; run emd --help", cfg.Args[0])
	}
	_, err := io.WriteString(cfg.Stdout, text)
	return err
}
