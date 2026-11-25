package cli

import (
	"context"
	"errors"
	"fmt"
	"io"
	"strings"

	mermaid "github.com/gosuda/elegant-mermaid"
	themes "github.com/gosuda/elegant-mermaid/internal/theme"
)

const usage = "Usage: emd COMMAND [OPTIONS]\n  render   Render Mermaid as SVG, PNG, or terminal text\n  check    Check syntax and semantics without changing files\n  lint     Check lint rules and optionally apply fixes\n  view     Watch and display a diagram in the terminal\n  layout   Print canonical layout data\n  explain  Explain a diagnostic code\n"

type Config struct {
	Args     []string
	Stdout   io.Writer
	Stderr   io.Writer
	Stdin    io.Reader
	Terminal TerminalEnv
}

type TerminalEnv struct {
	KittyWindowID string
	Term          string
	TermProgram   string
	ColorFGBG     string
	ColorTerm     string
	NoColor       string
	ForceColor    string
	CLIColor      string
	CLIColorForce string
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
	if len(cfg.Args) == 2 && (cfg.Args[1] == "--help" || cfg.Args[1] == "-h") && cfg.Args[0] != "kernel-eval" {
		return commandHelp(cfg)
	}
	return dispatch(ctx, cfg)
}

func dispatch(ctx context.Context, cfg Config) error {
	switch cfg.Args[0] {
	case "view":
		return viewCommand(ctx, cfg)
	case "render":
		return renderCommand(cfg)
	case "check":
		return checkCommand(cfg)
	case "lint":
		return lintCommand(cfg)
	case "explain":
		return explainCommand(cfg)
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
		text = "Render Mermaid as SVG, PNG, or terminal text\nUsage: emd render [INPUT] [-i INPUT] [-o OUTPUT] [-e svg|png|text] [-t THEME] [-b BACKGROUND] [-s SCALE] [--charset unicode|ascii] [--color auto|always|never] [--width COLS] [--svg-text font|paths] [--icon-pack FILE]... [-c CONFIG] [-a ARTEFACT_DIR]\nDefaults: input stdin; output stdout; format inferred from -o (.svg, .png, .txt), else text on a terminal and svg otherwise; theme elegant-light (elegant-dark on a dark terminal for text); background theme bg; scale 2 (1 to 8, PNG pixels per px); charset unicode; color auto; width 0; svg-text font (paths draws glyph outlines, so the viewer needs no font); icon packs none; config none; artefact directory none. Themes: " + strings.Join(themes.Names(), ", ") + ". PNG needs -o FILE.png or a redirected stdout. -c reads upstream config text (a block mapping); --icon-pack reads an Iconify JSON file and may repeat. Markdown input needs -o or -a; -o HOST.md rewrites the host with image links, using SVG unless -e png is given. -a selects the image directory.\nExample: emd render demo.mmd -e text\n"
	case "check":
		text = "Check syntax and semantics without changing files\nUsage: emd check [PATH...] [--output-format text|json|sarif|github] [--color auto|always|never]\nDefaults: paths . (.mmd, .mermaid, .md, .markdown, and .mdx files, skipping hidden directories, node_modules, and target; - reads stdin); output-format text; color auto. Markdown hosts report diagnostics at host positions.\nExample: emd check docs/\n"
	case "view":
		text = "Watch and display a diagram in the terminal\nUsage: emd view INPUT [-t THEME] [--graphics auto|kitty|iterm|sixel|cells] [--color auto|always|never]\nDefaults: theme elegant-light (elegant-dark on a dark terminal); graphics auto; color auto.\nExample: emd view demo.mmd\n"
	case "layout":
		text = "Print canonical layout data\nUsage: emd layout [INPUT] [--profile vector|cell] [--metrics]\nDefaults: input stdin; profile vector; metrics off. --metrics prints vector layout quality metrics.\nExample: emd layout demo.mmd --profile cell\n"
	case "lint":
		text = "Check lint rules and optionally apply fixes\nUsage: emd lint [PATH...] [--fix] [--unsafe-fixes] [--select CODES] [--ignore CODES] [--deny-warnings] [--output-format text|json|sarif|github] [--lint-config FILE] [--no-config] [--color auto|always|never]\nDefaults: paths . (.mmd, .mermaid, .md, .markdown, and .mdx files, skipping hidden directories, node_modules, and target; - reads stdin); fixes off (--fix applies safe fixes and rewrites the files; --unsafe-fixes also applies unsafe fixes and needs --fix; lint --fix - writes the fixed source to stdout and text diagnostics to stderr); select the default rule set; ignore none; deny-warnings off (a warning exits 0); output-format text; lint-config found by walking up from each input's directory to the first emd.json; no-config off; color auto. CODES is a comma-separated list of codes printed by emd check or emd lint. Exit 1 on an error diagnostic, or on a warning under --deny-warnings.\nExample: emd lint --fix demo.mmd\n"
	case "explain":
		text = "Explain a diagnostic code\nUsage: emd explain CODE [--output-format text|json]\nDefaults: output-format text. Prints the code, kind, severity, fix_safety, summary, help, rationale, and suppression comment of the registry row; an alias prints the row of its current code.\nExample: emd explain flowchart/unexpected-token\n"
	default:
		return fmt.Errorf("unknown command %s; run emd --help", cfg.Args[0])
	}
	_, err := io.WriteString(cfg.Stdout, text)
	return err
}
