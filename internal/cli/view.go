package cli

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
	themes "github.com/gosuda/elegant-mermaid/internal/theme"
	"github.com/gosuda/elegant-mermaid/internal/tui"
)

type viewOptions struct{ path, theme, graphics, color, script string }

func viewCommand(ctx context.Context, cfg Config) error {
	options, err := parseView(cfg.Args[1:])
	if err != nil {
		return err
	}
	if options.theme == "" {
		options.theme = viewTheme(cfg.Terminal.ColorFGBG)
	}
	if err = validateView(options); err != nil {
		return err
	}
	src, err := tui.Read(options.path)
	if err != nil {
		return err
	}
	state := tui.New(options.path, options.theme)
	state.Color = int(renderColour(options.color, cfg))
	if options.script != "" {
		return tui.Replay(ctx, state, src, options.script, cfg.Stdout)
	}
	if options.graphics != "auto" {
		state.Mode, err = termgfx.ParseMode(options.graphics)
		if err != nil {
			return err
		}
	}
	input, err := viewTerminalInput(cfg)
	if err != nil {
		return err
	}
	ctx, stop := signal.NotifyContext(ctx, os.Interrupt, syscall.SIGTERM)
	defer stop()
	return tui.Live(ctx, state, src, tui.LiveConfig{
		Input: input, Output: cfg.Stdout, Automatic: options.graphics == "auto",
		ProbeEnv: termgfx.Env{KittyWindowID: cfg.Terminal.KittyWindowID, Term: cfg.Terminal.Term, TermProgram: cfg.Terminal.TermProgram},
	})
}

func parseView(args []string) (viewOptions, error) {
	fs := flag.NewFlagSet("view", flag.ContinueOnError)
	fs.SetOutput(io.Discard)
	options := viewOptions{}
	fs.StringVar(&options.theme, "t", "", "theme")
	fs.StringVar(&options.graphics, "graphics", "auto", "graphics")
	fs.StringVar(&options.color, "color", "auto", "color")
	fs.StringVar(&options.script, "script", "", "script")
	paths, err := viewPositionals(fs, args)
	if err != nil {
		return options, err
	}
	if len(paths) != 1 || paths[0] == "-" {
		return options, fmt.Errorf("view requires a readable file path; stdin is not supported")
	}
	options.path = paths[0]
	return options, nil
}

func viewPositionals(fs *flag.FlagSet, args []string) ([]string, error) {
	var paths []string
	for len(args) > 0 {
		arg := args[0]
		args = args[1:]
		if arg == "--" {
			return append(paths, args...), nil
		}
		if !strings.HasPrefix(arg, "-") || arg == "-" {
			paths = append(paths, arg)
			continue
		}
		name := strings.TrimLeft(strings.SplitN(arg, "=", 2)[0], "-")
		if fs.Lookup(name) == nil {
			return nil, fmt.Errorf("unknown flag %s; run emd view --help", arg)
		}
		part, rest, err := flagPart(arg, args)
		if err != nil {
			return nil, err
		}
		args = rest
		if err = fs.Parse(part); err != nil {
			return nil, err
		}
	}
	return paths, nil
}

func viewTheme(background string) string {
	if darkBackground(background) {
		return "elegant-dark"
	}
	return "elegant-light"
}

func validateView(options viewOptions) error {
	if err := validateChoice(options.graphics, "--graphics", "auto", "kitty", "iterm", "sixel", "cells"); err != nil {
		return err
	}
	if err := validateChoice(options.color, "--color", "auto", "always", "never"); err != nil {
		return err
	}
	_, err := themes.Resolve(options.theme)
	return err
}

func viewTerminalInput(cfg Config) (*os.File, error) {
	input, ok := cfg.Stdin.(*os.File)
	if !ok {
		return nil, fmt.Errorf("view requires a pollable input stream; use --script for replay")
	}
	return input, nil
}
