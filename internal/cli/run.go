package cli

import (
	"context"
	"errors"
	"io"
)

const usage = "Usage: emd kernel-eval FILE\n"

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
	if _, writeErr := io.WriteString(cfg.Stderr, err.Error()+"\n"); writeErr != nil {
		return errors.Join(&ExitError{Code: 2}, writeErr)
	}
	return &ExitError{Code: 2}
}

func run(ctx context.Context, cfg Config) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	if len(cfg.Args) > 0 && cfg.Args[0] == "layout" {
		return layoutModel(cfg)
	}
	if len(cfg.Args) == 0 || cfg.Args[0] != "kernel-eval" {
		return errors.New(usage[:len(usage)-1])
	}
	return kernelEval(cfg)
}
