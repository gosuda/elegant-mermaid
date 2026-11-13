package main

import (
	"context"
	"errors"
	"os"

	"github.com/gosuda/elegant-mermaid/internal/cli"
)

func main() {
	err := cli.Run(context.Background(), cli.Config{
		Args: os.Args[1:], Stdin: os.Stdin, Stdout: os.Stdout, Stderr: os.Stderr,
		Terminal: cli.TerminalEnv{
			KittyWindowID: os.Getenv("KITTY_WINDOW_ID"),
			Term:          os.Getenv("TERM"),
			TermProgram:   os.Getenv("TERM_PROGRAM"),
			ColorFGBG:     os.Getenv("COLORFGBG"),
		},
	})
	if err == nil {
		return
	}
	if exit, ok := errors.AsType[*cli.ExitError](err); ok {
		os.Exit(exit.Code)
	}
	os.Exit(2)
}
