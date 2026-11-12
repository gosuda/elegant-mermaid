package main

import (
	"context"
	"errors"
	"os"

	"github.com/gosuda/elegant-mermaid/internal/cli"
)

func main() {
	err := cli.Run(context.Background(), cli.Config{Args: os.Args[1:], Stdout: os.Stdout, Stderr: os.Stderr})
	if err == nil {
		return
	}
	if exit, ok := errors.AsType[*cli.ExitError](err); ok {
		os.Exit(exit.Code)
	}
	os.Exit(2)
}
