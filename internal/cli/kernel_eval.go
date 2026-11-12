package cli

import (
	"errors"
	"flag"
	"io"
	"os"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func kernelEval(cfg Config) error {
	flags := flag.NewFlagSet("kernel-eval", flag.ContinueOnError)
	flags.SetOutput(io.Discard)
	if err := flags.Parse(cfg.Args[1:]); err != nil {
		return errors.New(strings.TrimSuffix(usage, "\n"))
	}
	if flags.NArg() != 1 {
		return errors.New(strings.TrimSuffix(usage, "\n"))
	}
	f, err := os.Open(flags.Arg(0))
	if err != nil {
		return err
	}
	defer func() { _ = f.Close() }()
	return geom.Eval(f, cfg.Stdout)
}
