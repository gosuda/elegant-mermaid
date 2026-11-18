package cli

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/fileerr"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const kernelEvalUsage = "Usage: emd kernel-eval FILE\n"

type kernelEvalInvocation struct {
	path string
	file bool
	help bool
}

func kernelEval(cfg Config) error {
	invocation, err := kernelEvalArgs(cfg.Args[1:])
	if err != nil {
		return err
	}
	if invocation.help {
		_, err = io.WriteString(cfg.Stdout, kernelEvalUsage)
		return err
	}
	cases, err := kernelEvalCases(cfg, invocation)
	if err != nil {
		return err
	}
	return geom.Eval(bytes.NewReader(cases), cfg.Stdout)
}

func kernelEvalArgs(args []string) (kernelEvalInvocation, error) {
	var invocation kernelEvalInvocation
	flags := true
	for _, arg := range args {
		switch {
		case !flags || arg == "-" || !strings.HasPrefix(arg, "-"):
			if invocation.file {
				return invocation, errors.New("kernel-eval accepts one INPUT")
			}
			invocation.path, invocation.file = arg, true
		case arg == "--":
			flags = false
		case arg == "-h" || arg == "--help":
			return kernelEvalInvocation{help: true}, nil
		default:
			return invocation, fmt.Errorf("unknown flag %s; run emd kernel-eval --help", arg)
		}
	}
	return invocation, nil
}

func kernelEvalCases(cfg Config, invocation kernelEvalInvocation) ([]byte, error) {
	if !invocation.file || invocation.path == "-" {
		input := cfg.Stdin
		if input == nil {
			input = strings.NewReader("")
		}
		cases, err := io.ReadAll(input)
		if err != nil {
			return nil, fileerr.Read(stdinPath, err)
		}
		return cases, nil
	}
	cases, err := os.ReadFile(invocation.path)
	if err != nil {
		return nil, fileerr.Read(invocation.path, err)
	}
	return cases, nil
}
