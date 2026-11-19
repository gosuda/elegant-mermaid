package cli

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/lint"
)

const (
	commonKind          = "common"
	suppressionTemplate = "%% emd-disable-next-line CODE: reason"
)

func explainCommand(cfg Config) error {
	set := flag.NewFlagSet("explain", flag.ContinueOnError)
	set.SetOutput(io.Discard)
	format := set.String("output-format", "text", "")
	args, err := parseFlagSet(set, "explain", cfg.Args[1:])
	if err != nil {
		return err
	}
	if err = validateChoice(*format, "--output-format", "text", "json"); err != nil {
		return err
	}
	switch {
	case len(args) == 0:
		return errors.New("missing CODE; run emd explain --help")
	case len(args) > 1:
		return fmt.Errorf("unexpected argument %s; run emd explain --help", args[1])
	}
	row, ok := lint.Describe(args[0])
	if !ok {
		return &lint.UnknownCodeError{Code: args[0]}
	}
	return writeExplanation(cfg.Stdout, *format, explanationFields(row))
}

type explanationField struct{ key, value string }

func explanationFields(row lint.Described) []explanationField {
	return []explanationField{
		{"code", row.Code},
		{"kind", codeKind(row.Code)},
		{"severity", row.Severity},
		{"fix_safety", row.FixSafety},
		{"summary", row.Summary},
		{"help", row.Help},
		{"rationale", row.Rationale},
		{"suppression", strings.Replace(suppressionTemplate, "CODE", row.Code, 1)},
	}
}

func codeKind(code string) string {
	prefix, _, _ := strings.Cut(code, "/")
	if slices.ContainsFunc(gen.Kinds, func(k gen.Kind) bool { return k.ID == prefix }) {
		return prefix
	}
	return commonKind
}

func writeExplanation(w io.Writer, format string, fields []explanationField) error {
	var out []byte
	if format == "json" {
		out = appendExplanationJSON(out, fields)
	} else {
		out = appendExplanationText(out, fields)
	}
	_, err := w.Write(out)
	return err
}

func appendExplanationText(dst []byte, fields []explanationField) []byte {
	for _, f := range fields {
		dst = append(dst, f.key+": "+f.value+"\n"...)
	}
	return dst
}

func appendExplanationJSON(dst []byte, fields []explanationField) []byte {
	dst = append(dst, '{')
	for i, f := range fields {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = diag.AppendString(dst, f.key)
		dst = append(dst, ':')
		dst = diag.AppendString(dst, f.value)
	}
	return append(dst, "}\n"...)
}
