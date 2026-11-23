package cli

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/fileerr"
	"github.com/gosuda/elegant-mermaid/internal/lint"
)

const (
	stdinInput = "-"
	stdinPath  = "<stdin>"
)

type lintOptions struct {
	fix, unsafeFixes, denyWarnings, noConfig bool
	selectCodes, ignoreCodes                 stringList
	format, color, configFile                string
	output                                   lint.Format
}

func lintFlags(args []string) (lintOptions, []string, error) {
	o := lintOptions{format: "text", color: "auto"}
	set := flag.NewFlagSet("lint", flag.ContinueOnError)
	set.SetOutput(io.Discard)
	set.BoolVar(&o.fix, "fix", false, "")
	set.BoolVar(&o.unsafeFixes, "unsafe-fixes", false, "")
	set.BoolVar(&o.denyWarnings, "deny-warnings", false, "")
	set.BoolVar(&o.noConfig, "no-config", false, "")
	set.Var(&o.selectCodes, "select", "")
	set.Var(&o.ignoreCodes, "ignore", "")
	set.StringVar(&o.format, "output-format", "text", "")
	set.StringVar(&o.configFile, "lint-config", "", "")
	set.StringVar(&o.color, "color", "auto", "")
	paths, err := parseFlagSet(set, "lint", args)
	return o, paths, err
}

func parseFlagSet(set *flag.FlagSet, command string, args []string) ([]string, error) {
	var positional []string
	for len(args) > 0 {
		a := args[0]
		args = args[1:]
		switch {
		case a == "--":
			return append(positional, args...), nil
		case !isFlagArg(a):
			positional = append(positional, a)
		default:
			rest, err := parseFlag(set, command, a, args)
			if err != nil {
				return nil, err
			}
			args = rest
		}
	}
	return positional, nil
}

func parseFlag(set *flag.FlagSet, command, a string, args []string) ([]string, error) {
	token, ok := splitFlag(a)
	name, value, hasValue := token.name, token.value, token.hasValue
	var f *flag.Flag
	if ok {
		f = set.Lookup(name)
	}
	if f == nil {
		return nil, unknownFlag(a, command)
	}
	part, rest := []string{a}, args
	if !boolFlag(f) {
		var err error
		if part, rest, err = flagPart(a, args); err != nil {
			return nil, err
		}
	}
	if set.Parse(part) != nil {
		if !hasValue {
			value = "true"
		}
		return nil, invalidValue(value, "--"+name, "true, false")
	}
	return rest, nil
}

func boolFlag(f *flag.Flag) bool {
	b, ok := f.Value.(interface{ IsBoolFlag() bool })
	return ok && b.IsBoolFlag()
}

func codeList(values stringList) []string {
	var codes []string
	for _, v := range values {
		for code := range strings.SplitSeq(v, ",") {
			if code = strings.TrimSpace(code); code != "" {
				codes = append(codes, code)
			}
		}
	}
	return codes
}

func (o *lintOptions) validate(paths []string) error {
	format, ok := lint.ParseFormat(o.format)
	if !ok {
		return invalidValue(o.format, "--output-format", "text, json, sarif, github")
	}
	o.output = format
	if err := validateChoice(o.color, "--color", "auto", "always", "never"); err != nil {
		return err
	}
	if o.unsafeFixes && !o.fix {
		return errors.New("--unsafe-fixes requires --fix")
	}
	if o.fix && o.output != lint.FormatText && slices.Contains(paths, stdinInput) {
		return errors.New("lint --fix - supports only text diagnostics; remove --output-format or pass a file path")
	}
	for _, list := range []stringList{o.selectCodes, o.ignoreCodes} {
		if err := lint.ValidateCodes(codeList(list)); err != nil {
			return err
		}
	}
	return nil
}

func (o lintOptions) fixLimit() diag.FixSafety {
	if o.unsafeFixes {
		return diag.FixUnsafe
	}
	return diag.FixSafe
}

func (o lintOptions) failingSeverity() diag.Severity {
	if o.denyWarnings {
		return diag.SeverityWarning
	}
	return diag.SeverityError
}

type configResolver struct {
	options lintOptions
	flags   lint.Config
	byDir   map[string]lint.Config
}

func newConfigResolver(o lintOptions) *configResolver {
	return &configResolver{
		options: o,
		flags:   lint.Config{Select: codeList(o.selectCodes), Ignore: codeList(o.ignoreCodes)},
		byDir:   map[string]lint.Config{},
	}
}

func readConfigFile(path string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fileerr.Read(path, err)
	}
	return data, nil
}

func (r *configResolver) forInput(input string) (lint.Config, error) {
	dir := filepath.Dir(input)
	key := dir
	if r.options.configFile != "" || r.options.noConfig {
		key = ""
	}
	cfg, found := r.byDir[key]
	if !found {
		var err error
		source := lint.ConfigSource{Dir: dir, File: r.options.configFile, Skip: r.options.noConfig}
		if cfg, err = lint.ResolveConfig(source, readConfigFile); err != nil {
			return lint.Config{}, err
		}
		r.byDir[key] = cfg
	}
	return cfg.WithFlags(r.flags.Select, r.flags.Ignore), nil
}

func lintFile(path string, src []byte, cfg lint.Config) diag.FileDiagnostics {
	if markdownHost(path) {
		report := lint.LintHost(src, cfg)
		return diag.FileDiagnostics{Path: path, Source: report.Source, Diagnostics: report.Diagnostics}
	}
	f, d := parseDiagram(path, src)
	f.Diagnostics = lint.Run(lint.AnalyzeDiagram(d), cfg).All()
	return f
}

func fixSource(path string, src []byte, cfg lint.Config, limit diag.FixSafety) ([]byte, int) {
	if markdownHost(path) {
		return lint.ApplyHostFixes(src, cfg, limit)
	}
	return lint.ApplyFixes(src, cfg, limit)
}

func lintCommand(cfg Config) error {
	o, paths, err := lintFlags(cfg.Args[1:])
	if err != nil {
		return err
	}
	if err = o.validate(paths); err != nil {
		return err
	}
	inputs, err := collectCheckPaths(paths)
	if err != nil {
		return err
	}
	if len(inputs) == 0 {
		_, err = fmt.Fprintln(cfg.Stderr, "no Mermaid files found in .")
		return err
	}
	out, err := lintAll(cfg, o, inputs)
	if err != nil {
		return err
	}
	if err = writeLintOutput(cfg, o, out); err != nil {
		return err
	}
	if hasSeverity(out.files, o.failingSeverity()) {
		return &ExitError{Code: 1}
	}
	return nil
}

type lintOutcome struct {
	files      []diag.FileDiagnostics
	stdinFixed []byte
	fixedStdin bool
}

func lintAll(cfg Config, o lintOptions, inputs []string) (lintOutcome, error) {
	var out lintOutcome
	resolver := newConfigResolver(o)
	for _, input := range inputs {
		if err := lintOne(cfg, o, resolver, input, &out); err != nil {
			return out, err
		}
	}
	return out, nil
}

func lintOne(cfg Config, o lintOptions, resolver *configResolver, input string, out *lintOutcome) error {
	src, err := modelSource(cfg, input)
	if err != nil {
		return err
	}
	lc, err := resolver.forInput(input)
	if err != nil {
		return err
	}
	path := displayPath(input)
	if o.fix {
		fixed, _ := fixSource(path, src, lc, o.fixLimit())
		if err = storeFixed(input, src, fixed, out); err != nil {
			return err
		}
		src = fixed
	}
	out.files = append(out.files, lintFile(path, src, lc))
	return nil
}

func displayPath(input string) string {
	if input == stdinInput {
		return stdinPath
	}
	return input
}

func storeFixed(input string, original, fixed []byte, out *lintOutcome) error {
	if input == stdinInput {
		out.stdinFixed, out.fixedStdin = fixed, true
		return nil
	}
	if bytes.Equal(original, fixed) {
		return nil
	}
	return rewriteFile(input, fixed)
}

func rewriteFile(path string, data []byte) error {
	info, err := os.Stat(path)
	if err != nil {
		return fileerr.Read(path, err)
	}
	if err = atomicRewrite(path, data, info.Mode().Perm()); err != nil {
		return fileerr.Write(path, err)
	}
	return nil
}

func atomicRewrite(path string, data []byte, mode fs.FileMode) (err error) {
	f, err := os.CreateTemp(filepath.Dir(path), ".emd-*")
	if err != nil {
		return err
	}
	defer func() {
		if err != nil {
			err = errors.Join(err, removeIfPresent(f.Name()))
		}
	}()
	if _, err = f.Write(data); err != nil {
		return errors.Join(err, f.Close())
	}
	if err = f.Chmod(mode); err != nil {
		return errors.Join(err, f.Close())
	}
	if err = f.Close(); err != nil {
		return err
	}
	return os.Rename(f.Name(), path)
}

func removeIfPresent(path string) error {
	if err := os.Remove(path); err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	return nil
}

func writeLintOutput(cfg Config, o lintOptions, out lintOutcome) error {
	if o.fix && out.fixedStdin {
		if _, err := cfg.Stdout.Write(out.stdinFixed); err != nil {
			return err
		}
		colour := ColourEnabled(o.color, terminalWriter(cfg.Stderr), cfg.Terminal)
		return writeLintFormat(cfg.Stderr, lint.FormatText, colour, out.files)
	}
	return writeLintFormat(cfg.Stdout, o.output, colourEnabled(o.color, cfg), out.files)
}

func writeLintFormat(w io.Writer, format lint.Format, colour bool, files []diag.FileDiagnostics) error {
	data, err := lint.Render(format, files, lint.RenderOptions{Version: mermaid.Version, Colour: colour})
	if err != nil {
		return err
	}
	_, err = w.Write(data)
	return err
}

func hasSeverity(files []diag.FileDiagnostics, threshold diag.Severity) bool {
	return slices.ContainsFunc(files, func(f diag.FileDiagnostics) bool {
		return slices.ContainsFunc(f.Diagnostics, func(d diag.Diagnostic) bool { return d.Severity <= threshold })
	})
}
