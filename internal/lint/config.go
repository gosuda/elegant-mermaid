package lint

import (
	"encoding/json"
	"errors"
	"io/fs"
	"maps"
	"path/filepath"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
)

const configName = "emd.json"

type Config struct {
	Select   []string
	Ignore   []string
	Severity map[string]diag.Severity
	Off      []string
}

type Rule struct {
	Row      Row
	Severity diag.Severity
}

type InvalidConfigError struct {
	Path    string
	Message string
}

func (e *InvalidConfigError) Error() string {
	return "invalid emd.json " + e.Path + ": " + e.Message
}

type UnknownCodeError struct {
	Code string
}

func (e *UnknownCodeError) Error() string {
	return "unknown diagnostic code: " + e.Code + "; use a code printed by emd check or emd lint"
}

type ReadFile func(path string) ([]byte, error)

type configProblem string

func (p configProblem) Error() string { return string(p) }

const (
	problemInvalidJSON = configProblem("not valid JSON")
	problemTopLevel    = configProblem("top level must be a JSON object")
	problemLint        = configProblem("lint must be a JSON object")
	problemMermaid     = configProblem("mermaid must be a JSON object")
	problemSeverityMap = configProblem("lint.severity must be a JSON object")
)

func ParseConfig(path string, data []byte) (Config, error) {
	cfg, err := decodeConfig(data)
	if err != nil {
		return Config{}, &InvalidConfigError{Path: path, Message: err.Error()}
	}
	if err = cfg.Validate(); err != nil {
		return Config{}, err
	}
	return cfg, nil
}

func decodeConfig(data []byte) (Config, error) {
	if !json.Valid(data) {
		return Config{}, problemInvalidJSON
	}
	var root map[string]json.RawMessage
	if json.Unmarshal(data, &root) != nil || root == nil {
		return Config{}, problemTopLevel
	}
	if err := checkKeys(root, "", "lint", "mermaid"); err != nil {
		return Config{}, err
	}
	if raw, ok := root["mermaid"]; ok && !isObject(raw) {
		return Config{}, problemMermaid
	}
	raw, ok := root["lint"]
	if !ok {
		return Config{}, nil
	}
	return decodeLint(raw)
}

func isObject(raw json.RawMessage) bool {
	var fields map[string]json.RawMessage
	return json.Unmarshal(raw, &fields) == nil && fields != nil
}

func checkKeys(fields map[string]json.RawMessage, prefix string, allowed ...string) error {
	for _, key := range slices.Sorted(maps.Keys(fields)) {
		if !slices.Contains(allowed, key) {
			return configProblem(`unknown key "` + prefix + key + `"`)
		}
	}
	return nil
}

func decodeLint(raw json.RawMessage) (Config, error) {
	var fields map[string]json.RawMessage
	if json.Unmarshal(raw, &fields) != nil || fields == nil {
		return Config{}, problemLint
	}
	if err := checkKeys(fields, "lint.", "select", "ignore", "severity"); err != nil {
		return Config{}, err
	}
	var cfg Config
	var err error
	if cfg.Select, err = stringList(fields, "select"); err != nil {
		return Config{}, err
	}
	if cfg.Ignore, err = stringList(fields, "ignore"); err != nil {
		return Config{}, err
	}
	cfg.Severity, cfg.Off, err = severityMap(fields["severity"])
	return cfg, err
}

func stringList(fields map[string]json.RawMessage, key string) ([]string, error) {
	raw, ok := fields[key]
	if !ok {
		return nil, nil
	}
	var list []string
	if json.Unmarshal(raw, &list) != nil {
		return nil, configProblem("lint." + key + " must be an array of strings")
	}
	return list, nil
}

func severityMap(raw json.RawMessage) (map[string]diag.Severity, []string, error) {
	if raw == nil {
		return nil, nil, nil
	}
	var entries map[string]string
	if json.Unmarshal(raw, &entries) != nil || entries == nil {
		return nil, nil, problemSeverityMap
	}
	severities := make(map[string]diag.Severity, len(entries))
	var off []string
	for _, code := range slices.Sorted(maps.Keys(entries)) {
		name := entries[code]
		if name == severityOff {
			off = append(off, code)
			continue
		}
		s, ok := severityName(name)
		if !ok {
			return nil, nil, configProblem(`lint.severity "` + code + `" must be error, warning, info, or off`)
		}
		severities[code] = s
	}
	return severities, off, nil
}

func severityName(name string) (diag.Severity, bool) {
	switch name {
	case "error":
		return diag.SeverityError, true
	case "warning":
		return diag.SeverityWarning, true
	case "info":
		return diag.SeverityInfo, true
	}
	return diag.SeverityError, false
}

func (c Config) Validate() error {
	for _, list := range [][]string{c.Select, c.Ignore, c.Off, slices.Sorted(maps.Keys(c.Severity))} {
		if err := ValidateCodes(list); err != nil {
			return err
		}
	}
	return nil
}

func ValidateCodes(list []string) error {
	for _, code := range list {
		if _, ok := lookup(code); !ok {
			return &UnknownCodeError{Code: code}
		}
	}
	return nil
}

func FindConfig(dir string, read ReadFile) (path string, data []byte, found bool, err error) {
	at, err := filepath.Abs(dir)
	if err != nil {
		return "", nil, false, err
	}
	for {
		path = filepath.Join(at, configName)
		data, err = read(path)
		if err == nil {
			return path, data, true, nil
		}
		if !errors.Is(err, fs.ErrNotExist) {
			return "", nil, false, err
		}
		parent := filepath.Dir(at)
		if parent == at {
			return "", nil, false, nil
		}
		at = parent
	}
}

func LoadConfig(dir string, read ReadFile) (Config, error) {
	path, data, found, err := FindConfig(dir, read)
	if err != nil || !found {
		return Config{}, err
	}
	return ParseConfig(path, data)
}

func LoadConfigFile(path string, read ReadFile) (Config, error) {
	data, err := read(path)
	if err != nil {
		return Config{}, err
	}
	return ParseConfig(path, data)
}

type ConfigSource struct {
	Dir  string
	File string
	Skip bool
}

func ResolveConfig(s ConfigSource, read ReadFile) (Config, error) {
	switch {
	case s.File != "":
		return LoadConfigFile(s.File, read)
	case s.Skip:
		return Config{}, nil
	}
	return LoadConfig(s.Dir, read)
}

func (c Config) WithFlags(selectCodes, ignoreCodes []string) Config {
	if len(selectCodes) > 0 {
		c.Select = slices.Clone(selectCodes)
	}
	if len(ignoreCodes) > 0 {
		c.Ignore = slices.Clone(ignoreCodes)
	}
	return c
}

type selector struct {
	selects  map[string]bool
	ignore   map[string]bool
	off      map[string]bool
	severity map[string]diag.Severity
	limited  bool
}

func newSelector(c Config) *selector {
	s := &selector{
		selects:  codeSet(c.Select),
		ignore:   codeSet(c.Ignore),
		off:      codeSet(c.Off),
		severity: make(map[string]diag.Severity, len(c.Severity)),
		limited:  len(c.Select) > 0,
	}
	for code, v := range c.Severity {
		s.severity[canonical(code)] = v
	}
	return s
}

func codeSet(list []string) map[string]bool {
	set := make(map[string]bool, len(list))
	for _, code := range list {
		set[canonical(code)] = true
	}
	return set
}

func (c Config) Rules() []Rule {
	s := newSelector(c)
	rules := make([]Rule, 0, len(gen.LintRules))
	for _, row := range gen.LintRules {
		if syntaxRow(row) {
			continue
		}
		if rule, ok := s.rule(row); ok {
			rules = append(rules, rule)
		}
	}
	return rules
}

func (s *selector) rule(row Row) (Rule, bool) {
	if s.ignore[row.Code] || s.off[row.Code] {
		return Rule{}, false
	}
	configured, ok := s.severity[row.Code]
	if !ok && !s.base(row) {
		return Rule{}, false
	}
	switch {
	case ok:
		return Rule{Row: row, Severity: configured}, true
	case row.Severity == severityOff:
		return Rule{Row: row, Severity: diag.SeverityWarning}, true
	}
	return Rule{Row: row, Severity: severityOf(row.Severity)}, true
}

func (s *selector) base(row Row) bool {
	if s.limited {
		return s.selects[row.Code]
	}
	return row.Severity != severityOff
}
