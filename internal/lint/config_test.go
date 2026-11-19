package lint

import (
	"errors"
	"io/fs"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
)

func memoryFS(files map[string]string) ReadFile {
	return func(path string) ([]byte, error) {
		if data, ok := files[path]; ok {
			return []byte(data), nil
		}
		return nil, &fs.PathError{Op: "open", Path: path, Err: fs.ErrNotExist}
	}
}

func TestEmdJSONWalksUp(t *testing.T) {
	read := memoryFS(map[string]string{
		"/work/emd.json":     `{"lint":{"ignore":["flowchart/no-self-loop"]}}`,
		"/work/pkg/emd.json": `{"lint":{"select":["flowchart/duplicate-ids"]}}`,
	})
	path, data, found, err := FindConfig("/work/pkg/deep/er", read)
	require.NoError(t, err)
	require.True(t, found)
	require.Equal(t, "/work/pkg/emd.json", path)
	require.JSONEq(t, `{"lint":{"select":["flowchart/duplicate-ids"]}}`, string(data))

	path, _, found, err = FindConfig("/work/other/deep", read)
	require.NoError(t, err)
	require.True(t, found)
	require.Equal(t, "/work/emd.json", path)

	_, _, found, err = FindConfig("/elsewhere/deep", read)
	require.NoError(t, err)
	require.False(t, found)

	cfg, err := LoadConfig("/work/pkg/deep", read)
	require.NoError(t, err)
	require.Equal(t, []string{"flowchart/duplicate-ids"}, cfg.Select)
	require.Empty(t, cfg.Ignore)

	cfg, err = LoadConfig("/elsewhere", read)
	require.NoError(t, err)
	require.Equal(t, Config{}, cfg)
}

func TestEmdJSONReadErrors(t *testing.T) {
	boom := errors.New("permission denied")
	read := func(path string) ([]byte, error) { return nil, boom }
	_, _, _, err := FindConfig("/work", read)
	require.ErrorIs(t, err, boom)
	_, err = LoadConfigFile("/work/custom.json", read)
	require.ErrorIs(t, err, boom)
	_, err = LoadConfigFile("/work/missing.json", memoryFS(nil))
	require.ErrorIs(t, err, fs.ErrNotExist)
}

func TestEmdJSONExplicitFile(t *testing.T) {
	read := memoryFS(map[string]string{
		"/work/emd.json":    `{"lint":{"ignore":["flowchart/no-self-loop"]}}`,
		"/work/custom.json": `{"lint":{"severity":{"flowchart/duplicate-ids":"info","common/no-experimental":"off"}}}`,
	})
	cfg, err := LoadConfigFile("/work/custom.json", read)
	require.NoError(t, err)
	require.Equal(t, map[string]diag.Severity{"flowchart/duplicate-ids": diag.SeverityInfo}, cfg.Severity)
	require.Equal(t, []string{"common/no-experimental"}, cfg.Off)
	require.Empty(t, cfg.Ignore)
}

func TestEmdJSONResolveConfig(t *testing.T) {
	read := memoryFS(map[string]string{
		"/work/emd.json":    `{"lint":{"ignore":["flowchart/no-self-loop"]}}`,
		"/work/custom.json": `{"lint":{"select":["flowchart/duplicate-ids"]}}`,
	})
	searched, err := ResolveConfig(ConfigSource{Dir: "/work/pkg"}, read)
	require.NoError(t, err)
	require.Equal(t, []string{"flowchart/no-self-loop"}, searched.Ignore)

	skipped, err := ResolveConfig(ConfigSource{Dir: "/work/pkg", Skip: true}, read)
	require.NoError(t, err)
	require.Equal(t, Config{}, skipped)

	named, err := ResolveConfig(ConfigSource{Dir: "/work/pkg", File: "/work/custom.json"}, read)
	require.NoError(t, err)
	require.Equal(t, []string{"flowchart/duplicate-ids"}, named.Select)
	require.Empty(t, named.Ignore)

	namedAndSkipped, err := ResolveConfig(ConfigSource{File: "/work/custom.json", Skip: true}, read)
	require.NoError(t, err)
	require.Equal(t, named, namedAndSkipped)

	_, err = ResolveConfig(ConfigSource{File: "/work/absent.json"}, read)
	require.ErrorIs(t, err, fs.ErrNotExist)
}

func TestEmdJSONInvalidFile(t *testing.T) {
	cases := []struct {
		name string
		data string
		want string
	}{
		{"empty", ``, "not valid JSON"},
		{"truncated", `{"lint":`, "not valid JSON"},
		{"trailing text", `{} x`, "not valid JSON"},
		{"array root", `[]`, "top level must be a JSON object"},
		{"string root", `"lint"`, "top level must be a JSON object"},
		{"null root", `null`, "top level must be a JSON object"},
		{"unknown top-level key", `{"lint":{},"extra":1}`, `unknown key "extra"`},
		{"first unknown key in byte order", `{"zeta":1,"alpha":2}`, `unknown key "alpha"`},
		{"lint not an object", `{"lint":[]}`, "lint must be a JSON object"},
		{"lint null", `{"lint":null}`, "lint must be a JSON object"},
		{"mermaid not an object", `{"mermaid":"dark"}`, "mermaid must be a JSON object"},
		{"unknown lint key", `{"lint":{"extend":[]}}`, `unknown key "lint.extend"`},
		{"select not a list", `{"lint":{"select":"flowchart/duplicate-ids"}}`, "lint.select must be an array of strings"},
		{"ignore with a number", `{"lint":{"ignore":["flowchart/duplicate-ids",1]}}`, "lint.ignore must be an array of strings"},
		{"severity not an object", `{"lint":{"severity":["error"]}}`, "lint.severity must be a JSON object"},
		{"severity null", `{"lint":{"severity":null}}`, "lint.severity must be a JSON object"},
		{"severity value", `{"lint":{"severity":{"flowchart/duplicate-ids":"fatal"}}}`, `lint.severity "flowchart/duplicate-ids" must be error, warning, info, or off`},
		{"severity value case", `{"lint":{"severity":{"flowchart/duplicate-ids":"Error"}}}`, `lint.severity "flowchart/duplicate-ids" must be error, warning, info, or off`},
		{"severity value type", `{"lint":{"severity":{"flowchart/duplicate-ids":1}}}`, `lint.severity must be a JSON object`},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := ParseConfig("/work/emd.json", []byte(c.data))
			var invalid *InvalidConfigError
			require.ErrorAs(t, err, &invalid)
			require.Equal(t, "invalid emd.json /work/emd.json: "+c.want, err.Error())
			require.Equal(t, "/work/emd.json", invalid.Path)
		})
	}
}

func TestEmdJSONAcceptsValidFiles(t *testing.T) {
	cases := []string{
		`{}`,
		` {"lint":{}} `,
		`{"lint":{"select":[],"ignore":[],"severity":{}}}`,
		`{"lint":{"select":null}}`,
		`{"mermaid":{"theme":"dark","themeVariables":{"fontFamily":"'Open Sans', sans-serif"}}}`,
		`{"lint":{"select":["flowchart/duplicate-ids"]},"mermaid":{}}`,
	}
	for _, data := range cases {
		_, err := ParseConfig("emd.json", []byte(data))
		require.NoError(t, err, data)
	}
}

func TestEmdJSONUnknownCode(t *testing.T) {
	message := func(code string) string {
		return "unknown diagnostic code: " + code + "; use a code printed by emd check or emd lint"
	}
	cases := []struct {
		name string
		data string
		code string
	}{
		{"select", `{"lint":{"select":["flowchart/duplicate-ids","flowchart/nope"]}}`, "flowchart/nope"},
		{"ignore", `{"lint":{"ignore":["nope"]}}`, "nope"},
		{"severity", `{"lint":{"severity":{"flowchart/nope":"error"}}}`, "flowchart/nope"},
		{"severity off", `{"lint":{"severity":{"flowchart/nope":"off"}}}`, "flowchart/nope"},
		{"select before ignore", `{"lint":{"ignore":["b/two"],"select":["a/one"]}}`, "a/one"},
		{"first severity code in byte order", `{"lint":{"severity":{"z/last":"info","a/first":"info"}}}`, "a/first"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := ParseConfig("emd.json", []byte(c.data))
			var unknown *UnknownCodeError
			require.ErrorAs(t, err, &unknown)
			require.Equal(t, c.code, unknown.Code)
			require.Equal(t, message(c.code), err.Error())
		})
	}
	require.NoError(t, ValidateCodes([]string{"flowchart/duplicate-ids", "flowchart/arrow-invalid", "meta/unknown-rule", "common/unknown-diagram-kind", "config/unknown-key"}))
	require.Equal(t, message("nope"), ValidateCodes([]string{"nope"}).Error())
	require.Equal(t, message("x"), Config{Off: []string{"x"}}.Validate().Error())
}

func TestEmdJSONFlagPrecedence(t *testing.T) {
	file := Config{
		Select:   []string{"flowchart/duplicate-ids"},
		Ignore:   []string{"flowchart/no-self-loop"},
		Severity: map[string]diag.Severity{"flowchart/duplicate-ids": diag.SeverityWarning},
		Off:      []string{"common/no-experimental"},
	}
	replaced := file.WithFlags([]string{"flowchart/no-self-loop"}, []string{"common/no-experimental"})
	require.Equal(t, []string{"flowchart/no-self-loop"}, replaced.Select)
	require.Equal(t, []string{"common/no-experimental"}, replaced.Ignore)
	require.Equal(t, file.Severity, replaced.Severity)
	require.Equal(t, file.Off, replaced.Off)

	kept := file.WithFlags(nil, nil)
	require.Equal(t, file, kept)
	onlySelect := file.WithFlags([]string{"common/no-experimental"}, nil)
	require.Equal(t, []string{"common/no-experimental"}, onlySelect.Select)
	require.Equal(t, file.Ignore, onlySelect.Ignore)
	require.Equal(t, []string{"flowchart/duplicate-ids"}, file.Select)
}

func severities(rules []Rule) map[string]diag.Severity {
	out := map[string]diag.Severity{}
	for _, r := range rules {
		out[r.Row.Code] = r.Severity
	}
	return out
}

func TestEmdJSONEffectiveRules(t *testing.T) {
	const (
		dupRule  = "flowchart/duplicate-ids"
		titleOff = "common/acc-title-missing"
		beta     = "common/no-experimental"
	)
	defaults := severities(Config{}.Rules())
	for _, row := range gen.LintRules {
		_, ok := defaults[row.Code]
		require.Equal(t, !syntaxRow(row) && row.Severity != "off", ok, row.Code)
	}
	require.Equal(t, diag.SeverityError, defaults[dupRule])
	require.Equal(t, diag.SeverityWarning, defaults["meta/unused-suppression"])

	empty := map[string]diag.Severity{}
	cases := []struct {
		name string
		cfg  Config
		want map[string]diag.Severity
	}{
		{"select replaces the default set", Config{Select: []string{dupRule}}, map[string]diag.Severity{dupRule: diag.SeverityError}},
		{"empty select is absent", Config{Select: []string{}}, defaults},
		{"select of an off rule runs it as a warning", Config{Select: []string{titleOff}}, map[string]diag.Severity{titleOff: diag.SeverityWarning}},
		{"severity adds an off rule", Config{Select: []string{dupRule}, Severity: map[string]diag.Severity{titleOff: diag.SeverityInfo}}, map[string]diag.Severity{dupRule: diag.SeverityError, titleOff: diag.SeverityInfo}},
		{"severity overrides a default", Config{Select: []string{dupRule}, Severity: map[string]diag.Severity{dupRule: diag.SeverityInfo}}, map[string]diag.Severity{dupRule: diag.SeverityInfo}},
		{"severity beats the off default of a selected rule", Config{Select: []string{titleOff}, Severity: map[string]diag.Severity{titleOff: diag.SeverityError}}, map[string]diag.Severity{titleOff: diag.SeverityError}},
		{"ignore removes a selected rule", Config{Select: []string{dupRule, beta}, Ignore: []string{beta}}, map[string]diag.Severity{dupRule: diag.SeverityError}},
		{"ignore removes a severity addition", Config{Select: []string{dupRule}, Severity: map[string]diag.Severity{beta: diag.SeverityError}, Ignore: []string{beta}}, map[string]diag.Severity{dupRule: diag.SeverityError}},
		{"off removes a selected rule", Config{Select: []string{dupRule, beta}, Off: []string{dupRule}}, map[string]diag.Severity{beta: diag.SeverityWarning}},
		{"off beats a severity entry", Config{Select: []string{dupRule}, Severity: map[string]diag.Severity{dupRule: diag.SeverityInfo}, Off: []string{dupRule}}, empty},
		{"syntax rows never join the set", Config{Select: []string{"flowchart/arrow-invalid", "flowchart/unclosed-node-bracket"}}, empty},
		{"unknown codes are ignored", Config{Select: []string{"nope/nothing"}, Ignore: []string{"nope/other"}, Severity: map[string]diag.Severity{"nope/third": diag.SeverityError}}, empty},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			require.Equal(t, c.want, severities(c.cfg.Rules()))
		})
	}
}

func TestEmdJSONRulesFollowRegistryOrder(t *testing.T) {
	rules := Config{}.Rules()
	require.Equal(t, "common/no-experimental", rules[0].Row.Code)
	positions := map[string]int{}
	for i, r := range rules {
		positions[r.Row.Code] = i
	}
	require.Less(t, positions["common/no-experimental"], positions["meta/unknown-rule"])
	require.Less(t, positions["meta/unknown-rule"], positions["flowchart/duplicate-ids"])
}
