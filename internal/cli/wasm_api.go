package cli

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/lint"
)

type wasmResponse struct {
	OK          bool            `json:"ok"`
	Output      string          `json:"output"`
	Diagnostics json.RawMessage `json:"diagnostics"`
	Applied     int             `json:"applied"`
}

type wasmOptions struct {
	theme      string
	background string
	charset    string
	profile    string
	stage      string
	max        string
	width      int
	lintConfig lint.Config
}

type wasmOptionKey struct {
	ops []string
	set func(o *wasmOptions, raw json.RawMessage) bool
}

type wasmOp func(source string, o wasmOptions) wasmResponse

var wasmOps = map[string]wasmOp{
	"check":       wasmCheck,
	"lint":        wasmLint,
	"fix":         wasmFix,
	"render_svg":  wasmRenderSVG,
	"render_text": wasmRenderText,
	"layout":      wasmLayout,
	"version":     wasmVersion,
}

var wasmOptionKeys = map[string]wasmOptionKey{
	"theme":      {[]string{"render_svg", "render_text"}, setWasmTheme},
	"background": {[]string{"render_svg"}, setWasmBackground},
	"charset":    {[]string{"render_text"}, wasmEnum(func(o *wasmOptions) *string { return &o.charset }, "unicode", "ascii")},
	"profile":    {[]string{"layout"}, wasmEnum(func(o *wasmOptions) *string { return &o.profile }, "vector", "cell")},
	"stage":      {[]string{"layout"}, wasmEnum(func(o *wasmOptions) *string { return &o.stage }, "layout", "model")},
	"max_width":  {[]string{"render_svg", "render_text"}, setWasmMaxWidth},
	"lint":       {[]string{"lint", "fix"}, setWasmLint},
	"max":        {[]string{"fix"}, wasmEnum(func(o *wasmOptions) *string { return &o.max }, "safe", "unsafe")},
}

func WasmCall(op, source, optionsJSON string) (response string) {
	defer func() {
		if r := recover(); r != nil {
			fmt.Fprintln(os.Stderr, "emd-wasm: internal error:", r)
			response = wasmEncode(wasmResponse{Diagnostics: json.RawMessage("[]")})
		}
	}()
	run, ok := wasmOps[op]
	if !ok {
		return wasmEncode(wasmInvalidOption("op"))
	}
	o, bad := parseWasmOptions(optionsJSON, op)
	if bad != "" {
		return wasmEncode(wasmInvalidOption(bad))
	}
	return wasmEncode(run(source, o))
}

func wasmInvalidOption(key string) wasmResponse {
	return wasmResponse{Output: "invalid option: " + key, Diagnostics: json.RawMessage("[]")}
}

func wasmEncode(r wasmResponse) string {
	var buf bytes.Buffer
	enc := json.NewEncoder(&buf)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(r); err != nil {
		return `{"ok":false,"output":"","diagnostics":[],"applied":0}`
	}
	return string(bytes.TrimSuffix(buf.Bytes(), []byte("\n")))
}

func wasmRun(args []string, stdin string) ([]byte, int) {
	var out bytes.Buffer
	err := Run(context.Background(), Config{
		Args:   args,
		Stdout: &out,
		Stderr: io.Discard,
		Stdin:  strings.NewReader(stdin),
	})
	return out.Bytes(), wasmExitCode(err)
}

func wasmExitCode(err error) int {
	if err == nil {
		return 0
	}
	if exit, ok := errors.AsType[*ExitError](err); ok {
		return exit.Code
	}
	return 2
}

func wasmCheckArgs() []string {
	return []string{"check", "--output-format", "json", "-"}
}

func wasmDiagnostics(checkJSON []byte) json.RawMessage {
	var doc struct {
		Files []struct {
			Diagnostics json.RawMessage `json:"diagnostics"`
		} `json:"files"`
	}
	if json.Unmarshal(checkJSON, &doc) != nil || len(doc.Files) == 0 {
		return json.RawMessage("[]")
	}
	d := doc.Files[0].Diagnostics
	if len(d) == 0 || bytes.Equal(d, []byte("null")) {
		return json.RawMessage("[]")
	}
	return d
}

func wasmVersion(string, wasmOptions) wasmResponse {
	out, _ := wasmRun([]string{"--version"}, "")
	return wasmResponse{OK: true, Output: string(out), Diagnostics: json.RawMessage("[]")}
}

func wasmCheck(source string, _ wasmOptions) wasmResponse {
	out, code := wasmRun(wasmCheckArgs(), source)
	return wasmResponse{OK: code == 0, Output: string(out), Diagnostics: wasmDiagnostics(out)}
}

func wasmLint(source string, o wasmOptions) wasmResponse {
	file := lintFile(stdinPath, []byte(source), o.lintConfig)
	out, err := lint.Render(lint.FormatJSON, []diag.FileDiagnostics{file}, lint.RenderOptions{})
	if err != nil {
		return wasmResponse{Output: err.Error(), Diagnostics: json.RawMessage("[]")}
	}
	return wasmResponse{OK: !hasSeverity([]diag.FileDiagnostics{file}, diag.SeverityError), Output: string(out), Diagnostics: wasmDiagnostics(out)}
}

func wasmFix(source string, o wasmOptions) wasmResponse {
	limit := diag.FixSafe
	if o.max == "unsafe" {
		limit = diag.FixUnsafe
	}
	fixed, applied := fixSource(stdinPath, []byte(source), o.lintConfig, limit)
	remaining := wasmLint(string(fixed), o)
	return wasmResponse{OK: true, Output: string(fixed), Diagnostics: remaining.Diagnostics, Applied: applied}
}

func wasmRenderSVG(source string, o wasmOptions) wasmResponse {
	args := []string{"render", "-e", "svg", "-t", o.theme}
	if o.background != "" {
		args = append(args, "-b", o.background)
	}
	return wasmRender(wasmWidthArgs(args, o), source)
}

func wasmRenderText(source string, o wasmOptions) wasmResponse {
	args := []string{"render", "-e", "text", "--charset", o.charset, "--color", "never", "-t", o.theme}
	return wasmRender(wasmWidthArgs(args, o), source)
}

func wasmLayout(source string, o wasmOptions) wasmResponse {
	return wasmRender([]string{"layout", "--profile", o.profile, "--stage", o.stage}, source)
}

func wasmWidthArgs(args []string, o wasmOptions) []string {
	if o.width < 0 {
		return args
	}
	return append(args, "--width", strconv.Itoa(o.width))
}

func wasmRender(args []string, source string) wasmResponse {
	out, code := wasmRun(args, source)
	r := wasmResponse{OK: code == 0}
	if r.OK {
		r.Output = string(out)
	}
	check, _ := wasmRun(wasmCheckArgs(), source)
	r.Diagnostics = wasmDiagnostics(check)
	return r
}

func parseWasmOptions(text, op string) (wasmOptions, string) {
	o := wasmOptions{theme: "elegant-light", charset: "unicode", profile: "vector", stage: "layout", max: "safe", width: -1}
	if strings.TrimSpace(text) == "" {
		return o, ""
	}
	dec := json.NewDecoder(strings.NewReader(text))
	if tok, err := dec.Token(); err != nil || tok != json.Delim('{') {
		return o, "options"
	}
	for dec.More() {
		if bad := readWasmMember(dec, op, &o); bad != "" {
			return o, bad
		}
	}
	if tok, err := dec.Token(); err != nil || tok != json.Delim('}') {
		return o, "options"
	}
	if _, err := dec.Token(); !errors.Is(err, io.EOF) {
		return o, "options"
	}
	return o, ""
}

func readWasmMember(dec *json.Decoder, op string, o *wasmOptions) string {
	tok, err := dec.Token()
	key, isString := tok.(string)
	if err != nil || !isString {
		return "options"
	}
	var raw json.RawMessage
	if dec.Decode(&raw) != nil {
		return "options"
	}
	spec, known := wasmOptionKeys[key]
	if !known {
		return key
	}
	if !slices.Contains(spec.ops, op) || spec.set(o, bytes.TrimSpace(raw)) {
		return ""
	}
	return key
}

func wasmRawString(raw json.RawMessage) (string, bool) {
	var s string
	if len(raw) == 0 || raw[0] != '"' || json.Unmarshal(raw, &s) != nil {
		return "", false
	}
	return s, true
}

func wasmEnum(field func(*wasmOptions) *string, choices ...string) func(*wasmOptions, json.RawMessage) bool {
	return func(o *wasmOptions, raw json.RawMessage) bool {
		s, ok := wasmRawString(raw)
		if !ok || !slices.Contains(choices, s) {
			return false
		}
		*field(o) = s
		return true
	}
}

func setWasmTheme(o *wasmOptions, raw json.RawMessage) bool {
	s, ok := wasmRawString(raw)
	if ok {
		o.theme = s
	}
	return ok
}

func setWasmBackground(o *wasmOptions, raw json.RawMessage) bool {
	if bytes.Equal(raw, []byte("null")) {
		o.background = ""
		return true
	}
	s, ok := wasmRawString(raw)
	if ok {
		o.background = s
	}
	return ok
}

func setWasmMaxWidth(o *wasmOptions, raw json.RawMessage) bool {
	if bytes.Equal(raw, []byte("null")) {
		o.width = -1
		return true
	}
	n, err := strconv.ParseInt(string(raw), 10, 32)
	if err != nil || n < 0 {
		return false
	}
	o.width = int(n)
	return true
}

func setWasmLint(o *wasmOptions, raw json.RawMessage) bool {
	doc := append(append([]byte(`{"lint":`), raw...), '}')
	cfg, err := lint.ParseConfig("emd.json", doc)
	if err != nil {
		return false
	}
	o.lintConfig = cfg
	return true
}
