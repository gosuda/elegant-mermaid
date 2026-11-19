package info

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/info"
)

const Version = "0.1.0"

type Model struct {
	Version string
}

func Resolve(_ *syn.Info) (*Model, []diag.Diagnostic) {
	return &Model{Version: Version}, nil
}
