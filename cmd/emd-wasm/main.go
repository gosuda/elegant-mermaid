//go:build js && wasm

package main

import (
	"syscall/js"

	"github.com/gosuda/elegant-mermaid/internal/cli"
)

func main() {
	js.Global().Set("emdCall", js.FuncOf(emdCall))
	select {}
}

func emdCall(_ js.Value, args []js.Value) any {
	return cli.WasmCall(stringArg(args, 0), stringArg(args, 1), stringArg(args, 2))
}

func stringArg(args []js.Value, i int) string {
	if i >= len(args) || args[i].Type() != js.TypeString {
		return ""
	}
	return args[i].String()
}
