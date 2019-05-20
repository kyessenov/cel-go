package main

import (
	"fmt"
	"os"

	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wast"

	"github.com/google/cel-go/cel"
	"github.com/google/cel-go/checker"
	"github.com/google/cel-go/checker/decls"
	gen "github.com/google/cel-go/wasm"
)

const (
	test = `true ? true && false : false`
)

func main() {
	input := test
	if len(os.Args) > 1 {
		input = os.Args[1]
	}

	env, _ := cel.NewEnv(cel.Declarations(
		decls.NewIdent("ai", decls.Int, nil),
		decls.NewIdent("ar", decls.NewMapType(decls.String, decls.String), nil),
		decls.NewIdent("headers.ip", decls.String, nil),
		decls.NewIdent("headers.path", decls.String, nil),
		decls.NewIdent("headers.token", decls.String, nil),
	))

	parsed, iss := env.Parse(input)
	if iss != nil {
		panic(iss.Err())
	}
	checked, iss := env.Check(parsed)
	if iss != nil {
		panic(iss.Err())
	}
	expr, _ := cel.AstToCheckedExpr(checked)
	fmt.Printf("checked %s\n", checker.Print(expr.Expr, expr))
	prg, _ := env.Program(checked)

	activation := map[string]interface{}{
		"ai":           int64(42),
		"ar":           map[string]string{"x": "y", "z": "t"},
		"headers.path": "/token",
	}

	out, _, _ := prg.Eval(activation)
	fmt.Printf("CEL value: %v\n", out)

	instrs, strings := gen.Plan(expr)
	module, host := gen.MakeModule(instrs, strings)
	wast.WriteTo(os.Stdout, module)
	host.Values = activation
	vm, err := exec.NewVM(module)
	if err != nil {
		panic(err)
	}
	o, err := vm.ExecCode(0)
	if err != nil {
		panic(err)
	}
	fmt.Printf("WASM value: %v\n", o)
}
