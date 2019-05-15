package main

import (
	"fmt"

	"github.com/go-interpreter/wagon/disasm"
	"github.com/go-interpreter/wagon/exec"
	"github.com/go-interpreter/wagon/wasm"
	ops "github.com/go-interpreter/wagon/wasm/operators"

	"github.com/google/cel-go/cel"
	"github.com/google/cel-go/checker"
)

const (
	test = `1 + 1 == 2`
)

func main() {
	env, _ := cel.NewEnv()
	parsed, iss := env.Parse(test)
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
	out, _, _ := prg.Eval(map[string]interface{}{})
	fmt.Printf("CEL value: %v\n", out)

	module := &wasm.Module{}
	module.FunctionIndexSpace = []wasm.Function{{
		Sig: &wasm.FunctionSig{
			ParamTypes:  []wasm.ValueType{},
			ReturnTypes: []wasm.ValueType{wasm.ValueTypeI64},
		},
		Body: &wasm.FunctionBody{
			Module: module,
			Code:   getCode(),
		},
	}}

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

func getCode() []byte {
	out, err := disasm.Assemble([]disasm.Instr{{
		Op:         op(ops.I64Const),
		Immediates: []interface{}{int64(42)},
	}, {
		Op:         op(ops.I64Const),
		Immediates: []interface{}{int64(42)},
	}, {
		Op: op(ops.I64Add),
	}})
	if err != nil {
		panic(err)
	}
	return out
}

func op(o byte) ops.Op {
	out, _ := ops.New(o)
	return out
}
